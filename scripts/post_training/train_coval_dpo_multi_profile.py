#!/usr/bin/env python3
"""Train one DPO LoRA adapter jointly on multiple CoVal profiles.

This is the multi-profile analogue of ``train_coval_dpo.py``.  It combines all
strict pairwise comparisons from a selected list of ``prompt_id:block_name``
cases, trains one shared LoRA adapter, then evaluates each case separately
against the same single-profile RTBT target used in the filtered DPO sweep.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import random
import statistics
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

os.environ.setdefault("TRANSFORMERS_NO_TF", "1")
os.environ.setdefault("TRANSFORMERS_NO_FLAX", "1")
os.environ.setdefault("USE_TF", "0")
os.environ.setdefault("USE_FLAX", "0")

import numpy as np
import torch
import torch.nn.functional as F
from peft import LoraConfig, get_peft_model
from transformers import AutoModelForCausalLM, AutoTokenizer

from scripts.theory.nlhf_tie_normalization import load_cases_tie_norm
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda
from scripts.post_training.train_coval_dpo import (
    EncodedCompletion,
    LABELS,
    build_pair_indices,
    choose_device,
    dtype_from_name,
    encode_completion,
    load_prompt_case,
    logsumexp,
    render_full,
    render_prefix,
    safe_tag,
    score_candidates,
    sequence_logprobs,
)


DEFAULT_BASELINE_JSONL = Path("results/empirical/dpo_rtbt/filtered_profile_sweeps/qwen25.jsonl")


def log(message: str) -> None:
    print(message, flush=True)


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    tmp.replace(path)


def append_jsonl(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as handle:
        handle.write(json.dumps(payload, sort_keys=True) + "\n")
        handle.flush()


@dataclass(frozen=True)
class PromptArtifacts:
    prompt_id: str
    encoded_items: list[EncodedCompletion]
    encoded_by_label: dict[str, EncodedCompletion]
    ref_logps: torch.Tensor
    ref_probs: dict[str, float]
    completion_tokens: dict[str, int]


@dataclass(frozen=True)
class JointCase:
    case_key: str
    prompt_id: str
    block_name: str
    num_rankings: int
    rankings: tuple[str, ...]
    chosen_idx: torch.Tensor
    rejected_idx: torch.Tensor
    pair_counts: dict[str, int]
    theoretical_probs: dict[str, float] | None
    baseline_tv_to_theory: float | None

    @property
    def num_pairs(self) -> int:
        return int(self.chosen_idx.shape[0])


def make_case_key(case) -> str:
    return f"{case.prompt_id}:{case.block_name}"


def parse_csv_arg(text: str) -> list[str]:
    return [part.strip() for part in text.split(",") if part.strip()]


def read_case_keys(path: Path) -> list[str]:
    keys: list[str] = []
    with path.open() as handle:
        for line in handle:
            line = line.strip()
            if line and not line.startswith("#"):
                keys.append(line)
    return keys


def collect_case_keys(args: argparse.Namespace) -> list[str]:
    keys: list[str] = []
    if args.case_keys_file is not None:
        keys.extend(read_case_keys(args.case_keys_file))
    for value in args.case_key:
        keys.extend(parse_csv_arg(value))

    deduped: list[str] = []
    seen: set[str] = set()
    for key in keys:
        if key in seen:
            continue
        deduped.append(key)
        seen.add(key)
    if not deduped:
        raise ValueError("Provide at least one --case-key or --case-keys-file")
    return deduped


def jsonable_probs(values: Iterable[float]) -> dict[str, float]:
    return {label: float(value) for label, value in zip(LABELS, values)}


def tv_distance(p: dict[str, float], q: dict[str, float]) -> float:
    return 0.5 * sum(abs(float(p[label]) - float(q[label])) for label in LABELS)


def max_abs_error(p: dict[str, float], q: dict[str, float]) -> float:
    return max(abs(float(p[label]) - float(q[label])) for label in LABELS)


def top_label(probs: dict[str, float]) -> str:
    return max(LABELS, key=lambda label: float(probs[label]))


def load_baseline_tvs(path: Path | None) -> dict[str, float]:
    if path is None or not path.exists():
        return {}
    out: dict[str, float] = {}
    with path.open() as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            value = row.get("tv_to_theory")
            if value is not None and math.isfinite(float(value)):
                out[row["case_key"]] = float(value)
    return out


def select_cases(dataset: Path, case_keys: Sequence[str]) -> list:
    wanted = set(case_keys)
    cases_by_key = {
        make_case_key(case): case
        for case in load_cases_tie_norm(dataset, ["world", "personal"])
        if make_case_key(case) in wanted
    }
    missing = [key for key in case_keys if key not in cases_by_key]
    if missing:
        raise KeyError(f"Missing case keys: {missing}")
    return [cases_by_key[key] for key in case_keys]


def build_prompt_artifacts(
    *,
    dataset: Path,
    prompt_ids: Sequence[str],
    identity_mode: str,
    renderer: str,
    tokenizer,
    model,
    pad_token_id: int,
    device: torch.device,
    max_length: int,
    progress_path: Path | None = None,
    setup_log_every: int = 1,
) -> dict[str, PromptArtifacts]:
    artifacts: dict[str, PromptArtifacts] = {}
    total_prompts = len(prompt_ids)
    start = time.perf_counter()
    for index, prompt_id in enumerate(prompt_ids, start=1):
        prompt_start = time.perf_counter()
        should_log = (
            setup_log_every <= 1
            or index == 1
            or index == total_prompts
            or index % setup_log_every == 0
        )
        if should_log:
            log(
                f"reference_scoring start {index}/{total_prompts} "
                f"prompt_id={prompt_id}"
            )
        prompt_case = load_prompt_case(dataset, prompt_id, identity_mode)
        prefix_text = render_prefix(prompt_case.prompt_messages, renderer)
        encoded_by_label: dict[str, EncodedCompletion] = {}
        completion_tokens: dict[str, int] = {}
        for label in LABELS:
            full_text = render_full(
                prompt_case.prompt_messages,
                prompt_case.responses[label],
                renderer,
            )
            encoded = encode_completion(tokenizer, label, prefix_text, full_text, max_length)
            encoded_by_label[label] = encoded
            completion_tokens[label] = encoded.completion_tokens
        encoded_items = [encoded_by_label[label] for label in LABELS]

        model.eval()
        with torch.inference_mode():
            ref_logps = sequence_logprobs(
                model, encoded_items, pad_token_id, device
            ).detach().float()
        ref_norm = logsumexp(float(ref_logps[idx].cpu()) for idx in range(len(LABELS)))
        ref_probs = {
            label: math.exp(float(ref_logps[idx].cpu()) - ref_norm)
            for idx, label in enumerate(LABELS)
        }
        artifacts[prompt_id] = PromptArtifacts(
            prompt_id=prompt_id,
            encoded_items=encoded_items,
            encoded_by_label=encoded_by_label,
            ref_logps=ref_logps.detach().clone(),
            ref_probs=ref_probs,
            completion_tokens=completion_tokens,
        )
        elapsed = time.perf_counter() - start
        prompt_seconds = time.perf_counter() - prompt_start
        progress_row = {
            "phase": "reference_scoring",
            "index": index,
            "total": total_prompts,
            "prompt_id": prompt_id,
            "prompt_seconds": prompt_seconds,
            "elapsed_seconds": elapsed,
        }
        if progress_path is not None:
            append_jsonl(progress_path, progress_row)
        if should_log:
            log(
                f"reference_scoring done {index}/{total_prompts} "
                f"prompt_id={prompt_id} prompt_seconds={prompt_seconds:.1f} "
                f"elapsed_seconds={elapsed:.1f}"
            )
    return artifacts


def build_joint_cases(
    *,
    cases: Sequence,
    prompt_artifacts: dict[str, PromptArtifacts],
    beta: float,
    baseline_tvs: dict[str, float],
    device: torch.device,
) -> list[JointCase]:
    joint_cases: list[JointCase] = []
    for case in cases:
        if tuple(case.response_indices) != LABELS:
            raise ValueError(f"{make_case_key(case)} has labels {case.response_indices}")
        chosen_idx_cpu, rejected_idx_cpu, pair_counts = build_pair_indices(case.rankings, LABELS)
        ref_probs = prompt_artifacts[case.prompt_id].ref_probs
        theoretical = solve_weighted_logistic_borda(
            beta,
            np.asarray(case.total_wins, dtype=float),
            np.asarray([ref_probs[label] for label in LABELS], dtype=float),
        )
        joint_cases.append(
            JointCase(
                case_key=make_case_key(case),
                prompt_id=case.prompt_id,
                block_name=case.block_name,
                num_rankings=len(case.rankings),
                rankings=tuple(case.rankings),
                chosen_idx=chosen_idx_cpu.to(device),
                rejected_idx=rejected_idx_cpu.to(device),
                pair_counts=pair_counts,
                theoretical_probs=None if theoretical is None else jsonable_probs(theoretical),
                baseline_tv_to_theory=baseline_tvs.get(make_case_key(case)),
            )
        )
    return joint_cases


def finite_stats(values: Sequence[float]) -> dict[str, float | int | None]:
    finite = [float(value) for value in values if math.isfinite(float(value))]
    if not finite:
        return {
            "count": 0,
            "mean": None,
            "median": None,
            "min": None,
            "max": None,
        }
    return {
        "count": len(finite),
        "mean": float(statistics.mean(finite)),
        "median": float(statistics.median(finite)),
        "min": float(min(finite)),
        "max": float(max(finite)),
    }


def append_aggregate_csv(path: Path, row: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "run_name",
        "k",
        "case_keys",
        "total_pairs",
        "steps",
        "lr",
        "beta",
        "mean_tv_to_theory",
        "median_tv_to_theory",
        "max_tv_to_theory",
        "mean_baseline_tv_to_theory",
        "mean_tv_degradation",
        "top_mismatches",
        "train_seconds",
        "run_json",
    ]
    exists = path.exists()
    with path.open("a", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        if not exists:
            writer.writeheader()
        writer.writerow({name: row.get(name) for name in fieldnames})


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--case-key", action="append", default=[])
    parser.add_argument("--case-keys-file", type=Path, default=None)
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
    parser.add_argument("--renderer", choices=("qwen", "llama2"), default="qwen")
    parser.add_argument(
        "--identity-mode",
        choices=("exact", "strip_identity", "neutralize_identity"),
        default="strip_identity",
    )
    parser.add_argument("--device", choices=("cpu", "mps", "cuda"), default="mps")
    parser.add_argument("--dtype", choices=("float16", "bfloat16", "float32"), default="float16")
    parser.add_argument("--beta", type=float, default=0.1)
    parser.add_argument("--lr", type=float, default=5e-5)
    parser.add_argument("--steps", type=int, default=100)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-length", type=int, default=4096)
    parser.add_argument("--log-every", type=int, default=10)
    parser.add_argument(
        "--train-prompt-log-every",
        type=int,
        default=0,
        help=(
            "Log every N prompts inside each training step to "
            "training_prompt_progress.jsonl; 0 disables."
        ),
    )
    parser.add_argument(
        "--setup-log-every",
        type=int,
        default=1,
        help="Log every N prompts during reference scoring/setup.",
    )
    parser.add_argument(
        "--save-checkpoints-every",
        type=int,
        default=0,
        help="Save intermediate LoRA checkpoints every N training steps; 0 disables.",
    )
    parser.add_argument("--lora-r", type=int, default=8)
    parser.add_argument("--lora-alpha", type=int, default=32)
    parser.add_argument("--lora-dropout", type=float, default=0.05)
    parser.add_argument("--target-modules", default="q_proj,v_proj")
    parser.add_argument(
        "--grad-clip",
        type=float,
        default=None,
        help="Clip trainable-parameter gradient norm after each full-batch step.",
    )
    parser.add_argument("--output-root", type=Path, default=Path("results/intermediate/multi_profile_dpo_qwen25"))
    parser.add_argument("--tag", default=None)
    parser.add_argument("--baseline-jsonl", type=Path, default=DEFAULT_BASELINE_JSONL)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--save-policy", action="store_true")
    parser.add_argument(
        "--fix-mistral-regex",
        action="store_true",
        help="Pass fix_mistral_regex=True when loading Mistral-family tokenizers.",
    )
    args = parser.parse_args()

    random.seed(args.seed)
    np.random.seed(args.seed)
    torch.manual_seed(args.seed)

    case_keys = collect_case_keys(args)
    cases = select_cases(args.dataset, case_keys)
    prompt_ids = list(dict.fromkeys(case.prompt_id for case in cases))
    log(f"selected_cases={len(cases)} prompts={len(prompt_ids)}")
    for key in case_keys:
        log(f"case_key={key}")
    if args.dry_run:
        return

    run_name = (
        safe_tag(args.tag)
        if args.tag
        else safe_tag(f"k{len(case_keys)}__seed{args.seed}__steps{args.steps}__lr{args.lr}")
    )
    run_dir = args.output_root / run_name
    run_dir.mkdir(parents=True, exist_ok=True)
    run_json = run_dir / "run.json"
    setup_progress_jsonl = run_dir / "setup_progress.jsonl"
    training_progress_jsonl = run_dir / "training_progress.jsonl"
    training_step_progress_jsonl = run_dir / "training_step_progress.jsonl"
    training_prompt_progress_jsonl = run_dir / "training_prompt_progress.jsonl"

    device = choose_device(args.device)
    dtype = dtype_from_name(args.dtype)
    baseline_tvs = load_baseline_tvs(args.baseline_jsonl)

    write_json(
        run_dir / "run_started.json",
        {
            "status": "started",
            "run_name": run_name,
            "case_keys": case_keys,
            "case_count": len(case_keys),
            "prompt_count": len(prompt_ids),
            "model": args.model,
            "renderer": args.renderer,
            "identity_mode": args.identity_mode,
            "device": str(device),
            "dtype": args.dtype,
            "beta": args.beta,
            "lr": args.lr,
            "steps": args.steps,
            "grad_clip": args.grad_clip,
            "save_policy": args.save_policy,
            "save_checkpoints_every": args.save_checkpoints_every,
            "train_prompt_log_every": args.train_prompt_log_every,
        },
    )

    setup_start = time.perf_counter()
    log(f"loading tokenizer/model model={args.model} dtype={args.dtype} device={device}")
    tokenizer_kwargs = {"trust_remote_code": True}
    if args.fix_mistral_regex:
        tokenizer_kwargs["fix_mistral_regex"] = True
    tokenizer = AutoTokenizer.from_pretrained(args.model, **tokenizer_kwargs)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    if tokenizer.pad_token_id is None:
        raise ValueError("Tokenizer has no pad_token_id")

    model = AutoModelForCausalLM.from_pretrained(
        args.model,
        torch_dtype=dtype,
        trust_remote_code=True,
    )
    model.to(device)
    model.eval()

    prompt_artifacts = build_prompt_artifacts(
        dataset=args.dataset,
        prompt_ids=prompt_ids,
        identity_mode=args.identity_mode,
        renderer=args.renderer,
        tokenizer=tokenizer,
        model=model,
        pad_token_id=tokenizer.pad_token_id,
        device=device,
        max_length=args.max_length,
        progress_path=setup_progress_jsonl,
        setup_log_every=args.setup_log_every,
    )
    joint_cases = build_joint_cases(
        cases=cases,
        prompt_artifacts=prompt_artifacts,
        beta=args.beta,
        baseline_tvs=baseline_tvs,
        device=device,
    )
    total_pairs = sum(case.num_pairs for case in joint_cases)
    setup_seconds = time.perf_counter() - setup_start
    log(f"total_pairs={total_pairs} setup_seconds={setup_seconds:.1f}")
    write_json(
        run_dir / "setup_complete.json",
        {
            "status": "setup_complete",
            "run_name": run_name,
            "case_count": len(case_keys),
            "prompt_count": len(prompt_ids),
            "total_pairs": total_pairs,
            "setup_seconds": setup_seconds,
        },
    )

    target_modules = parse_csv_arg(args.target_modules)
    lora_config = LoraConfig(
        r=args.lora_r,
        lora_alpha=args.lora_alpha,
        lora_dropout=args.lora_dropout,
        target_modules=target_modules,
        bias="none",
        task_type="CAUSAL_LM",
    )
    model = get_peft_model(model, lora_config)
    model.train()
    model.print_trainable_parameters()

    cases_by_prompt: dict[str, list[JointCase]] = {prompt_id: [] for prompt_id in prompt_ids}
    for joint_case in joint_cases:
        cases_by_prompt[joint_case.prompt_id].append(joint_case)
    prompt_case_counts = {
        prompt_id: len(cases_by_prompt[prompt_id]) for prompt_id in prompt_ids
    }
    prompt_pair_counts = {
        prompt_id: sum(joint_case.num_pairs for joint_case in cases_by_prompt[prompt_id])
        for prompt_id in prompt_ids
    }

    optimizer = torch.optim.AdamW(
        [parameter for parameter in model.parameters() if parameter.requires_grad],
        lr=args.lr,
    )
    training_log: list[dict] = []
    start = time.perf_counter()
    for step in range(1, args.steps + 1):
        step_start = time.perf_counter()
        append_jsonl(
            training_step_progress_jsonl,
            {
                "event": "step_start",
                "step": step,
                "elapsed_seconds": step_start - start,
            },
        )
        if step % args.log_every == 0 or step == 1 or step == args.steps:
            log(f"step {step} start elapsed_seconds={step_start - start:.1f}")
        optimizer.zero_grad(set_to_none=True)
        loss_value = 0.0
        for prompt_index, prompt_id in enumerate(prompt_ids, start=1):
            artifacts = prompt_artifacts[prompt_id]
            should_log_prompt = (
                args.train_prompt_log_every > 0
                and (
                    args.train_prompt_log_every <= 1
                    or prompt_index == 1
                    or prompt_index == len(prompt_ids)
                    or prompt_index % args.train_prompt_log_every == 0
                )
            )
            prompt_start = time.perf_counter()
            if should_log_prompt:
                prompt_base = {
                    "event": "prompt_start",
                    "step": step,
                    "prompt_index": prompt_index,
                    "prompt_count": len(prompt_ids),
                    "prompt_id": prompt_id,
                    "num_cases": prompt_case_counts[prompt_id],
                    "num_pairs": prompt_pair_counts[prompt_id],
                    "elapsed_seconds": prompt_start - start,
                    "step_elapsed_seconds": prompt_start - step_start,
                }
                append_jsonl(training_prompt_progress_jsonl, prompt_base)
                log(
                    "step "
                    f"{step} prompt {prompt_index}/{len(prompt_ids)} start "
                    f"prompt_id={prompt_id} cases={prompt_case_counts[prompt_id]} "
                    f"pairs={prompt_pair_counts[prompt_id]} "
                    f"elapsed_seconds={prompt_start - start:.1f}"
                )
            forward_start = time.perf_counter()
            policy_logps = sequence_logprobs(
                model, artifacts.encoded_items, tokenizer.pad_token_id, device
            ).float()
            forward_seconds = time.perf_counter() - forward_start
            ref_logps = artifacts.ref_logps.to(device)
            loss_start = time.perf_counter()
            prompt_loss_sum = None
            for joint_case in cases_by_prompt[prompt_id]:
                log_ratio_chosen = (
                    policy_logps[joint_case.chosen_idx] - ref_logps[joint_case.chosen_idx]
                )
                log_ratio_rejected = (
                    policy_logps[joint_case.rejected_idx]
                    - ref_logps[joint_case.rejected_idx]
                )
                logits = args.beta * (log_ratio_chosen - log_ratio_rejected)
                case_loss_sum = -F.logsigmoid(logits).sum()
                prompt_loss_sum = (
                    case_loss_sum
                    if prompt_loss_sum is None
                    else prompt_loss_sum + case_loss_sum
                )
            loss_seconds = time.perf_counter() - loss_start
            if prompt_loss_sum is None:
                if should_log_prompt:
                    prompt_done = time.perf_counter()
                    append_jsonl(
                        training_prompt_progress_jsonl,
                        {
                            "event": "prompt_skipped",
                            "step": step,
                            "prompt_index": prompt_index,
                            "prompt_count": len(prompt_ids),
                            "prompt_id": prompt_id,
                            "num_cases": prompt_case_counts[prompt_id],
                            "num_pairs": prompt_pair_counts[prompt_id],
                            "forward_seconds": forward_seconds,
                            "loss_seconds": loss_seconds,
                            "prompt_seconds": prompt_done - prompt_start,
                            "elapsed_seconds": prompt_done - start,
                            "step_elapsed_seconds": prompt_done - step_start,
                        },
                    )
                continue
            prompt_loss = prompt_loss_sum / total_pairs
            if not bool(torch.isfinite(prompt_loss).detach().cpu()):
                raise FloatingPointError(
                    f"Non-finite prompt loss at step={step} prompt_id={prompt_id}"
                )
            loss_value += float(prompt_loss.detach().cpu())
            backward_start = time.perf_counter()
            prompt_loss.backward()
            backward_seconds = time.perf_counter() - backward_start
            if should_log_prompt:
                prompt_done = time.perf_counter()
                append_jsonl(
                    training_prompt_progress_jsonl,
                    {
                        "event": "prompt_done",
                        "step": step,
                        "prompt_index": prompt_index,
                        "prompt_count": len(prompt_ids),
                        "prompt_id": prompt_id,
                        "num_cases": prompt_case_counts[prompt_id],
                        "num_pairs": prompt_pair_counts[prompt_id],
                        "prompt_loss": float(prompt_loss.detach().cpu()),
                        "forward_seconds": forward_seconds,
                        "loss_seconds": loss_seconds,
                        "backward_seconds": backward_seconds,
                        "prompt_seconds": prompt_done - prompt_start,
                        "elapsed_seconds": prompt_done - start,
                        "step_elapsed_seconds": prompt_done - step_start,
                    },
                )
                log(
                    "step "
                    f"{step} prompt {prompt_index}/{len(prompt_ids)} done "
                    f"loss={float(prompt_loss.detach().cpu()):.6g} "
                    f"forward_seconds={forward_seconds:.1f} "
                    f"backward_seconds={backward_seconds:.1f} "
                    f"prompt_seconds={prompt_done - prompt_start:.1f}"
                )
        if not math.isfinite(loss_value):
            raise FloatingPointError(f"Non-finite loss at step={step}: {loss_value}")
        clip_seconds = None
        if args.grad_clip is not None:
            clip_start = time.perf_counter()
            torch.nn.utils.clip_grad_norm_(
                [parameter for parameter in model.parameters() if parameter.requires_grad],
                max_norm=args.grad_clip,
            )
            clip_seconds = time.perf_counter() - clip_start
        optimizer_start = time.perf_counter()
        optimizer.step()
        optimizer_seconds = time.perf_counter() - optimizer_start
        step_done = time.perf_counter()
        append_jsonl(
            training_step_progress_jsonl,
            {
                "event": "step_done",
                "step": step,
                "loss": loss_value,
                "step_seconds": step_done - step_start,
                "optimizer_seconds": optimizer_seconds,
                "clip_seconds": clip_seconds,
                "elapsed_seconds": step_done - start,
            },
        )

        if step % args.log_every == 0 or step == args.steps:
            elapsed = time.perf_counter() - start
            row = {
                "step": step,
                "loss": loss_value,
                "elapsed_seconds": elapsed,
                "step_seconds": step_done - step_start,
                "optimizer_seconds": optimizer_seconds,
                "clip_seconds": clip_seconds,
            }
            training_log.append(row)
            checkpoint_dir = None
            if args.save_checkpoints_every > 0 and step % args.save_checkpoints_every == 0:
                checkpoint_dir = run_dir / "checkpoints" / f"step_{step:04d}"
                model.save_pretrained(checkpoint_dir)
            progress_row = dict(row)
            if checkpoint_dir is not None:
                progress_row["checkpoint_dir"] = str(checkpoint_dir)
            append_jsonl(training_progress_jsonl, progress_row)
            write_json(
                run_dir / "run_partial.json",
                {
                    "status": "training",
                    "run_name": run_name,
                    "case_count": len(case_keys),
                    "prompt_count": len(prompt_ids),
                    "total_pairs": total_pairs,
                    "setup_seconds": setup_seconds,
                    "last_step": step,
                    "steps": args.steps,
                    "training_log": training_log,
                },
            )
            log(
                f"step {step}: loss={loss_value:.6g} "
                f"step_seconds={step_done - step_start:.1f} "
                f"elapsed_seconds={elapsed:.1f}"
            )

    train_seconds = time.perf_counter() - start
    model.eval()
    final_by_prompt: dict[str, dict[str, float]] = {}
    final_logps_by_prompt: dict[str, dict[str, float]] = {}
    with torch.inference_mode():
        for prompt_id in prompt_ids:
            logps, probs = score_candidates(
                model,
                prompt_artifacts[prompt_id].encoded_by_label,
                tokenizer.pad_token_id,
                device,
            )
            final_logps_by_prompt[prompt_id] = logps
            final_by_prompt[prompt_id] = probs

    per_case_rows: list[dict] = []
    for joint_case in joint_cases:
        artifacts = prompt_artifacts[joint_case.prompt_id]
        final_probs = final_by_prompt[joint_case.prompt_id]
        theoretical_probs = joint_case.theoretical_probs
        row = {
            "case_key": joint_case.case_key,
            "prompt_id": joint_case.prompt_id,
            "block_name": joint_case.block_name,
            "num_rankings": joint_case.num_rankings,
            "num_pairs": joint_case.num_pairs,
            "rankings": joint_case.rankings,
            "pair_counts": joint_case.pair_counts,
            "completion_tokens": artifacts.completion_tokens,
            "reference_probs": artifacts.ref_probs,
            "theoretical_probs": theoretical_probs,
            "final_probs": final_probs,
            "final_logprobs": final_logps_by_prompt[joint_case.prompt_id],
            "tv_to_theory": None
            if theoretical_probs is None
            else tv_distance(final_probs, theoretical_probs),
            "max_abs_error": None
            if theoretical_probs is None
            else max_abs_error(final_probs, theoretical_probs),
            "tv_final_to_reference": tv_distance(final_probs, artifacts.ref_probs),
            "tv_theory_to_reference": None
            if theoretical_probs is None
            else tv_distance(theoretical_probs, artifacts.ref_probs),
            "baseline_tv_to_theory": joint_case.baseline_tv_to_theory,
            "top_reference": top_label(artifacts.ref_probs),
            "top_theory": None if theoretical_probs is None else top_label(theoretical_probs),
            "top_final": top_label(final_probs),
            "top_theory_matches_final": None
            if theoretical_probs is None
            else top_label(theoretical_probs) == top_label(final_probs),
            "top_reference_matches_final": top_label(artifacts.ref_probs) == top_label(final_probs),
        }
        per_case_rows.append(row)

    tvs = [
        float(row["tv_to_theory"])
        for row in per_case_rows
        if row["tv_to_theory"] is not None and math.isfinite(float(row["tv_to_theory"]))
    ]
    baseline_tvs_selected = [
        float(row["baseline_tv_to_theory"])
        for row in per_case_rows
        if row["baseline_tv_to_theory"] is not None
        and math.isfinite(float(row["baseline_tv_to_theory"]))
    ]
    tv_stats = finite_stats(tvs)
    baseline_stats = finite_stats(baseline_tvs_selected)
    mean_degradation = (
        None
        if tv_stats["mean"] is None or baseline_stats["mean"] is None
        else float(tv_stats["mean"]) - float(baseline_stats["mean"])
    )
    top_mismatches = sum(row["top_theory_matches_final"] is False for row in per_case_rows)

    record = {
        "run_name": run_name,
        "case_keys": case_keys,
        "model": args.model,
        "renderer": args.renderer,
        "identity_mode": args.identity_mode,
        "device": str(device),
        "dtype": args.dtype,
        "beta": args.beta,
        "lr": args.lr,
        "steps": args.steps,
        "seed": args.seed,
        "max_length": args.max_length,
        "baseline_jsonl": None if args.baseline_jsonl is None else str(args.baseline_jsonl),
        "lora": {
            "r": args.lora_r,
            "alpha": args.lora_alpha,
            "dropout": args.lora_dropout,
            "target_modules": target_modules,
        },
        "grad_clip": args.grad_clip,
        "total_pairs": total_pairs,
        "prompt_count": len(prompt_ids),
        "setup_seconds": setup_seconds,
        "train_seconds": train_seconds,
        "training_log": training_log,
        "per_case": per_case_rows,
        "aggregate": {
            "tv_to_theory": tv_stats,
            "single_profile_baseline_tv_to_theory": baseline_stats,
            "mean_tv_degradation": mean_degradation,
            "top_mismatches": top_mismatches,
        },
    }
    with run_json.open("w") as handle:
        json.dump(record, handle, indent=2, sort_keys=True)

    if args.save_policy:
        policy_dir = run_dir / "policy_lora"
        model.save_pretrained(policy_dir)
        tokenizer.save_pretrained(policy_dir)

    append_aggregate_csv(
        args.output_root / "aggregate.csv",
        {
            "run_name": run_name,
            "k": len(case_keys),
            "case_keys": json.dumps(case_keys),
            "total_pairs": total_pairs,
            "steps": args.steps,
            "lr": args.lr,
            "beta": args.beta,
            "mean_tv_to_theory": tv_stats["mean"],
            "median_tv_to_theory": tv_stats["median"],
            "max_tv_to_theory": tv_stats["max"],
            "mean_baseline_tv_to_theory": baseline_stats["mean"],
            "mean_tv_degradation": mean_degradation,
            "top_mismatches": top_mismatches,
            "train_seconds": train_seconds,
            "run_json": str(run_json),
        },
    )

    log(f"wrote {run_json}")
    log(
        "aggregate "
        + json.dumps(
            {
                "mean_tv_to_theory": tv_stats["mean"],
                "median_tv_to_theory": tv_stats["median"],
                "max_tv_to_theory": tv_stats["max"],
                "mean_baseline_tv_to_theory": baseline_stats["mean"],
                "mean_tv_degradation": mean_degradation,
                "top_mismatches": top_mismatches,
            },
            sort_keys=True,
        )
    )
    for row in per_case_rows:
        log(
            f"{row['case_key']} tv={row['tv_to_theory']} "
            f"baseline_tv={row['baseline_tv_to_theory']} "
            f"top={row['top_reference']}->{row['top_theory']}->{row['top_final']}"
        )


if __name__ == "__main__":
    main()
