#!/usr/bin/env python3
"""Batch empirical-vs-theory comparison for CoVal single-profile updates.

Loads one base model once, caches prompt encodings/reference distributions by
prompt id, resets only the LoRA parameters between profiles, and appends one
summary row per profile. Intended for long-running resumable sweeps.
"""

from __future__ import annotations

import argparse
import gc
import json
import math
import os
import random
import time
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np
from scipy.special import logsumexp as scipy_logsumexp
import torch
import torch.nn.functional as F

from scripts.post_training.nash_md_loss import finite_slate_nash_md_loss
from scripts.post_training.experiment_provenance import (
    load_frozen_references, provenance, ensure_metadata, successful_case_keys,
)
from peft import LoraConfig, get_peft_model
from transformers import AutoModelForCausalLM, AutoTokenizer

from scripts.theory.nlhf_tie_normalization import load_cases_tie_norm, solve_nlhf_tie_norm_log
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda_log
from scripts.post_training.train_coval_dpo import (
    EncodedCompletion,
    LABELS,
    build_pair_indices,
    choose_device,
    dtype_from_name,
    encode_completion,
    logsumexp,
    normalize_prompt_messages,
    render_full,
    render_prefix,
    safe_tag,
    score_candidates,
    sequence_logprobs,
)


def parse_csv(text: str) -> list[str]:
    return [part.strip() for part in text.split(",") if part.strip()]


def load_prompt_case_map(dataset: Path, identity_mode: str) -> dict[str, dict]:
    prompt_map: dict[str, dict] = {}
    with dataset.open() as handle:
        for line in handle:
            obj = json.loads(line)
            prompt_id = obj.get("prompt_id")
            if not prompt_id:
                continue
            responses: dict[str, str] = {}
            for response in obj["responses"]:
                assistant_text = next(
                    (
                        msg["content"]
                        for msg in response.get("messages", [])
                        if msg.get("role") == "assistant"
                    ),
                    None,
                )
                if assistant_text is not None:
                    responses[response["response_index"]] = assistant_text
            if set(responses) != set(LABELS):
                continue
            prompt_map[prompt_id] = {
                "prompt_id": prompt_id,
                "prompt_messages": normalize_prompt_messages(
                    obj["prompt"]["messages"], identity_mode=identity_mode
                ),
                "responses": responses,
            }
    return prompt_map


def make_case_key(case) -> str:
    return f"{case.prompt_id}:{case.block_name}"


def jsonable_probs(values: Iterable[float]) -> dict[str, float]:
    return {label: float(val) for label, val in zip(LABELS, values)}


def tv_distance(p: dict[str, float], q: dict[str, float]) -> float:
    return 0.5 * sum(abs(float(p[label]) - float(q[label])) for label in LABELS)


def max_abs_error(p: dict[str, float], q: dict[str, float]) -> float:
    return max(abs(float(p[label]) - float(q[label])) for label in LABELS)


def entropy(p: dict[str, float]) -> float:
    total = 0.0
    for label in LABELS:
        value = float(p[label])
        if value > 0:
            total -= value * math.log(value)
    return total


def capture_trainable_state(model) -> dict[str, torch.Tensor]:
    return {
        name: parameter.detach().cpu().clone()
        for name, parameter in model.named_parameters()
        if parameter.requires_grad
    }


def reset_trainable_state(model, initial_state: dict[str, torch.Tensor]) -> None:
    with torch.no_grad():
        for name, parameter in model.named_parameters():
            if parameter.requires_grad:
                parameter.copy_(initial_state[name].to(device=parameter.device, dtype=parameter.dtype))


def read_seen_keys(path: Path) -> set[str]:
    return successful_case_keys(path)


def read_case_key_filter(path: Path | None) -> set[str] | None:
    if path is None:
        return None
    allowed: set[str] = set()
    with path.open() as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            allowed.add(line)
    return allowed


def append_jsonl(path: Path, row: dict) -> None:
    with path.open("a") as handle:
        handle.write(json.dumps(row, sort_keys=True, allow_nan=False) + "\n")
        handle.flush()
        os.fsync(handle.fileno())


def write_status(path: Path, status: dict) -> None:
    with path.open("w") as handle:
        json.dump(status, handle, indent=2, sort_keys=True)


def maybe_empty_cache(device: torch.device) -> None:
    if device.type == "mps":
        try:
            torch.mps.empty_cache()
        except Exception:
            pass
    elif device.type == "cuda":
        torch.cuda.empty_cache()


def seed_everything(seed: int, device: torch.device | None = None) -> None:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if device is not None and device.type == "cuda":
        torch.cuda.manual_seed_all(seed)


def train_nlhf_case(
    model,
    encoded_items: Sequence[EncodedCompletion],
    ref_logps_tensor: torch.Tensor,
    ref_probs: dict[str, float],
    pad_token_id: int,
    device: torch.device,
    case,
    tau: float,
    lr: float,
    steps: int,
    mixture_coef: float,
    exploration_epsilon: float,
    exploration_decay_steps: int,
    checkpoint_every: int,
    grad_clip: float | None,
    weight_decay: float,
) -> tuple[dict[str, float], dict[str, float] | None, float, list[dict]]:
    wins = np.asarray(case.total_wins, dtype=float)
    ties = np.asarray(case.total_ties, dtype=float)
    theoretical_log = solve_nlhf_tie_norm_log(tau, wins, ties, ref_logps_tensor.detach().cpu().numpy().astype(float))
    if theoretical_log is None:
        raise RuntimeError('NLHF target solver failed; refusing to train without a checked target')
    theoretical_probs = jsonable_probs(np.exp(theoretical_log))

    totals = wins + wins.T + ties
    cbar = np.full_like(wins, 0.5, dtype=float)
    mask = totals > 0
    cbar[mask] = (wins[mask] + 0.5 * ties[mask]) / totals[mask]
    np.fill_diagonal(cbar, 0.5)
    preference_probs = torch.tensor(cbar, dtype=torch.float32, device=device)
    ref_cond_logps = F.log_softmax(ref_logps_tensor, dim=0).detach()
    checkpoints: list[dict] = []

    trainable_parameters = [parameter for parameter in model.parameters() if parameter.requires_grad]
    optimizer = torch.optim.AdamW(trainable_parameters, lr=lr, weight_decay=weight_decay)
    model.train()
    start = time.perf_counter()

    def record_checkpoint(step: int, log_policy: torch.Tensor) -> None:
        logs = log_policy.detach().cpu().numpy().astype(float)
        logs -= scipy_logsumexp(logs)
        probs = jsonable_probs(np.exp(logs))
        checkpoints.append(
            {
                "step": step,
                "probs": probs,
                "log_probs": jsonable_probs(logs),
                "tv_to_theory": None
                if theoretical_probs is None
                else tv_distance(probs, theoretical_probs),
                "entropy": entropy(probs),
                "top": max(LABELS, key=lambda label: probs[label]),
            }
        )

    if checkpoint_every > 0:
        model.eval()
        with torch.inference_mode():
            sequence_scores = sequence_logprobs(model, encoded_items, pad_token_id, device).float()
            record_checkpoint(0, F.log_softmax(sequence_scores, dim=0))
        model.train()

    for _step in range(steps):
        sequence_scores = sequence_logprobs(model, encoded_items, pad_token_id, device).float()
        log_policy = F.log_softmax(sequence_scores, dim=0)
        policy = log_policy.exp()
        if exploration_decay_steps > 0:
            effective_exploration_epsilon = exploration_epsilon * max(
                0.0,
                1.0 - (_step / exploration_decay_steps),
            )
        else:
            effective_exploration_epsilon = exploration_epsilon
        loss = finite_slate_nash_md_loss(
            log_policy, ref_cond_logps, preference_probs, tau,
            mixture_coef, effective_exploration_epsilon,
        )
        if not bool(torch.isfinite(loss).detach().cpu()):
            raise FloatingPointError(f"non-finite NLHF loss at step {_step + 1}: {float(loss.detach().cpu())}")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        if grad_clip is not None:
            grad_norm = torch.nn.utils.clip_grad_norm_(trainable_parameters, grad_clip)
            if not bool(torch.isfinite(grad_norm).detach().cpu()):
                raise FloatingPointError(
                    f"non-finite NLHF gradient norm at step {_step + 1}: {float(grad_norm.detach().cpu())}"
                )
        optimizer.step()
        step = _step + 1
        if checkpoint_every > 0 and (step % checkpoint_every == 0 or step == steps):
            model.eval()
            with torch.inference_mode():
                sequence_scores = sequence_logprobs(model, encoded_items, pad_token_id, device).float()
                record_checkpoint(step, F.log_softmax(sequence_scores, dim=0))
            model.train()
    train_seconds = time.perf_counter() - start
    model.eval()
    with torch.inference_mode():
        _logps, final_probs = score_candidates(
            model,
            {label: encoded_items[idx] for idx, label in enumerate(LABELS)},
            pad_token_id,
            device,
        )
    return final_probs, theoretical_probs, train_seconds, checkpoints


def train_dpo_case(
    model,
    encoded_items: Sequence[EncodedCompletion],
    ref_logps_tensor: torch.Tensor,
    ref_probs: dict[str, float],
    pad_token_id: int,
    device: torch.device,
    case,
    beta: float,
    lr: float,
    steps: int,
    full_batch: bool,
    batch_size: int,
    grad_clip: float | None,
    log_every: int,
    case_key: str,
    weight_decay: float,
) -> tuple[dict[str, float], dict[str, float] | None, float]:
    wins = np.asarray(case.total_wins, dtype=float)
    theoretical_log = solve_weighted_logistic_borda_log(
        beta,
        wins,
        ref_logps_tensor.detach().cpu().numpy().astype(float),
    )
    if theoretical_log is None:
        raise RuntimeError('RTBT target unavailable; check domain and solver before training')
    theoretical_probs = jsonable_probs(np.exp(theoretical_log))

    chosen_idx_cpu, rejected_idx_cpu, pair_counts = build_pair_indices(case.rankings, LABELS)
    chosen_idx = chosen_idx_cpu.to(device)
    rejected_idx = rejected_idx_cpu.to(device)
    ref_logps_tensor = ref_logps_tensor.to(device)
    num_pairs = int(chosen_idx.shape[0])

    trainable_parameters = [
        parameter for parameter in model.parameters() if parameter.requires_grad
    ]
    optimizer = torch.optim.AdamW(trainable_parameters, lr=lr, weight_decay=weight_decay)
    model.train()
    start = time.perf_counter()
    for step in range(1, steps + 1):
        step_start = time.perf_counter()
        if full_batch:
            batch_chosen = chosen_idx
            batch_rejected = rejected_idx
        else:
            batch_indices = torch.randint(0, num_pairs, (batch_size,), device=device)
            batch_chosen = chosen_idx[batch_indices]
            batch_rejected = rejected_idx[batch_indices]

        policy_logps = sequence_logprobs(model, encoded_items, pad_token_id, device).float()
        log_ratio_chosen = policy_logps[batch_chosen] - ref_logps_tensor[batch_chosen]
        log_ratio_rejected = policy_logps[batch_rejected] - ref_logps_tensor[batch_rejected]
        logits = beta * (log_ratio_chosen - log_ratio_rejected)
        loss = -F.logsigmoid(logits).mean()
        if not bool(torch.isfinite(loss).detach().cpu()):
            raise FloatingPointError(f"non-finite DPO loss for {case_key} at step {step}")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        if grad_clip is not None:
            grad_norm = torch.nn.utils.clip_grad_norm_(trainable_parameters, grad_clip)
            if not bool(torch.isfinite(grad_norm).detach().cpu()):
                raise FloatingPointError(f"non-finite DPO gradient for {case_key} at step {step}")
        optimizer.step()
        if log_every > 0 and (step == 1 or step == steps or step % log_every == 0):
            elapsed = time.perf_counter() - start
            print(
                f"[dpo-step] {case_key} step={step}/{steps} "
                f"loss={loss.item():.6g} step_secs={time.perf_counter() - step_start:.1f} "
                f"elapsed_secs={elapsed:.1f}",
                flush=True,
            )
    train_seconds = time.perf_counter() - start
    model.eval()
    with torch.inference_mode():
        _logps, final_probs = score_candidates(
            model,
            {label: encoded_items[idx] for idx, label in enumerate(LABELS)},
            pad_token_id,
            device,
        )
    return final_probs, theoretical_probs, train_seconds


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog=(
            "The defaults are generic. Use explicit flags from README.md or "
            "the curated *_meta.json files to reproduce paper runs."
        ),
    )
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--blocks", default="world,personal")
    parser.add_argument("--rules", default="nlhf,dpo")
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
    parser.add_argument("--model-revision", default=None,
                        help="Pinned Hugging Face commit for the local model snapshot; recorded in provenance.")
    parser.add_argument("--reference-cache", type=Path, default=None,
                        help="Freeze these elicited references for selection, theoretical targets and training loss.")
    parser.add_argument("--cpu-threads", type=int, default=4)
    parser.add_argument("--mps-memory-fraction", type=float, default=0.30)
    parser.add_argument("--renderer", choices=("qwen", "llama2"), default="qwen")
    parser.add_argument(
        "--identity-mode",
        choices=("exact", "strip_identity", "neutralize_identity"),
        default="strip_identity",
    )
    parser.add_argument("--device", choices=("cpu", "mps", "cuda"), default="mps")
    parser.add_argument(
        "--dtype",
        choices=("float16", "bfloat16", "float32"),
        default="float16",
        help="Computation dtype. Paper Nash-MD and Mistral-Nemo DPO runs override this to float32.",
    )
    parser.add_argument("--tau", type=float, default=0.01)
    parser.add_argument("--beta", type=float, default=0.1)
    parser.add_argument(
        "--lr",
        type=float,
        default=1e-7,
        help="Learning rate. Paper runs override this; see README.md and curated *_meta.json files.",
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=200,
        help="Optimizer steps. Paper DPO uses 100; paper Nash-MD uses 300.",
    )
    parser.add_argument(
        "--nlhf-exploration-epsilon",
        type=float,
        default=0.0,
        help="Historical uniform exploration floor in [0, 1).",
    )
    parser.add_argument(
        "--nlhf-exploration-decay-steps",
        type=int,
        default=0,
        help=(
            "Linearly decay --nlhf-exploration-epsilon to zero over this many "
            "NLHF steps. A value of 0 keeps the exploration floor constant."
        ),
    )
    parser.add_argument(
        "--nlhf-mixture-coef",
        type=float,
        default=0.0,
        help="Mixture coefficient for the Nash-MD opponent distribution.",
    )
    parser.add_argument(
        "--nlhf-checkpoint-every",
        type=int,
        default=0,
        help="If positive, store NLHF policy snapshots every N steps.",
    )
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--reset-seed-per-case",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Reset Python, NumPy, and Torch RNGs to --seed before each profile.",
    )
    parser.add_argument("--max-length", type=int, default=4096)
    parser.add_argument("--lora-r", type=int, default=8)
    parser.add_argument("--lora-alpha", type=int, default=32)
    parser.add_argument(
        "--lora-dropout",
        type=float,
        default=0.05,
        help="LoRA dropout. Paper DPO uses 0.05; paper Nash-MD uses 0.0.",
    )
    parser.add_argument("--target-modules", default="q_proj,v_proj")
    parser.add_argument("--dpo-full-batch", action="store_true")
    parser.add_argument("--dpo-batch-size", type=int, default=4)
    parser.add_argument(
        "--grad-clip",
        type=float,
        default=None,
        help="Clip LoRA gradient norm before each optimizer step.",
    )
    parser.add_argument(
        "--weight-decay",
        type=float,
        default=0.01,
        help=(
            "AdamW weight decay. Paper Nash-MD runs use 0.0."
        ),
    )
    parser.add_argument(
        "--dpo-log-every",
        type=int,
        default=0,
        help="If positive, print DPO step additional_checks every N training steps.",
    )
    parser.add_argument("--max-cases", type=int, default=None)
    parser.add_argument("--max-new-cases", type=int, default=None)
    parser.add_argument("--case-keys-file", type=Path, default=None)
    parser.add_argument("--output-root", type=Path, default=Path("results/intermediate/empirical_vs_theory_all_profiles"))
    parser.add_argument("--tag", default=None)
    parser.add_argument(
        "--fix-mistral-regex",
        action="store_true",
        help="Pass fix_mistral_regex=True when loading Mistral-family tokenizers.",
    )
    args = parser.parse_args()

    if not 0.0 <= args.nlhf_exploration_epsilon < 1.0:
        raise ValueError("--nlhf-exploration-epsilon must be in [0, 1)")
    if args.nlhf_exploration_decay_steps < 0:
        raise ValueError("--nlhf-exploration-decay-steps must be nonnegative")
    if not 0.0 <= args.nlhf_mixture_coef <= 1.0:
        raise ValueError("--nlhf-mixture-coef must be in [0, 1]")
    if args.nlhf_checkpoint_every < 0:
        raise ValueError("--nlhf-checkpoint-every must be nonnegative")
    if args.weight_decay < 0:
        raise ValueError("--weight-decay must be nonnegative")

    blocks = parse_csv(args.blocks)
    rules = parse_csv(args.rules)
    device = choose_device(args.device)
    if args.cpu_threads <= 0 or not 0 < args.mps_memory_fraction <= 1:
        raise ValueError('Require positive CPU threads and an MPS memory fraction in (0,1]')
    torch.set_num_threads(args.cpu_threads)
    if device.type == 'mps':
        torch.mps.set_per_process_memory_fraction(args.mps_memory_fraction)
    dtype = dtype_from_name(args.dtype)
    seed_everything(args.seed, device)

    cases = load_cases_tie_norm(args.dataset, blocks)
    if args.max_cases is not None:
        cases = cases[: args.max_cases]
    allowed_case_keys = read_case_key_filter(args.case_keys_file)
    if allowed_case_keys is not None:
        cases = [case for case in cases if make_case_key(case) in allowed_case_keys]
        missing = allowed_case_keys-{make_case_key(case) for case in cases}
        if missing:
            raise ValueError(f'Requested case keys not found: {sorted(missing)}')

    frozen_references = (load_frozen_references(args.reference_cache, LABELS)
                         if args.reference_cache is not None else None)
    if frozen_references is not None:
        missing = {case.prompt_id for case in cases}-frozen_references.keys()
        if missing:
            raise ValueError(f'Missing frozen references for {len(missing)} prompts')
        if any(frozen_references[c.prompt_id].get('identity_mode') != args.identity_mode
               or frozen_references[c.prompt_id].get('renderer') != args.renderer for c in cases):
            raise ValueError('Frozen reference prompt rendering differs from training')

    prompt_cases = load_prompt_case_map(args.dataset, args.identity_mode)
    total_cases = len(cases)
    tag = f"__{safe_tag(args.tag)}" if args.tag else ""

    print(f"loaded_cases={total_cases} blocks={blocks} rules={rules}")
    print(f"loading tokenizer/model model={args.model} dtype={args.dtype} device={device}")

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

    target_modules = [name.strip() for name in args.target_modules.split(",") if name.strip()]
    lora_config = LoraConfig(
        r=args.lora_r,
        lora_alpha=args.lora_alpha,
        lora_dropout=args.lora_dropout,
        target_modules=target_modules,
        bias="none",
        task_type="CAUSAL_LM",
    )
    model = get_peft_model(model, lora_config)
    initial_trainable_state = capture_trainable_state(model)
    model.train()

    encoded_cache: dict[str, list[EncodedCompletion]] = {}
    reference_cache: dict[str, tuple[torch.Tensor, dict[str, float], dict[str, int]]] = {}
    initial_model_probabilities: dict[str, dict[str, float]] = {}

    def get_prompt_artifacts(prompt_id: str) -> tuple[list[EncodedCompletion], torch.Tensor, dict[str, float], dict[str, int]]:
        if prompt_id in encoded_cache and prompt_id in reference_cache:
            ref_tensor, ref_probs, token_counts = reference_cache[prompt_id]
            return encoded_cache[prompt_id], ref_tensor, ref_probs, token_counts

        prompt_case = prompt_cases[prompt_id]
        prefix_text = render_prefix(prompt_case["prompt_messages"], args.renderer)
        encoded_items: list[EncodedCompletion] = []
        token_counts: dict[str, int] = {}
        for label in LABELS:
            full_text = render_full(
                prompt_case["prompt_messages"],
                prompt_case["responses"][label],
                args.renderer,
            )
            encoded = encode_completion(
                tokenizer, label, prefix_text, full_text, args.max_length
            )
            encoded_items.append(encoded)
            token_counts[label] = encoded.completion_tokens

        model.eval()
        with torch.inference_mode():
            ref_logps_tensor = sequence_logprobs(
                model, encoded_items, tokenizer.pad_token_id, device
            ).detach().float()
        model.train()
        ref_probs = {
            label: math.exp(float(ref_logps_tensor[idx].cpu()) - logsumexp(float(ref_logps_tensor[j].cpu()) for j in range(len(LABELS))))
            for idx, label in enumerate(LABELS)
        }
        initial_model_probabilities[prompt_id] = ref_probs.copy()
        if frozen_references is not None:
            fixed = frozen_references[prompt_id]
            ref_logps_tensor = torch.tensor([fixed['response_logprobs'][x] for x in LABELS],
                                           dtype=torch.float32, device=device)
            ref_probs = {x: float(fixed['rho'][x]) for x in LABELS}
        encoded_cache[prompt_id] = encoded_items
        reference_cache[prompt_id] = (ref_logps_tensor.detach().clone(), ref_probs, token_counts)
        return encoded_items, ref_logps_tensor.detach().clone(), ref_probs, token_counts

    for rule in rules:
        rule_dir = args.output_root / safe_tag(Path(args.model).name) / rule
        rule_dir.mkdir(parents=True, exist_ok=True)
        run_name = (
            f"{rule}__blocks-{safe_tag('-'.join(blocks))}__"
            f"steps{args.steps}__lr{args.lr}__tau{args.tau}__beta{args.beta}{tag}"
        )
        results_path = rule_dir / f"{run_name}.jsonl"
        status_path = rule_dir / f"{run_name}.status.json"
        meta_path = rule_dir / f"{run_name}.meta.json"
        if results_path.exists() and results_path.stat().st_size and not meta_path.exists():
            raise ValueError('Existing result rows have no immutable run metadata; use a new output/tag')
        seen = read_seen_keys(results_path)

        metadata = {
            "rule": rule,
            "model": args.model,
            "renderer": args.renderer,
            "identity_mode": args.identity_mode,
            "device": str(device),
            "dtype": args.dtype,
            "tau": args.tau,
            "beta": args.beta,
            "lr": args.lr,
            "steps": args.steps,
            "nlhf_exploration_epsilon": args.nlhf_exploration_epsilon,
            "nlhf_exploration_decay_steps": args.nlhf_exploration_decay_steps,
            "nlhf_mixture_coef": args.nlhf_mixture_coef,
            "nlhf_checkpoint_every": args.nlhf_checkpoint_every,
            "blocks": blocks,
            "seed": args.seed,
            "reset_seed_per_case": args.reset_seed_per_case,
            "lora": {
                "r": args.lora_r,
                "alpha": args.lora_alpha,
                "dropout": args.lora_dropout,
                "target_modules": target_modules,
            },
            "dpo_full_batch": args.dpo_full_batch,
            "dpo_batch_size": args.dpo_batch_size,
            "grad_clip": args.grad_clip,
            "weight_decay": args.weight_decay,
            "dpo_log_every": args.dpo_log_every,
            "results_path": str(results_path),
            "total_cases": total_cases,
            "case_keys_file": None if args.case_keys_file is None else str(args.case_keys_file),
            "reference_cache": None if args.reference_cache is None else str(args.reference_cache),
            "cpu_threads": args.cpu_threads,
            "mps_memory_fraction": args.mps_memory_fraction,
            "provenance": provenance(args.dataset, args.reference_cache, args.case_keys_file, args.model_revision),
        }
        ensure_metadata(meta_path, metadata)

        completed = 0
        failed = 0
        new_completed = 0
        started_rule = time.perf_counter()
        for idx, case in enumerate(cases, start=1):
            case_key = make_case_key(case)
            if case_key in seen:
                completed += 1
                continue

            if args.reset_seed_per_case:
                seed_everything(args.seed, device)
            reset_trainable_state(model, initial_trainable_state)
            maybe_empty_cache(device)
            gc.collect()

            try:
                encoded_items, ref_logps_tensor, ref_probs, token_counts = get_prompt_artifacts(case.prompt_id)
                case_start = time.perf_counter()
                if rule == "nlhf":
                    final_probs, theoretical_probs, train_seconds, nlhf_checkpoints = train_nlhf_case(
                        model=model,
                        encoded_items=encoded_items,
                        ref_logps_tensor=ref_logps_tensor.to(device),
                        ref_probs=ref_probs,
                        pad_token_id=tokenizer.pad_token_id,
                        device=device,
                        case=case,
                        tau=args.tau,
                        lr=args.lr,
                        steps=args.steps,
                        mixture_coef=args.nlhf_mixture_coef,
                        exploration_epsilon=args.nlhf_exploration_epsilon,
                        exploration_decay_steps=args.nlhf_exploration_decay_steps,
                        checkpoint_every=args.nlhf_checkpoint_every,
                        grad_clip=args.grad_clip,
                        weight_decay=args.weight_decay,
                    )
                elif rule == "dpo":
                    nlhf_checkpoints = []
                    print(f"[dpo-start] {completed + 1}/{total_cases} {case_key}", flush=True)
                    final_probs, theoretical_probs, train_seconds = train_dpo_case(
                        model=model,
                        encoded_items=encoded_items,
                        ref_logps_tensor=ref_logps_tensor.to(device),
                        ref_probs=ref_probs,
                        pad_token_id=tokenizer.pad_token_id,
                        device=device,
                        case=case,
                        beta=args.beta,
                        lr=args.lr,
                        steps=args.steps,
                        full_batch=args.dpo_full_batch,
                        batch_size=args.dpo_batch_size,
                        grad_clip=args.grad_clip,
                        log_every=args.dpo_log_every,
                        case_key=case_key,
                        weight_decay=args.weight_decay,
                    )
                else:
                    raise ValueError(f"Unknown rule: {rule}")
                case_seconds = time.perf_counter() - case_start
                row = {
                    "case_key": case_key,
                    "prompt_id": case.prompt_id,
                    "block_name": case.block_name,
                    "index": idx,
                    "rule": rule,
                    "num_rankings": len(case.rankings),
                    "reference_probs": ref_probs,
                    "reference_sequence_logprobs": jsonable_probs(ref_logps_tensor.detach().cpu().numpy()),
                    "initial_model_probs": initial_model_probabilities[case.prompt_id],
                    "theoretical_probs": theoretical_probs,
                    "final_probs": final_probs,
                    "tv_to_theory": None if theoretical_probs is None else tv_distance(final_probs, theoretical_probs),
                    "max_abs_error": None if theoretical_probs is None else max_abs_error(final_probs, theoretical_probs),
                    "duration_seconds": case_seconds,
                    "train_seconds": train_seconds,
                    "nlhf_exploration_epsilon": args.nlhf_exploration_epsilon if rule == "nlhf" else None,
                    "nlhf_exploration_decay_steps": args.nlhf_exploration_decay_steps if rule == "nlhf" else None,
                    "nlhf_mixture_coef": args.nlhf_mixture_coef if rule == "nlhf" else None,
                    "weight_decay": args.weight_decay,
                    "nlhf_checkpoints": nlhf_checkpoints if rule == "nlhf" else [],
                    "completion_tokens": token_counts,
                    "theory_available": theoretical_probs is not None,
                }
                append_jsonl(results_path, row)
                seen.add(case_key)
                completed += 1
                new_completed += 1
                elapsed = time.perf_counter() - started_rule
                avg = elapsed / completed if completed else float("nan")
                remaining = avg * (total_cases - completed) if completed else float("nan")
                print(
                    f"[{rule}] {completed}/{total_cases} {case_key} "
                    f"tv={row['tv_to_theory']} secs={case_seconds:.1f} "
                    f"eta_hours={remaining / 3600:.1f}"
                )
                write_status(
                    status_path,
                    {
                        "rule": rule,
                        "completed": completed,
                        "total_cases": total_cases,
                        "last_case_key": case_key,
                        "elapsed_seconds": elapsed,
                        "avg_seconds_per_case": avg,
                        "estimated_remaining_seconds": remaining,
                        "results_path": str(results_path),
                    },
                )
                if args.max_new_cases is not None and new_completed >= args.max_new_cases:
                    print(
                        f"[{rule}] stopping after max_new_cases={args.max_new_cases} "
                        f"(completed={completed}/{total_cases})"
                    )
                    break
            except Exception as exc:
                row = {
                    "case_key": case_key,
                    "prompt_id": case.prompt_id,
                    "block_name": case.block_name,
                    "index": idx,
                    "rule": rule,
                    "error": repr(exc),
                }
                append_jsonl(results_path, row)
                failed += 1
                new_completed += 1
                print(f"[{rule}] ERROR {case_key}: {exc!r}")
                write_status(
                    status_path,
                    {
                        "rule": rule,
                        "completed": completed,
                        "total_cases": total_cases,
                        "last_case_key": case_key,
                        "error": repr(exc),
                        "results_path": str(results_path),
                    },
                )
                if args.max_new_cases is not None and new_completed >= args.max_new_cases:
                    print(
                        f"[{rule}] stopping after max_new_cases={args.max_new_cases} "
                        f"(completed={completed}/{total_cases})"
                    )
                    break

        elapsed = time.perf_counter() - started_rule
        print(f"[{rule}] done successful={completed} failed={failed} elapsed_hours={elapsed / 3600:.2f}")
        if failed:
            raise RuntimeError(f'{failed} {rule} cases failed; failures were logged and remain eligible for retry')


if __name__ == "__main__":
    main()
