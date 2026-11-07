#!/usr/bin/env python3
"""Sequential action-restricted Online-IPO checks for NLHF commutativity.

This script tests the empirical analogue of

    F(R2, F(R1, rho))  vs.  F(R1, F(R2, rho)).

For each stage, the reference distribution in the Online-IPO loss is the
model-induced distribution at the start of that stage, matching the formal
reference-update structure. The model is trained continuously through the two
stages, but the four-candidate reference log-probabilities are frozen within
each stage.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

import numpy as np
import torch
import torch.nn.functional as F
from peft import LoraConfig, get_peft_model
from transformers import AutoModelForCausalLM, AutoTokenizer

from scripts.theory.nlhf_tie_normalization import solve_nlhf_tie_norm
from scripts.post_training.train_coval_dpo import (
    LABELS,
    dtype_from_name,
    encode_completion,
    load_prompt_case,
    logsumexp,
    render_full,
    render_prefix,
    safe_tag,
    sequence_logprobs,
    choose_device,
)
from scripts.additional_checks.train_coval_online_ipo import normalized_support_matrix, profile_matrices


@dataclass(frozen=True)
class CommutativityPreset:
    prompt_id: str
    block_name: str
    r1: tuple[str, ...]
    r2: tuple[str, ...]


def expand_grouped(groups: Sequence[tuple[int, str]]) -> tuple[str, ...]:
    out: list[str] = []
    for count, ranking in groups:
        out.extend([ranking] * count)
    return tuple(out)


PRESETS: dict[str, CommutativityPreset] = {
    "main_uniform_f450": CommutativityPreset(
        prompt_id="f450f2e2-1d90-577e-a311-c95fb9960433",
        block_name="world",
        r1=expand_grouped(
            [
                (4, "D>A>C>B"),
                (3, "A>D>C>B"),
                (1, "B=C=D>A"),
                (1, "B>C>D>A"),
                (1, "D>A=C>B"),
                (1, "C=D>A>B"),
            ]
        ),
        r2=expand_grouped(
            [
                (1, "A>D>C>B"),
                (1, "A=C>D>B"),
                (1, "A>D>B>C"),
                (3, "C>A>B=D"),
                (1, "D>C>A>B"),
                (1, "B=C>A>D"),
                (1, "A>D>B=C"),
                (1, "A>C>D>B"),
            ]
        ),
    ),
    "qwen_da331": CommutativityPreset(
        prompt_id="da331e43-535b-5dd9-9718-6b048de5e015",
        block_name="world",
        r1=expand_grouped(
            [
                (4, "A>D>B>C"),
                (3, "A>D>B=C"),
                (1, "A=D>B=C"),
                (1, "C>A>B=D"),
                (1, "A>B=C=D"),
                (1, "A>D>C>B"),
            ]
        ),
        r2=expand_grouped(
            [
                (1, "D>A>B>C"),
                (1, "D>A>C=B"),
                (1, "A>D>C>B"),
                (1, "D>B>A>C"),
                (1, "A>B=C>D"),
                (1, "D>A=C>B"),
                (1, "A>D>B=C"),
                (1, "D>A>C>B"),
                (1, "A>D>B>C"),
                (1, "D>A>B=C"),
            ]
        ),
    ),
    "main_nemo_2720": CommutativityPreset(
        prompt_id="2720d0fa-c8f8-598d-a849-e73e3ddccabb",
        block_name="world",
        r1=expand_grouped(
            [
                (2, "B>D>A=C"),
                (1, "B=D>A=C"),
                (2, "D=B>A=C"),
                (1, "B>D>C>A"),
            ]
        ),
        r2=expand_grouped(
            [
                (1, "D>B>A=C"),
                (1, "D>C>B>A"),
                (2, "D>B>A>C"),
                (1, "A=B=C=D"),
            ]
        ),
    ),
    "nemo_9066": CommutativityPreset(
        prompt_id="9066b3b8-4b6f-5676-a873-261341da3c93",
        block_name="world",
        r1=(
            "C>B=A>D",
            "C>B>A>D",
            "B>A=D>C",
            "C>B>D>A",
            "B>A>C>D",
        ),
        r2=(
            "A>B>D>C",
            "C=D>A>B",
            "A>B>C=D",
            "C>A>B=D",
            "B=A>C=D",
        ),
    ),
}


def probs_from_logps(logps: dict[str, float]) -> dict[str, float]:
    norm = logsumexp(logps.values())
    return {label: math.exp(logps[label] - norm) for label in LABELS}


def tensor_by_label(values: torch.Tensor) -> dict[str, float]:
    return {label: float(values[idx].detach().cpu()) for idx, label in enumerate(LABELS)}


def numpy_by_label(values: np.ndarray) -> dict[str, float]:
    return {label: float(values[idx]) for idx, label in enumerate(LABELS)}


def tv_distance(p: dict[str, float], q: dict[str, float]) -> float:
    return 0.5 * sum(abs(p[label] - q[label]) for label in LABELS)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--preset", choices=sorted(PRESETS), default="qwen_da331")
    parser.add_argument("--order", choices=("12", "21"), default="12")
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
    parser.add_argument("--renderer", choices=("qwen", "llama2"), default="qwen")
    parser.add_argument("--identity-mode", choices=("exact", "strip_identity", "neutralize_identity"), default="strip_identity")
    parser.add_argument("--device", choices=("cpu", "mps", "cuda"), default="mps")
    parser.add_argument("--dtype", choices=("float16", "bfloat16", "float32"), default="float16")
    parser.add_argument("--beta", type=float, default=0.01)
    parser.add_argument("--steps-per-stage", type=int, default=100)
    parser.add_argument("--lr", type=float, default=5e-7)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-length", type=int, default=4096)
    parser.add_argument("--log-every", type=int, default=10)
    parser.add_argument("--lora-r", type=int, default=8)
    parser.add_argument("--lora-alpha", type=int, default=32)
    parser.add_argument("--lora-dropout", type=float, default=0.05)
    parser.add_argument("--target-modules", default="q_proj,v_proj")
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/online_ipo_commutativity_runs"))
    parser.add_argument("--tag", default=None)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--save-policy", action="store_true")
    parser.add_argument(
        "--fix-mistral-regex",
        action="store_true",
        help="Pass fix_mistral_regex=True when loading Mistral-family tokenizers.",
    )
    args = parser.parse_args()

    if args.beta <= 0:
        raise ValueError("--beta must be positive")
    random.seed(args.seed)
    np.random.seed(args.seed)
    torch.manual_seed(args.seed)

    preset = PRESETS[args.preset]
    stage_specs = [("R1", preset.r1), ("R2", preset.r2)]
    if args.order == "21":
        stage_specs = list(reversed(stage_specs))

    print(
        f"preset={args.preset} prompt={preset.prompt_id}:{preset.block_name} "
        f"order={args.order}"
    )
    for stage_name, rankings in stage_specs:
        wins, ties = profile_matrices(rankings, LABELS)
        print(
            f"{stage_name}: voters={len(rankings)} normalized_support="
            + json.dumps(normalized_support_matrix(wins, ties).tolist())
        )
    if args.dry_run:
        return

    device = choose_device(args.device)
    dtype = dtype_from_name(args.dtype)
    prompt_case = load_prompt_case(args.dataset, preset.prompt_id, args.identity_mode)
    prefix_text = render_prefix(prompt_case.prompt_messages, args.renderer)

    tokenizer_kwargs = {"trust_remote_code": True}
    if args.fix_mistral_regex:
        tokenizer_kwargs["fix_mistral_regex"] = True
    tokenizer = AutoTokenizer.from_pretrained(args.model, **tokenizer_kwargs)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    if tokenizer.pad_token_id is None:
        raise ValueError("Tokenizer has no pad_token_id")

    encoded_by_label = {}
    for label in LABELS:
        full_text = render_full(prompt_case.prompt_messages, prompt_case.responses[label], args.renderer)
        encoded_by_label[label] = encode_completion(
            tokenizer, label, prefix_text, full_text, args.max_length
        )
    encoded_items = [encoded_by_label[label] for label in LABELS]
    print(
        "completion_tokens="
        + json.dumps({label: encoded_by_label[label].completion_tokens for label in LABELS}, sort_keys=True)
    )

    print(f"loading model={args.model} dtype={args.dtype} device={device}")
    model = AutoModelForCausalLM.from_pretrained(
        args.model,
        torch_dtype=dtype,
        trust_remote_code=True,
    )
    model.to(device)
    model.eval()

    with torch.inference_mode():
        base_logps_tensor = sequence_logprobs(
            model, encoded_items, tokenizer.pad_token_id, device
        ).detach().float()
    base_logps = {label: float(base_logps_tensor[idx].cpu()) for idx, label in enumerate(LABELS)}
    base_probs = probs_from_logps(base_logps)
    print("base_reference_probs=" + json.dumps(base_probs, sort_keys=True))

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
    model.train()
    model.print_trainable_parameters()
    optimizer = torch.optim.AdamW(
        [parameter for parameter in model.parameters() if parameter.requires_grad],
        lr=args.lr,
    )

    target_gap = 1.0 / (2.0 * args.beta)
    stage_records: list[dict] = []
    theory_rho = np.asarray([base_probs[label] for label in LABELS], dtype=float)

    def compute_policy_state() -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        sequence_logps = sequence_logprobs(model, encoded_items, tokenizer.pad_token_id, device).float()
        log_policy = F.log_softmax(sequence_logps, dim=0)
        policy = log_policy.exp()
        return sequence_logps, log_policy, policy

    def expected_ipo_loss(
        log_policy: torch.Tensor,
        policy: torch.Tensor,
        ref_cond_logps: torch.Tensor,
        support: torch.Tensor,
    ) -> torch.Tensor:
        log_ratio = log_policy - ref_cond_logps
        pair_logit = log_ratio[:, None] - log_ratio[None, :]
        chosen_x_loss = (pair_logit - target_gap) ** 2
        chosen_y_loss = (-pair_logit - target_gap) ** 2
        expected_pair_loss = support * chosen_x_loss + (1.0 - support) * chosen_y_loss
        pair_weights = policy.detach()[:, None] * policy.detach()[None, :]
        return torch.sum(pair_weights * expected_pair_loss)

    for stage_name, rankings in stage_specs:
        wins, ties = profile_matrices(rankings, LABELS)
        cbar = normalized_support_matrix(wins, ties)
        support = torch.tensor(cbar, dtype=torch.float32, device=device)

        model.eval()
        with torch.inference_mode():
            ref_sequence_logps, ref_cond_logps, ref_policy = compute_policy_state()
        model.train()
        ref_cond_logps = ref_cond_logps.detach()
        ref_probs = tensor_by_label(ref_policy)
        theoretical = solve_nlhf_tie_norm(args.beta, wins, ties, theory_rho)
        if theoretical is not None:
            theory_rho = theoretical

        stage_log: list[dict] = []

        def log_stage_step(step: int, loss_value: float | None = None) -> None:
            model.eval()
            with torch.inference_mode():
                _sequence_logps, _log_policy, policy = compute_policy_state()
            model.train()
            row = {
                "step": step,
                "loss": loss_value,
                "probs": tensor_by_label(policy),
            }
            stage_log.append(row)
            prob_text = " ".join(f"{label}={row['probs'][label]:.4g}" for label in LABELS)
            if loss_value is None:
                print(f"{stage_name} step {step}: {prob_text}")
            else:
                print(f"{stage_name} step {step}: loss={loss_value:.6g} {prob_text}")

        print(
            f"stage={stage_name} start_ref="
            + json.dumps(ref_probs, sort_keys=True)
            + " theory="
            + json.dumps(None if theoretical is None else numpy_by_label(theoretical), sort_keys=True)
        )
        log_stage_step(0)
        for step in range(1, args.steps_per_stage + 1):
            _sequence_logps, log_policy, policy = compute_policy_state()
            loss = expected_ipo_loss(log_policy, policy, ref_cond_logps, support)
            optimizer.zero_grad(set_to_none=True)
            loss.backward()
            optimizer.step()
            if step % args.log_every == 0 or step == args.steps_per_stage:
                log_stage_step(step, float(loss.detach().cpu()))

        stage_records.append(
            {
                "stage": stage_name,
                "rankings": list(rankings),
                "wins": wins.tolist(),
                "ties": ties.tolist(),
                "normalized_support": cbar.tolist(),
                "stage_reference_probs": ref_probs,
                "theoretical_output": None if theoretical is None else numpy_by_label(theoretical),
                "training_log": stage_log,
            }
        )

    final_probs = stage_records[-1]["training_log"][-1]["probs"]
    run_tag = "__".join(
        [
            args.preset,
            args.order,
            f"beta{args.beta}",
            f"seed{args.seed}",
            safe_tag(args.tag) if args.tag else "",
        ]
    ).strip("_")
    run_dir = args.output_dir / run_tag
    run_dir.mkdir(parents=True, exist_ok=True)
    record = {
        "preset": args.preset,
        "prompt_id": preset.prompt_id,
        "block_name": preset.block_name,
        "order": args.order,
        "model": args.model,
        "renderer": args.renderer,
        "identity_mode": args.identity_mode,
        "device": str(device),
        "dtype": args.dtype,
        "fix_mistral_regex": args.fix_mistral_regex,
        "beta": args.beta,
        "target_gap": target_gap,
        "lr": args.lr,
        "steps_per_stage": args.steps_per_stage,
        "lora": {
            "r": args.lora_r,
            "alpha": args.lora_alpha,
            "dropout": args.lora_dropout,
            "target_modules": target_modules,
        },
        "completion_tokens": {
            label: encoded_by_label[label].completion_tokens for label in LABELS
        },
        "base_reference_logprobs": base_logps,
        "base_reference_probs": base_probs,
        "stages": stage_records,
        "final_probs": final_probs,
    }
    with (run_dir / "run.json").open("w") as handle:
        json.dump(record, handle, indent=2, sort_keys=True)
    if args.save_policy:
        model.save_pretrained(run_dir / "policy_lora")
        tokenizer.save_pretrained(run_dir / "policy_lora")
    print("final_probs=" + json.dumps(final_probs, sort_keys=True))
    print(f"wrote {run_dir / 'run.json'}")


if __name__ == "__main__":
    main()
