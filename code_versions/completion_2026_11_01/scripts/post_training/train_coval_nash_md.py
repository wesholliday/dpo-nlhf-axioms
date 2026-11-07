#!/usr/bin/env python3
"""Action-restricted Nash-MD/NLHF training on one CoVal profile.

This is deliberately not a target-fitting script. It does not train toward
`solve_nlhf_tie_norm(...)`. Instead, it adapts the training structure used by
TRL's NashMDTrainer to the fixed four-candidate CoVal setting:

* the policy distribution is the current model's normalized probability over
  the four fixed CoVal responses;
* the comparison distribution is the geometric mixture of the policy and
  reference distributions;
* the pairwise preference probability is the empirical CoVal normalized support
  cbar(x, y);
* the loss is the Nash-MD REINFORCE-style score loss plus a KL term.

The theoretical NLHF distribution is logged only for comparison.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from pathlib import Path
from typing import Sequence

import numpy as np
import torch
import torch.nn.functional as F

from scripts.post_training.nash_md_loss import finite_slate_nash_md_loss
from scripts.post_training.experiment_provenance import load_frozen_references, provenance
from peft import LoraConfig, get_peft_model
from transformers import AutoModelForCausalLM, AutoTokenizer

from scripts.theory.nlhf_tie_normalization import (
    load_cases_tie_norm,
    ranking_to_wins_and_ties,
    solve_nlhf_tie_norm,
)
from scripts.post_training.train_coval_dpo import (
    LABELS,
    compact_ranking,
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


def normalized_support_matrix(wins: np.ndarray, ties: np.ndarray) -> np.ndarray:
    totals = wins + wins.T + ties
    out = np.full_like(wins, 0.5, dtype=float)
    mask = totals > 0
    out[mask] = (wins[mask] + 0.5 * ties[mask]) / totals[mask]
    np.fill_diagonal(out, 0.5)
    return out


def load_profile(
    dataset: Path,
    prompt_id: str,
    block_name: str,
    delete_ranking: str | None,
    replace_ranking: Sequence[str] | None,
) -> tuple[tuple[str, ...], list[str], str | None, tuple[str, str] | None]:
    if delete_ranking and replace_ranking:
        raise ValueError("Use at most one of --delete-ranking and --replace-ranking")
    cases = [
        case
        for case in load_cases_tie_norm(dataset, [block_name])
        if case.prompt_id == prompt_id and case.block_name == block_name
    ]
    if len(cases) != 1:
        raise ValueError(f"Expected one case for {prompt_id}:{block_name}, found {len(cases)}")
    case = cases[0]
    rankings = list(case.rankings)
    deleted: str | None = None
    replaced: tuple[str, str] | None = None

    if delete_ranking is not None:
        want = compact_ranking(delete_ranking)
        for idx, ranking in enumerate(rankings):
            if compact_ranking(ranking) == want:
                deleted = rankings.pop(idx)
                break
        if deleted is None:
            raise ValueError(f"Ranking to delete not found: {delete_ranking}")

    if replace_ranking is not None:
        old, new = replace_ranking
        want = compact_ranking(old)
        for idx, ranking in enumerate(rankings):
            if compact_ranking(ranking) == want:
                rankings[idx] = new
                replaced = (ranking, new)
                break
        if replaced is None:
            raise ValueError(f"Ranking to replace not found: {old}")

    return case.response_indices, rankings, deleted, replaced


def profile_matrices(rankings: Sequence[str], labels: Sequence[str]) -> tuple[np.ndarray, np.ndarray]:
    index = {label: idx for idx, label in enumerate(labels)}
    wins = np.zeros((len(labels), len(labels)), dtype=float)
    ties = np.zeros_like(wins)
    for ranking in rankings:
        ranking_wins, ranking_ties = ranking_to_wins_and_ties(ranking, index)
        wins += ranking_wins
        ties += ranking_ties
    return wins, ties


def probs_from_logps(logps: dict[str, float]) -> dict[str, float]:
    norm = logsumexp(logps.values())
    return {label: math.exp(logps[label] - norm) for label in LABELS}


def tensor_probs_by_label(values: torch.Tensor) -> dict[str, float]:
    return {label: float(values[idx].detach().cpu()) for idx, label in enumerate(LABELS)}


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog=(
            "Paper Nash-MD runs use dtype=float32, mixture_coef=0, "
            "weight_decay=0, lora_dropout=0, lr=3e-6, and 300 steps."
        ),
    )
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--prompt-id", required=True)
    parser.add_argument("--block-name", choices=("world", "personal"), default="world")
    parser.add_argument("--delete-ranking", default=None)
    parser.add_argument("--replace-ranking", nargs=2, metavar=("OLD", "NEW"), default=None)
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
    parser.add_argument("--model-revision", default=None)
    parser.add_argument("--reference-cache", type=Path, default=None)
    parser.add_argument("--renderer", choices=("qwen", "llama2"), default="qwen")
    parser.add_argument("--identity-mode", choices=("exact", "strip_identity", "neutralize_identity"), default="strip_identity")
    parser.add_argument("--device", choices=("cpu", "mps", "cuda"), default="mps")
    parser.add_argument("--dtype", choices=("float16", "bfloat16", "float32"), default="float32")
    parser.add_argument("--tau", type=float, default=0.01)
    parser.add_argument(
        "--mixture-coef",
        type=float,
        default=0.0,
        help="Mixture coefficient for the opponent distribution. The paper's Nash-MD runs use 0.",
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=300,
        help="Number of optimizer steps. The paper's Nash-MD runs use 300.",
    )
    parser.add_argument("--lr", type=float, default=3e-6)
    parser.add_argument(
        "--exploration-epsilon",
        type=float,
        default=0.0,
        help=(
            "Must be zero. Finite-slate expectations are summed exactly; "
            "the historical uniform floor changed the gradient."
        ),
    )
    parser.add_argument(
        "--exploration-decay-steps",
        type=int,
        default=0,
        help=(
            "Linearly decay --exploration-epsilon to zero over this many "
            "training steps. A value of 0 keeps the exploration floor constant."
        ),
    )
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-length", type=int, default=4096)
    parser.add_argument("--log-every", type=int, default=10)
    parser.add_argument(
        "--grad-clip",
        type=float,
        default=None,
        help="Clip LoRA gradient norm before each optimizer step.",
    )
    parser.add_argument(
        "--weight-decay",
        type=float,
        default=0.0,
        help=(
            "AdamW weight decay. The paper's Nash-MD runs use 0.0."
        ),
    )
    parser.add_argument("--lora-r", type=int, default=8)
    parser.add_argument("--lora-alpha", type=int, default=32)
    parser.add_argument("--lora-dropout", type=float, default=0.0)
    parser.add_argument("--target-modules", default="q_proj,v_proj")
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/nash_md_coval_runs"))
    parser.add_argument("--tag", default=None)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--save-policy", action="store_true")
    parser.add_argument(
        "--fix-mistral-regex",
        action="store_true",
        help="Pass fix_mistral_regex=True when loading Mistral-family tokenizers.",
    )
    args = parser.parse_args()

    if not 0.0 <= args.mixture_coef <= 1.0:
        raise ValueError("--mixture-coef must be in [0, 1]")
    if not 0.0 <= args.exploration_epsilon < 1.0:
        raise ValueError("--exploration-epsilon must be in [0, 1)")
    if args.exploration_decay_steps < 0:
        raise ValueError("--exploration-decay-steps must be nonnegative")
    if args.weight_decay < 0:
        raise ValueError("--weight-decay must be nonnegative")
    random.seed(args.seed)
    np.random.seed(args.seed)
    torch.manual_seed(args.seed)

    device = choose_device(args.device)
    dtype = dtype_from_name(args.dtype)
    labels, rankings, deleted, replaced = load_profile(
        args.dataset,
        args.prompt_id,
        args.block_name,
        args.delete_ranking,
        args.replace_ranking,
    )
    if tuple(labels) != LABELS:
        raise ValueError(f"This script expects labels A/B/C/D, found {labels}")
    wins, ties = profile_matrices(rankings, labels)
    cbar = normalized_support_matrix(wins, ties)

    print(
        f"profile={args.prompt_id}:{args.block_name} voters={len(rankings)} "
        f"deleted={deleted} replaced={replaced}"
    )
    print("normalized_support=" + json.dumps(cbar.tolist()))
    if args.dry_run:
        return

    prompt_case = load_prompt_case(args.dataset, args.prompt_id, args.identity_mode)
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
        ref_logps_tensor = sequence_logprobs(
            model, encoded_items, tokenizer.pad_token_id, device
        ).detach().float()
    ref_logps = {label: float(ref_logps_tensor[idx].cpu()) for idx, label in enumerate(LABELS)}
    ref_probs = probs_from_logps(ref_logps)
    initial_model_probs = ref_probs.copy()
    if args.reference_cache is not None:
        fixed = load_frozen_references(args.reference_cache, LABELS)[args.prompt_id]
        ref_logps = {label: float(fixed['response_logprobs'][label]) for label in LABELS}
        ref_logps_tensor = torch.tensor([ref_logps[x] for x in LABELS], dtype=torch.float32, device=device)
        ref_probs = {label: float(fixed['rho'][label]) for label in LABELS}
    ref_cond_logps = F.log_softmax(ref_logps_tensor, dim=0).detach().to(device)
    rho = np.asarray([ref_probs[label] for label in LABELS], dtype=float)
    theoretical = solve_nlhf_tie_norm(args.tau, wins, ties, rho)
    if theoretical is None:
        raise RuntimeError('NLHF target failed; refusing to train without a checked prediction')
    print("reference_probs=" + json.dumps(ref_probs, sort_keys=True))
    print("theoretical_nlhf=" + json.dumps(
        None if theoretical is None else {label: float(theoretical[idx]) for idx, label in enumerate(LABELS)},
        sort_keys=True,
    ))

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
    trainable_parameters = [parameter for parameter in model.parameters() if parameter.requires_grad]
    optimizer = torch.optim.AdamW(trainable_parameters, lr=args.lr, weight_decay=args.weight_decay)

    preference_probs = torch.tensor(cbar, dtype=torch.float32, device=device)
    log_rows: list[dict] = []

    def compute_policy_state() -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        sequence_logps = sequence_logprobs(model, encoded_items, tokenizer.pad_token_id, device).float()
        log_policy = F.log_softmax(sequence_logps, dim=0)
        policy = log_policy.exp()
        return sequence_logps, log_policy, policy

    def log_step(step: int, loss_value: float | None = None) -> None:
        model.eval()
        with torch.inference_mode():
            sequence_logps, log_policy, policy = compute_policy_state()
            mixture_logits = args.mixture_coef * ref_cond_logps + (1.0 - args.mixture_coef) * log_policy
            mixture = F.softmax(mixture_logits, dim=0)
            expected_advantage = (preference_probs - 0.5).matmul(mixture)
            kl = torch.sum(policy * (log_policy - ref_cond_logps))
        model.train()
        row = {
            "step": step,
            "loss": loss_value,
            "sequence_logprobs": tensor_probs_by_label(sequence_logps),
            "log_probs": tensor_probs_by_label(log_policy),
            "probs": tensor_probs_by_label(policy),
            "mixture_probs": tensor_probs_by_label(mixture),
            "expected_advantage": tensor_probs_by_label(expected_advantage),
            "conditional_kl_to_reference": float(kl.detach().cpu()),
        }
        log_rows.append(row)
        prob_text = " ".join(f"{label}={row['probs'][label]:.4g}" for label in LABELS)
        if loss_value is None:
            print(f"step {step}: {prob_text}")
        else:
            print(f"step {step}: loss={loss_value:.6g} {prob_text}")

    log_step(0)
    for step in range(1, args.steps + 1):
        _sequence_logps, log_policy, policy = compute_policy_state()
        if args.exploration_decay_steps > 0:
            effective_exploration_epsilon = args.exploration_epsilon * max(
                0.0,
                1.0 - ((step - 1) / args.exploration_decay_steps),
            )
        else:
            effective_exploration_epsilon = args.exploration_epsilon
        loss = finite_slate_nash_md_loss(
            log_policy, ref_cond_logps, preference_probs, args.tau,
            args.mixture_coef, effective_exploration_epsilon,
        )
        if not bool(torch.isfinite(loss).detach().cpu()):
            raise FloatingPointError(f"non-finite Nash-MD loss at step {step}: {float(loss.detach().cpu())}")

        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        if args.grad_clip is not None:
            grad_norm = torch.nn.utils.clip_grad_norm_(trainable_parameters, args.grad_clip)
            if not bool(torch.isfinite(grad_norm).detach().cpu()):
                raise FloatingPointError(
                    f"non-finite Nash-MD gradient norm at step {step}: {float(grad_norm.detach().cpu())}"
                )
        optimizer.step()

        if step % args.log_every == 0 or step == args.steps:
            log_step(step, float(loss.detach().cpu()))

    tag_bits = [
        args.prompt_id,
        args.block_name,
        "minus_" + safe_tag(compact_ranking(args.delete_ranking)) if args.delete_ranking else "full",
        f"tau{args.tau}",
        f"mix{args.mixture_coef}",
        f"seed{args.seed}",
    ]
    if replaced is not None:
        tag_bits[2] = "replace_" + safe_tag(compact_ranking(replaced[0])) + "_to_" + safe_tag(compact_ranking(replaced[1]))
    if args.tag:
        tag_bits.append(safe_tag(args.tag))
    run_tag = "__".join(tag_bits).replace("/", "_")
    run_dir = args.output_dir / run_tag
    run_dir.mkdir(parents=True, exist_ok=True)
    record = {
        "prompt_id": args.prompt_id,
        "block_name": args.block_name,
        "deleted_ranking": deleted,
        "replaced_ranking": replaced,
        "rankings": rankings,
        "wins": wins.tolist(),
        "ties": ties.tolist(),
        "normalized_support": cbar.tolist(),
        "model": args.model,
        "provenance": provenance(args.dataset, args.reference_cache, None, args.model_revision),
        "initial_model_probs": initial_model_probs,
        "renderer": args.renderer,
        "identity_mode": args.identity_mode,
        "device": str(device),
        "dtype": args.dtype,
        "fix_mistral_regex": args.fix_mistral_regex,
        "tau": args.tau,
        "mixture_coef": args.mixture_coef,
        "exploration_epsilon": args.exploration_epsilon,
        "exploration_decay_steps": args.exploration_decay_steps,
        "grad_clip": args.grad_clip,
        "weight_decay": args.weight_decay,
        "lr": args.lr,
        "steps": args.steps,
        "lora": {
            "r": args.lora_r,
            "alpha": args.lora_alpha,
            "dropout": args.lora_dropout,
            "target_modules": target_modules,
        },
        "completion_tokens": {
            label: encoded_by_label[label].completion_tokens for label in LABELS
        },
        "reference_logprobs": ref_logps,
        "reference_probs": ref_probs,
        "theoretical_nlhf": None
        if theoretical is None
        else {label: float(theoretical[idx]) for idx, label in enumerate(LABELS)},
        "training_log": log_rows,
    }
    with (run_dir / "run.json").open("w") as handle:
        json.dump(record, handle, indent=2, sort_keys=True, allow_nan=False)
    if args.save_policy:
        model.save_pretrained(run_dir / "policy_lora")
        tokenizer.save_pretrained(run_dir / "policy_lora")
    print(f"wrote {run_dir / 'run.json'}")


if __name__ == "__main__":
    main()
