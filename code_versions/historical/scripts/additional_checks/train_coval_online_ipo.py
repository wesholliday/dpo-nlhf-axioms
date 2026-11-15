#!/usr/bin/env python3
"""Action-restricted Online-IPO training on one CoVal profile.

This script adapts TRL's OnlineDPOTrainer with ``loss_type="ipo"`` to the
fixed four-candidate CoVal setting. It is not target fitting: the closed-form
tie-normalized NLHF distribution is logged only as a comparator.

At each step we compute the current model-induced distribution over A/B/C/D.
Instead of sampling two completions, we take the exact expectation over ordered
pairs drawn from that current distribution. For an ordered pair (x, y), the
empirical CoVal support cbar(x, y) is the probability that x is chosen over y.
The pair loss is TRL's IPO loss:

    ((log pi_theta(x)/pi_ref(x) - log pi_theta(y)/pi_ref(y)) - 1/(2 beta))^2

for the chosen direction, averaged over both possible pairwise outcomes.
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


def tensor_by_label(values: torch.Tensor) -> dict[str, float]:
    return {label: float(values[idx].detach().cpu()) for idx, label in enumerate(LABELS)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--prompt-id", required=True)
    parser.add_argument("--block-name", choices=("world", "personal"), default="world")
    parser.add_argument("--delete-ranking", default=None)
    parser.add_argument("--replace-ranking", nargs=2, metavar=("OLD", "NEW"), default=None)
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
    parser.add_argument("--renderer", choices=("qwen", "llama2"), default="qwen")
    parser.add_argument("--identity-mode", choices=("exact", "strip_identity", "neutralize_identity"), default="strip_identity")
    parser.add_argument("--device", choices=("cpu", "mps", "cuda"), default="mps")
    parser.add_argument("--dtype", choices=("float16", "bfloat16", "float32"), default="float16")
    parser.add_argument("--beta", type=float, default=0.01)
    parser.add_argument("--theory-tau", type=float, default=None)
    parser.add_argument("--steps", type=int, default=200)
    parser.add_argument("--lr", type=float, default=5e-7)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-length", type=int, default=4096)
    parser.add_argument("--log-every", type=int, default=10)
    parser.add_argument("--lora-r", type=int, default=8)
    parser.add_argument("--lora-alpha", type=int, default=32)
    parser.add_argument("--lora-dropout", type=float, default=0.05)
    parser.add_argument("--target-modules", default="q_proj,v_proj")
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/online_ipo_coval_runs"))
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
    theory_tau = args.beta if args.theory_tau is None else args.theory_tau

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
    ref_cond_logps = F.log_softmax(ref_logps_tensor, dim=0).detach().to(device)
    rho = np.asarray([ref_probs[label] for label in LABELS], dtype=float)
    theoretical = solve_nlhf_tie_norm(theory_tau, wins, ties, rho)
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
    optimizer = torch.optim.AdamW(
        [parameter for parameter in model.parameters() if parameter.requires_grad],
        lr=args.lr,
    )

    support = torch.tensor(cbar, dtype=torch.float32, device=device)
    target_gap = 1.0 / (2.0 * args.beta)
    label_indices = torch.arange(len(LABELS), device=device)
    log_rows: list[dict] = []

    def compute_policy_state() -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        sequence_logps = sequence_logprobs(model, encoded_items, tokenizer.pad_token_id, device).float()
        log_policy = F.log_softmax(sequence_logps, dim=0)
        policy = log_policy.exp()
        return sequence_logps, log_policy, policy

    def expected_ipo_loss(log_policy: torch.Tensor, policy: torch.Tensor) -> torch.Tensor:
        log_ratio = log_policy - ref_cond_logps
        pair_logit = log_ratio[:, None] - log_ratio[None, :]
        chosen_x_loss = (pair_logit - target_gap) ** 2
        chosen_y_loss = (-pair_logit - target_gap) ** 2
        expected_pair_loss = support * chosen_x_loss + (1.0 - support) * chosen_y_loss
        pair_weights = policy.detach()[:, None] * policy.detach()[None, :]
        return torch.sum(pair_weights * expected_pair_loss)

    def log_step(step: int, loss_value: float | None = None) -> None:
        model.eval()
        with torch.inference_mode():
            _sequence_logps, log_policy, policy = compute_policy_state()
            log_ratio = log_policy - ref_cond_logps
            pair_logit = log_ratio[:, None] - log_ratio[None, :]
            expected_loss_by_first = torch.sum(
                policy[None, :] * (
                    support * (pair_logit - target_gap) ** 2
                    + (1.0 - support) * (-pair_logit - target_gap) ** 2
                ),
                dim=1,
            )
        model.train()
        row = {
            "step": step,
            "loss": loss_value,
            "probs": tensor_by_label(policy),
            "log_ratios": tensor_by_label(log_ratio),
            "expected_loss_by_first_candidate": tensor_by_label(expected_loss_by_first),
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
        loss = expected_ipo_loss(log_policy, policy)

        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        optimizer.step()

        if step % args.log_every == 0 or step == args.steps:
            log_step(step, float(loss.detach().cpu()))

    tag_bits = [
        args.prompt_id,
        args.block_name,
        "minus_" + safe_tag(compact_ranking(args.delete_ranking)) if args.delete_ranking else "full",
        f"beta{args.beta}",
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
        "renderer": args.renderer,
        "identity_mode": args.identity_mode,
        "device": str(device),
        "dtype": args.dtype,
        "fix_mistral_regex": args.fix_mistral_regex,
        "beta": args.beta,
        "theory_tau": theory_tau,
        "target_gap": target_gap,
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
        json.dump(record, handle, indent=2, sort_keys=True)
    if args.save_policy:
        model.save_pretrained(run_dir / "policy_lora")
        tokenizer.save_pretrained(run_dir / "policy_lora")
    print(f"wrote {run_dir / 'run.json'}")


if __name__ == "__main__":
    main()
