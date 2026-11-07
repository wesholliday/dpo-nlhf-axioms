#!/usr/bin/env python3
"""Sequential action-restricted Nash-MD checks for NLHF commutativity.

It tests whether actual sequential Nash-MD-style training depends on the order
in which two CoVal subprofiles are presented:

    train on R1 then R2  vs.  train on R2 then R1.

For each stage, the stage reference distribution is frozen as the current
model-induced distribution over the four candidate responses at the beginning
of that stage.
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

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
    render_full,
    render_prefix,
    safe_tag,
    sequence_logprobs,
    choose_device,
)
from scripts.post_training.train_coval_nash_md import normalized_support_matrix, profile_matrices, probs_from_logps
from scripts.post_training.commutativity_presets import (
    CommutativityPreset,
    PRESETS,
    numpy_by_label,
    tensor_by_label,
)


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog=(
            "Paper Nash-MD commutativity checks use dtype=float32, mixture_coef=0, "
            "weight_decay=0, lora_dropout=0, lr=3e-6, and 300 steps per stage."
        ),
    )
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--preset", choices=sorted(PRESETS), default="nemo_9066")
    parser.add_argument(
        "--prompt-id",
        default=None,
        help="Override --preset with a prompt id for an arbitrary commutativity witness.",
    )
    parser.add_argument(
        "--block-name",
        default=None,
        help="Override --preset with the CoVal block name for an arbitrary witness.",
    )
    parser.add_argument(
        "--rankings-left-json",
        default=None,
        help="JSON list of rankings for R1; requires --prompt-id and --block-name.",
    )
    parser.add_argument(
        "--rankings-right-json",
        default=None,
        help="JSON list of rankings for R2; requires --prompt-id and --block-name.",
    )
    parser.add_argument("--order", choices=("12", "21"), default="12")
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
    parser.add_argument("--renderer", choices=("qwen", "llama2"), default="qwen")
    parser.add_argument("--identity-mode", choices=("exact", "strip_identity", "neutralize_identity"), default="strip_identity")
    parser.add_argument("--device", choices=("cpu", "mps", "cuda"), default="mps")
    parser.add_argument("--dtype", choices=("float16", "bfloat16", "float32"), default="float32")
    parser.add_argument("--tau", type=float, default=0.01)
    parser.add_argument(
        "--mixture-coef",
        type=float,
        default=0.0,
        help="Mixture coefficient for the opponent distribution. The paper's checks use 0.",
    )
    parser.add_argument(
        "--exploration-epsilon",
        type=float,
        default=0.0,
        help=(
            "Diagnostic score-function exploration floor. If positive, replace "
            "policy sample weights by (1-eps)*policy + eps*uniform."
        ),
    )
    parser.add_argument(
        "--exploration-decay-steps",
        type=int,
        default=0,
        help=(
            "Linearly decay --exploration-epsilon to zero over this many "
            "training steps in each stage. A value of 0 keeps it constant."
        ),
    )
    parser.add_argument("--steps-per-stage", type=int, default=300)
    parser.add_argument("--lr", type=float, default=3e-6)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-length", type=int, default=4096)
    parser.add_argument("--log-every", type=int, default=50)
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
            "AdamW weight decay. The paper's Nash-MD commutativity checks use 0.0."
        ),
    )
    parser.add_argument("--lora-r", type=int, default=8)
    parser.add_argument("--lora-alpha", type=int, default=32)
    parser.add_argument("--lora-dropout", type=float, default=0.0)
    parser.add_argument("--target-modules", default="q_proj,v_proj")
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/nash_md_commutativity_runs"))
    parser.add_argument("--tag", default=None)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--save-policy", action="store_true")
    parser.add_argument(
        "--fix-mistral-regex",
        action="store_true",
        help="Pass fix_mistral_regex=True when loading Mistral-family tokenizers.",
    )
    args = parser.parse_args()

    if args.tau <= 0:
        raise ValueError("--tau must be positive")
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

    if args.rankings_left_json is not None or args.rankings_right_json is not None:
        if not (args.prompt_id and args.block_name and args.rankings_left_json and args.rankings_right_json):
            raise ValueError(
                "Arbitrary witnesses require --prompt-id, --block-name, "
                "--rankings-left-json, and --rankings-right-json"
            )
        preset = CommutativityPreset(
            prompt_id=args.prompt_id,
            block_name=args.block_name,
            r1=tuple(json.loads(args.rankings_left_json)),
            r2=tuple(json.loads(args.rankings_right_json)),
        )
        preset_name = f"{safe_tag(args.prompt_id)}__{safe_tag(args.block_name)}"
    else:
        preset = PRESETS[args.preset]
        preset_name = args.preset
    stage_specs = [("R1", preset.r1), ("R2", preset.r2)]
    if args.order == "21":
        stage_specs = list(reversed(stage_specs))

    print(
        f"preset={preset_name} prompt={preset.prompt_id}:{preset.block_name} "
        f"order={args.order} mixture={args.mixture_coef}"
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
    trainable_parameters = [parameter for parameter in model.parameters() if parameter.requires_grad]
    optimizer = torch.optim.AdamW(trainable_parameters, lr=args.lr, weight_decay=args.weight_decay)
    uniform_weights = torch.full((len(LABELS),), 1.0 / len(LABELS), dtype=torch.float32, device=device)

    stage_records: list[dict] = []
    theory_rho = np.asarray([base_probs[label] for label in LABELS], dtype=float)

    def compute_policy_state() -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        sequence_logps = sequence_logprobs(model, encoded_items, tokenizer.pad_token_id, device).float()
        log_policy = F.log_softmax(sequence_logps, dim=0)
        policy = log_policy.exp()
        return sequence_logps, log_policy, policy

    for stage_name, rankings in stage_specs:
        wins, ties = profile_matrices(rankings, LABELS)
        cbar = normalized_support_matrix(wins, ties)
        preference_probs = torch.tensor(cbar, dtype=torch.float32, device=device)

        model.eval()
        with torch.inference_mode():
            _ref_sequence_logps, ref_cond_logps, ref_policy = compute_policy_state()
        model.train()
        ref_cond_logps = ref_cond_logps.detach()
        ref_probs = tensor_by_label(ref_policy)

        theoretical = solve_nlhf_tie_norm(args.tau, wins, ties, theory_rho)
        if theoretical is not None:
            theory_rho = theoretical

        stage_log: list[dict] = []

        def log_stage_step(step: int, loss_value: float | None = None) -> None:
            model.eval()
            with torch.inference_mode():
                _sequence_logps, log_policy, policy = compute_policy_state()
                mixture_logits = args.mixture_coef * ref_cond_logps + (1.0 - args.mixture_coef) * log_policy
                mixture = F.softmax(mixture_logits, dim=0)
                expected_advantage = (preference_probs - 0.5).matmul(mixture)
                kl = torch.sum(policy * (log_policy - ref_cond_logps))
            model.train()
            row = {
                "step": step,
                "loss": loss_value,
                "probs": tensor_by_label(policy),
                "mixture_probs": tensor_by_label(mixture),
                "expected_advantage": tensor_by_label(expected_advantage),
                "conditional_kl_to_stage_reference": float(kl.detach().cpu()),
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
            if args.exploration_decay_steps > 0:
                effective_exploration_epsilon = args.exploration_epsilon * max(
                    0.0,
                    1.0 - ((step - 1) / args.exploration_decay_steps),
                )
            else:
                effective_exploration_epsilon = args.exploration_epsilon
            with torch.no_grad():
                mixture_logits = args.mixture_coef * ref_cond_logps + (1.0 - args.mixture_coef) * log_policy.detach()
                mixture = F.softmax(mixture_logits, dim=0)
                expected_advantage = (preference_probs - 0.5).matmul(mixture)
                log_ratio = log_policy.detach() - ref_cond_logps
                sample_weights = (
                    (1.0 - effective_exploration_epsilon) * policy.detach()
                    + effective_exploration_epsilon * uniform_weights
                )
                coefficient = args.tau * log_ratio - expected_advantage
            loss = torch.sum(sample_weights * coefficient * log_policy)
            if not bool(torch.isfinite(loss).detach().cpu()):
                raise FloatingPointError(
                    f"non-finite Nash-MD commutativity loss in {stage_name} at step {step}: {float(loss.detach().cpu())}"
                )

            optimizer.zero_grad(set_to_none=True)
            loss.backward()
            if args.grad_clip is not None:
                grad_norm = torch.nn.utils.clip_grad_norm_(trainable_parameters, args.grad_clip)
                if not bool(torch.isfinite(grad_norm).detach().cpu()):
                    raise FloatingPointError(
                        f"non-finite Nash-MD commutativity gradient norm in {stage_name} at step {step}: {float(grad_norm.detach().cpu())}"
                    )
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
    run_tag_bits = [
        preset_name,
        args.order,
        f"tau{args.tau}",
        f"mix{args.mixture_coef}",
        f"seed{args.seed}",
    ]
    if args.tag:
        run_tag_bits.append(safe_tag(args.tag))
    run_tag = "__".join(run_tag_bits).replace("/", "_")
    run_dir = args.output_dir / run_tag
    run_dir.mkdir(parents=True, exist_ok=True)
    record = {
        "prompt_id": preset.prompt_id,
        "block_name": preset.block_name,
        "preset": args.preset,
        "order": args.order,
        "model": args.model,
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
    print(f"wrote {run_dir / 'run.json'}")


if __name__ == "__main__":
    main()
