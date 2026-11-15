#!/usr/bin/env python3
"""Run batch_profile_empirical_vs_theory.py in restartable chunks.

The in-process MPS runner is much faster than one-subprocess-per-profile, but
it can slow down sharply if left alive for too many profiles. This supervisor
restarts it after a small number of new cases while preserving the resumable
JSONL outputs.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path

from scripts.theory.nlhf_tie_normalization import load_cases_tie_norm
from scripts.post_training.train_coval_dpo import safe_tag


def parse_csv(text: str) -> list[str]:
    return [part.strip() for part in text.split(",") if part.strip()]


def read_seen_keys(path: Path) -> set[str]:
    seen: set[str] = set()
    if not path.exists():
        return seen
    with path.open() as handle:
        for line in handle:
            if line.strip():
                seen.add(json.loads(line)["case_key"])
    return seen


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


def write_status(path: Path, status: dict) -> None:
    with path.open("w") as handle:
        json.dump(status, handle, indent=2, sort_keys=True)


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
    parser.add_argument("--rule", choices=("nlhf", "dpo"), required=True)
    parser.add_argument("--python", default=".venv_mps/bin/python")
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
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
        help="Diagnostic exploration floor passed to NLHF/Nash-MD batch runs.",
    )
    parser.add_argument(
        "--nlhf-exploration-decay-steps",
        type=int,
        default=0,
        help=(
            "Linearly decay --nlhf-exploration-epsilon to zero over this many "
            "NLHF steps in the batch runner. A value of 0 keeps it constant."
        ),
    )
    parser.add_argument(
        "--nlhf-mixture-coef",
        type=float,
        default=0.0,
        help="Mixture coefficient passed to NLHF/Nash-MD batch runs.",
    )
    parser.add_argument("--seed", type=int, default=0)
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
        "--dpo-log-every",
        type=int,
        default=0,
        help="If positive, pass DPO step training-step logging through to the batch runner.",
    )
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
            "AdamW weight decay passed to the batch runner. Paper Nash-MD runs use 0.0."
        ),
    )
    parser.add_argument("--max-cases", type=int, default=None)
    parser.add_argument("--case-keys-file", type=Path, default=None)
    parser.add_argument("--chunk-new-cases", type=int, default=5)
    parser.add_argument("--sleep-seconds", type=float, default=2.0)
    parser.add_argument("--output-root", type=Path, default=Path("results/intermediate/empirical_vs_theory_all_profiles_chunked"))
    parser.add_argument("--tag", default="chunked")
    parser.add_argument("--fix-mistral-regex", action="store_true")
    args = parser.parse_args()

    if args.nlhf_exploration_decay_steps < 0:
        raise ValueError("--nlhf-exploration-decay-steps must be nonnegative")
    if args.weight_decay < 0:
        raise ValueError("--weight-decay must be nonnegative")

    blocks = parse_csv(args.blocks)
    cases = load_cases_tie_norm(args.dataset, blocks)
    if args.max_cases is not None:
        cases = cases[: args.max_cases]
    allowed_case_keys = read_case_key_filter(args.case_keys_file)
    if allowed_case_keys is not None:
        cases = [case for case in cases if f"{case.prompt_id}:{case.block_name}" in allowed_case_keys]
    total_cases = len(cases)

    run_name = (
        f"{args.rule}__blocks-{safe_tag('-'.join(blocks))}__"
        f"steps{args.steps}__lr{args.lr}__tau{args.tau}__beta{args.beta}__"
        f"{safe_tag(args.tag)}"
    )
    rule_dir = args.output_root / safe_tag(Path(args.model).name) / args.rule
    rule_dir.mkdir(parents=True, exist_ok=True)
    results_path = rule_dir / f"{run_name}.jsonl"
    status_path = rule_dir / f"{run_name}.status.json"
    meta_path = rule_dir / f"{run_name}.meta.json"

    with meta_path.open("w") as handle:
        json.dump(
            {
                "rule": args.rule,
                "model": args.model,
                "renderer": args.renderer,
                "identity_mode": args.identity_mode,
                "device": args.device,
                "dtype": args.dtype,
                "tau": args.tau,
                "beta": args.beta,
                "lr": args.lr,
                "steps": args.steps,
                "nlhf_exploration_epsilon": args.nlhf_exploration_epsilon,
                "nlhf_exploration_decay_steps": args.nlhf_exploration_decay_steps,
                "nlhf_mixture_coef": args.nlhf_mixture_coef,
                "seed": args.seed,
                "blocks": blocks,
                "chunk_new_cases": args.chunk_new_cases,
                "grad_clip": args.grad_clip,
                "weight_decay": args.weight_decay,
                "dpo_log_every": args.dpo_log_every,
                "output_root": str(args.output_root),
                "results_path": str(results_path),
                "python": args.python,
                "case_keys_file": None if args.case_keys_file is None else str(args.case_keys_file),
            },
            handle,
            indent=2,
            sort_keys=True,
        )

    started = time.perf_counter()
    chunk_index = 0
    while True:
        seen = read_seen_keys(results_path)
        completed = len(seen)
        if completed >= total_cases:
            write_status(
                status_path,
                {
                    "rule": args.rule,
                    "completed": completed,
                    "total_cases": total_cases,
                    "chunk_index": chunk_index,
                    "elapsed_seconds": time.perf_counter() - started,
                    "results_path": str(results_path),
                    "done": True,
                },
            )
            print(f"[{args.rule}] all done {completed}/{total_cases}")
            break

        chunk_index += 1
        write_status(
            status_path,
            {
                "rule": args.rule,
                "completed": completed,
                "total_cases": total_cases,
                "chunk_index": chunk_index,
                "elapsed_seconds": time.perf_counter() - started,
                "results_path": str(results_path),
                "done": False,
            },
        )
        print(
            f"[{args.rule}] starting chunk {chunk_index} at "
            f"{completed}/{total_cases} with max_new_cases={args.chunk_new_cases}"
        )

        cmd = [
            args.python,
            "-m",
            "scripts.post_training.batch_profile_empirical_vs_theory",
            "--dataset",
            str(args.dataset),
            "--blocks",
            args.blocks,
            "--rules",
            args.rule,
            "--model",
            args.model,
            "--renderer",
            args.renderer,
            "--identity-mode",
            args.identity_mode,
            "--device",
            args.device,
            "--dtype",
            args.dtype,
            "--tau",
            str(args.tau),
            "--beta",
            str(args.beta),
            "--lr",
            str(args.lr),
            "--steps",
            str(args.steps),
            "--nlhf-exploration-epsilon",
            str(args.nlhf_exploration_epsilon),
            "--nlhf-exploration-decay-steps",
            str(args.nlhf_exploration_decay_steps),
            "--nlhf-mixture-coef",
            str(args.nlhf_mixture_coef),
            "--seed",
            str(args.seed),
            "--max-length",
            str(args.max_length),
            "--lora-r",
            str(args.lora_r),
            "--lora-alpha",
            str(args.lora_alpha),
            "--lora-dropout",
            str(args.lora_dropout),
            "--target-modules",
            args.target_modules,
            "--weight-decay",
            str(args.weight_decay),
            "--max-new-cases",
            str(args.chunk_new_cases),
            "--output-root",
            str(args.output_root),
            "--tag",
            args.tag,
        ]
        if args.max_cases is not None:
            cmd.extend(["--max-cases", str(args.max_cases)])
        if args.case_keys_file is not None:
            cmd.extend(["--case-keys-file", str(args.case_keys_file)])
        if args.fix_mistral_regex:
            cmd.append("--fix-mistral-regex")
        if args.grad_clip is not None:
            cmd.extend(["--grad-clip", str(args.grad_clip)])
        if args.rule == "dpo":
            if args.dpo_log_every > 0:
                cmd.extend(["--dpo-log-every", str(args.dpo_log_every)])
            if args.dpo_full_batch:
                cmd.append("--dpo-full-batch")
            else:
                cmd.extend(["--dpo-batch-size", str(args.dpo_batch_size)])

        subprocess.run(cmd, check=True)
        time.sleep(args.sleep_seconds)


if __name__ == "__main__":
    main()
