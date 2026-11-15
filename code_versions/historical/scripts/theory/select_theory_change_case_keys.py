#!/usr/bin/env python3
"""Select profile case keys whose theory predicts a nontrivial change from rho."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import numpy as np

from scripts.theory.nlhf_tie_normalization import load_cases_tie_norm, solve_nlhf_tie_norm
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases as load_rtbt_cases
from scripts.theory.search_model_reference_violation_counts import rho_for_case as rtbt_rho_for_case
from scripts.theory.search_new_nlhf_tie_normalization_examples import ReferenceConfig, load_rho_cache, rho_for_case
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda


def tv_distance(p: np.ndarray, q: np.ndarray) -> float:
    return 0.5 * float(np.sum(np.abs(p - q)))


def jsonable_probs(labels: list[str], values: np.ndarray) -> dict[str, float]:
    return {label: float(values[i]) for i, label in enumerate(labels)}


def case_key(case) -> str:
    return f"{case.prompt_id}:{case.block_name}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--blocks", default="world,personal")
    parser.add_argument("--rule", choices=("nlhf", "rtbt"), required=True)
    parser.add_argument("--rho-cache", type=Path, required=True)
    parser.add_argument("--tau", type=float, default=0.01)
    parser.add_argument("--beta", type=float, default=0.1)
    parser.add_argument("--tv-threshold", type=float, default=0.01)
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/theory_change_case_selection"))
    parser.add_argument("--tag", default="selection")
    args = parser.parse_args()

    blocks = [part.strip() for part in args.blocks.split(",") if part.strip()]
    if args.rule == "nlhf":
        cases = load_cases_tie_norm(args.dataset, blocks)
    else:
        cases = load_rtbt_cases(args.dataset, blocks)

    rho_cache = load_rho_cache(args.rho_cache)
    ref = ReferenceConfig("selection", args.rho_cache)

    output_dir = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)
    stem = f"{args.rule}__tvgeq_{args.tv_threshold}__{args.tag}"
    csv_path = output_dir / f"{stem}.csv"
    keys_path = output_dir / f"{stem}.case_keys.txt"
    meta_path = output_dir / f"{stem}.meta.json"

    rows: list[dict] = []
    for case in cases:
        try:
            if args.rule == "nlhf":
                rho, _ = rho_for_case(case, ref, rho_cache)
                theory = solve_nlhf_tie_norm(
                    args.tau,
                    np.asarray(case.total_wins, dtype=float),
                    np.asarray(case.total_ties, dtype=float),
                    rho,
                )
            else:
                record = rho_cache.get(case.prompt_id)
                if record is None:
                    continue
                rho = rtbt_rho_for_case(case, record)
                theory = solve_weighted_logistic_borda(
                    args.beta,
                    np.asarray(case.total_wins, dtype=float),
                    rho,
                )
        except KeyError:
            continue

        if theory is None:
            continue
        tv = tv_distance(theory, rho)
        if tv < args.tv_threshold:
            continue
        rows.append(
            {
                "case_key": case_key(case),
                "prompt_id": case.prompt_id,
                "block_name": case.block_name,
                "rule": args.rule,
                "param_name": "tau" if args.rule == "nlhf" else "beta",
                "param_value": args.tau if args.rule == "nlhf" else args.beta,
                "tv_theory_to_reference": tv,
                "reference_probs": json.dumps(jsonable_probs(case.response_indices, rho), sort_keys=True),
                "theoretical_probs": json.dumps(jsonable_probs(case.response_indices, theory), sort_keys=True),
            }
        )

    rows.sort(key=lambda row: (-float(row["tv_theory_to_reference"]), row["case_key"]))
    with csv_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "case_key",
                "prompt_id",
                "block_name",
                "rule",
                "param_name",
                "param_value",
                "tv_theory_to_reference",
                "reference_probs",
                "theoretical_probs",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)

    with keys_path.open("w") as handle:
        for row in rows:
            handle.write(f"{row['case_key']}\n")

    metadata = {
        "dataset": str(args.dataset),
        "blocks": blocks,
        "rule": args.rule,
        "rho_cache": str(args.rho_cache),
        "tau": args.tau,
        "beta": args.beta,
        "tv_threshold": args.tv_threshold,
        "count": len(rows),
        "csv": str(csv_path),
        "case_keys": str(keys_path),
    }
    with meta_path.open("w") as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True)
        handle.write("\n")

    print(json.dumps(metadata, sort_keys=True))


if __name__ == "__main__":
    main()
