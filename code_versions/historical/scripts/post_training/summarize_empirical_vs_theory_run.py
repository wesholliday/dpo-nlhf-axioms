#!/usr/bin/env python3
"""Convert an empirical-vs-theory JSONL run into a compact CSV summary."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path


def top_entry(probs: dict[str, float] | None) -> tuple[str, float]:
    if not probs:
        return "", float("nan")
    label, value = max(probs.items(), key=lambda item: float(item[1]))
    return label, float(value)


def tv_distance(left: dict[str, float] | None, right: dict[str, float] | None) -> float:
    if not left or not right:
        return float("nan")
    labels = sorted(set(left) | set(right))
    return 0.5 * sum(abs(float(left.get(label, 0.0)) - float(right.get(label, 0.0))) for label in labels)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input_jsonl", type=Path)
    parser.add_argument("--output-csv", type=Path, default=None)
    args = parser.parse_args()

    input_path = args.input_jsonl
    output_path = (
        args.output_csv
        if args.output_csv is not None
        else input_path.with_suffix(".summary.csv")
    )

    rows: list[dict] = []
    with input_path.open() as handle:
        for line_number, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            reference_probs = record.get("reference_probs")
            theoretical_probs = record.get("theoretical_probs")
            final_probs = record.get("final_probs")
            ref_top, ref_top_prob = top_entry(record.get("reference_probs"))
            theory_top, theory_top_prob = top_entry(record.get("theoretical_probs"))
            final_top, final_top_prob = top_entry(record.get("final_probs"))
            rows.append(
                {
                    "row_number": line_number,
                    "index": record.get("index"),
                    "prompt_id": record.get("prompt_id"),
                    "block_name": record.get("block_name"),
                    "case_key": record.get("case_key"),
                    "duration_seconds": record.get("duration_seconds"),
                    "train_seconds": record.get("train_seconds"),
                    "tv_to_theory": record.get("tv_to_theory"),
                    "tv_theory_to_reference": tv_distance(theoretical_probs, reference_probs),
                    "tv_final_to_reference": tv_distance(final_probs, reference_probs),
                    "max_abs_error": record.get("max_abs_error"),
                    "reference_top": ref_top,
                    "reference_top_prob": ref_top_prob,
                    "theory_top": theory_top,
                    "theory_top_prob": theory_top_prob,
                    "final_top": final_top,
                    "final_top_prob": final_top_prob,
                    "theory_available": record.get("theory_available"),
                    "error": record.get("error", ""),
                }
            )

    fieldnames = [
        "row_number",
        "index",
        "prompt_id",
        "block_name",
        "case_key",
        "duration_seconds",
        "train_seconds",
        "tv_to_theory",
        "tv_theory_to_reference",
        "tv_final_to_reference",
        "max_abs_error",
        "reference_top",
        "reference_top_prob",
        "theory_top",
        "theory_top_prob",
        "final_top",
        "final_top_prob",
        "theory_available",
        "error",
    ]

    with output_path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    print(f"Wrote {output_path}")


if __name__ == "__main__":
    main()
