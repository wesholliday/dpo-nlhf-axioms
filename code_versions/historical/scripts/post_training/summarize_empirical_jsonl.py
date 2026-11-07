#!/usr/bin/env python3
"""Summarize empirical-vs-theory JSONL outputs into compact CSV files."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any

LABELS = ("A", "B", "C", "D")


def tv_distance(p: dict[str, float] | None, q: dict[str, float] | None) -> float | None:
    if p is None or q is None:
        return None
    return 0.5 * sum(abs(float(p[label]) - float(q[label])) for label in LABELS)


def top_label(probs: dict[str, float] | None) -> tuple[str | None, float | None]:
    if probs is None:
        return None, None
    label = max(LABELS, key=lambda item: float(probs[item]))
    return label, float(probs[label])


def fmt(value: Any) -> Any:
    return "" if value is None else value


def summarize(input_path: Path, output_path: Path) -> None:
    rows: list[dict[str, Any]] = []
    with input_path.open() as handle:
        for row_number, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            reference = row.get("reference_probs")
            theory = row.get("theoretical_probs")
            final = row.get("final_probs")
            reference_top, reference_top_prob = top_label(reference)
            theory_top, theory_top_prob = top_label(theory)
            final_top, final_top_prob = top_label(final)
            rows.append(
                {
                    "row_number": row_number,
                    "index": row.get("index"),
                    "prompt_id": row.get("prompt_id"),
                    "block_name": row.get("block_name"),
                    "case_key": row.get("case_key"),
                    "duration_seconds": row.get("duration_seconds"),
                    "train_seconds": row.get("train_seconds"),
                    "tv_to_theory": row.get("tv_to_theory"),
                    "tv_theory_to_reference": tv_distance(theory, reference),
                    "tv_final_to_reference": tv_distance(final, reference),
                    "max_abs_error": row.get("max_abs_error"),
                    "reference_top": reference_top,
                    "reference_top_prob": reference_top_prob,
                    "theory_top": theory_top,
                    "theory_top_prob": theory_top_prob,
                    "final_top": final_top,
                    "final_top_prob": final_top_prob,
                    "theory_available": row.get("theory_available"),
                    "error": row.get("error"),
                }
            )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fields = [
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
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: fmt(row.get(field)) for field in fields})


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    summarize(args.input, args.output)


if __name__ == "__main__":
    main()
