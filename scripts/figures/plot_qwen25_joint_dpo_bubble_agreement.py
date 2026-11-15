#!/usr/bin/env python3
"""Agreement plot for the Qwen2.5 all-154 joint DPO run."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

from scripts.figures.plot_qwen25_bubble_agreement_panels import FIGURE_DIR, LABELS, Row, top, tv, write_one  # noqa: E402


DEFAULT_INPUT = Path("results/empirical/dpo_rtbt/joint_qwen25/run.json")
DEFAULT_STEM = "joint_qwen25_dpo_bubble_agreement"


def load_rows(path: Path) -> list[Row]:
    with path.open() as handle:
        raw = json.load(handle)

    rows: list[Row] = []
    for case in raw["per_case"]:
        theory = {label: float(case["theoretical_probs"][label]) for label in LABELS}
        empirical = {label: float(case["final_probs"][label]) for label in LABELS}
        reference = {label: float(case["reference_probs"][label]) for label in LABELS}
        rows.append(
            Row(
                case_key=str(case["case_key"]),
                theory=theory,
                empirical=empirical,
                reference=reference,
                tv_theory_reference=float(case.get("tv_theory_to_reference", tv(theory, reference))),
                tv_empirical_theory=float(case["tv_to_theory"]),
                theory_top=str(case.get("top_theory") or top(theory)),
                empirical_top=str(case.get("top_final") or top(empirical)),
            )
        )
    if not rows:
        raise ValueError(f"No per-case rows found in {path}")
    return rows


def write_plot_data(rows: list[Row], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "case_key",
                "candidate",
                "theory_probability",
                "empirical_probability",
                "reference_probability",
                "tv_theory_reference",
                "tv_empirical_theory",
                "theory_top",
                "empirical_top",
                "top_matches",
            ],
        )
        writer.writeheader()
        for row in rows:
            for label in LABELS:
                writer.writerow(
                    {
                        "case_key": row.case_key,
                        "candidate": label,
                        "theory_probability": row.theory[label],
                        "empirical_probability": row.empirical[label],
                        "reference_probability": row.reference[label],
                        "tv_theory_reference": row.tv_theory_reference,
                        "tv_empirical_theory": row.tv_empirical_theory,
                        "theory_top": row.theory_top,
                        "empirical_top": row.empirical_top,
                        "top_matches": row.theory_top == row.empirical_top,
                    }
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output-stem", default=DEFAULT_STEM)
    parser.add_argument("--right-y-max", type=float, default=1.0)
    args = parser.parse_args()

    rows = load_rows(args.input)
    write_one(
        rows,
        title="Qwen2.5 RTBT vs. joint DPO: theory vs. experiment",
        subtitle=f"{len(rows)} profiles; one shared LoRA adapter trained jointly",
        output_stem=args.output_stem,
        y_max=args.right_y_max,
    )
    csv_path = FIGURE_DIR / f"{args.output_stem}_plot_data.csv"
    write_plot_data(rows, csv_path)
    print(f"wrote {csv_path}")


if __name__ == "__main__":
    main()
