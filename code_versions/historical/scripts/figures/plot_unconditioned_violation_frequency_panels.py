#!/usr/bin/env python3
"""Plot unconditioned monotonicity/involvement violation frequencies."""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


DEFAULT_INPUT = Path("results/theory/frequency_figure_data/profile_conditioned_summary.csv")
DEFAULT_OUTPUT = Path("paper/figures/violation_frequency_unconditioned_three_panel_min_effect_0p01.png")
DEFAULT_SVG_OUTPUT = Path("paper/figures/violation_frequency_unconditioned_three_panel_min_effect_0p01.svg")
DEFAULT_PDF_OUTPUT = Path("paper/figures/violation_frequency_unconditioned_three_panel_min_effect_0p01.pdf")
DEFAULT_PLOT_DATA = Path(
    "results/theory/frequency_figure_data/"
    "violation_frequency_unconditioned_three_panel_min_effect_0p01_plot_data.csv"
)

MODEL_ORDER = ["Nemo", "Qwen2.5", "Qwen3"]
MODEL_STYLES = {
    "nemo_base_strip_identity": {"label": "Nemo", "color": "#1f77b4"},
    "qwen25_base_strip_identity": {"label": "Qwen2.5", "color": "#d62728"},
    "qwen3_base_strip_identity": {"label": "Qwen3", "color": "#2ca02c"},
}

PANELS = [
    ("nlhf_tie_norm", "monotonicity", "NLHF Monotonicity Violation", "tau"),
    ("nlhf_tie_norm", "involvement", "NLHF Involvement Violation", "tau"),
    ("rtbt", "involvement", "RTBT Involvement Violation", "beta"),
]
RTBT_DOMAIN_PROFILES = 1320


def load_rows(path: Path, effect_threshold: float) -> list[dict]:
    rows: list[dict] = []
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            if row["condition"] != "all":
                continue
            if row["source"] != "single_voter":
                continue
            if not math.isclose(float(row["threshold"]), effect_threshold, rel_tol=0.0, abs_tol=1e-12):
                continue
            profiles_total = int(row["profiles_total"])
            profiles_with_witness = int(row["profiles_with_witness"])
            percent_with_witness = float(row["percent_with_witness"])
            if row["rule"] == "rtbt":
                profiles_total = RTBT_DOMAIN_PROFILES
                percent_with_witness = 100.0 * profiles_with_witness / profiles_total
            rows.append(
                {
                    "model_alias": row["model_alias"],
                    "rule": row["rule"],
                    "axiom": row["axiom"],
                    "param_name": row["param_name"],
                    "param_value": float(row["param_value"]),
                    "profiles_total": profiles_total,
                    "profiles_with_witness": profiles_with_witness,
                    "percent_with_witness": percent_with_witness,
                }
            )
    return rows


def write_plot_data(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "panel",
                "model",
                "param_name",
                "param_value",
                "profiles_total",
                "profiles_with_witness",
                "percent_with_witness",
                "condition",
            ],
        )
        writer.writeheader()
        for rule, axiom, title, param_name in PANELS:
            for model_alias, style in MODEL_STYLES.items():
                subset = [
                    row
                    for row in rows
                    if row["model_alias"] == model_alias
                    and row["rule"] == rule
                    and row["axiom"] == axiom
                ]
                subset.sort(key=lambda row: row["param_value"])
                for row in subset:
                    writer.writerow(
                        {
                            "panel": title,
                            "model": style["label"],
                            "param_name": param_name,
                            "param_value": row["param_value"],
                            "profiles_total": row["profiles_total"],
                            "profiles_with_witness": row["profiles_with_witness"],
                            "percent_with_witness": row["percent_with_witness"],
                            "condition": "unconditioned",
                        }
                    )


def plot_rows(rows: list[dict], output: Path, svg_output: Path | None, pdf_output: Path | None) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(12.0, 3.8), constrained_layout=True, sharey=True)

    label_to_alias = {style["label"]: alias for alias, style in MODEL_STYLES.items()}
    for ax, (rule, axiom, title, param_name) in zip(axes, PANELS):
        panel_max = 0.0
        for model_label in MODEL_ORDER:
            model_alias = label_to_alias[model_label]
            style = MODEL_STYLES[model_alias]
            subset = [
                row
                for row in rows
                if row["model_alias"] == model_alias
                and row["rule"] == rule
                and row["axiom"] == axiom
            ]
            subset.sort(key=lambda row: row["param_value"])
            if not subset:
                continue
            xs = [row["param_value"] for row in subset]
            ys = [row["percent_with_witness"] for row in subset]
            panel_max = max(panel_max, max(ys))
            ax.plot(
                xs,
                ys,
                marker="o",
                linewidth=2.0,
                markersize=5,
                color=style["color"],
                label=style["label"],
            )
        ax.set_xscale("log")
        ax.set_xlabel(param_name)
        ax.set_title(title, fontsize=11)
        ax.grid(True, alpha=0.3)
        ax.set_ylim(0.0, panel_max + max(0.25, 0.08 * panel_max))

    axes[0].set_ylabel("% of profiles")
    axes[0].legend(frameon=False, loc="best")
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=220, bbox_inches="tight")
    if svg_output is not None:
        fig.savefig(svg_output, bbox_inches="tight")
    if pdf_output is not None:
        fig.savefig(pdf_output, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--effect-threshold", type=float, default=0.01)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--svg-output", type=Path, default=DEFAULT_SVG_OUTPUT)
    parser.add_argument("--pdf-output", type=Path, default=DEFAULT_PDF_OUTPUT)
    parser.add_argument("--plot-data-output", type=Path, default=DEFAULT_PLOT_DATA)
    parser.add_argument("--no-svg", action="store_true")
    parser.add_argument("--no-pdf", action="store_true")
    args = parser.parse_args()

    rows = load_rows(args.input, args.effect_threshold)
    write_plot_data(args.plot_data_output, rows)
    plot_rows(rows, args.output, None if args.no_svg else args.svg_output, None if args.no_pdf else args.pdf_output)
    print(f"Wrote {args.plot_data_output}")
    print(f"Wrote {args.output}")
    if not args.no_svg:
        print(f"Wrote {args.svg_output}")
    if not args.no_pdf:
        print(f"Wrote {args.pdf_output}")


if __name__ == "__main__":
    main()
