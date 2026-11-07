#!/usr/bin/env python3
"""Plot profile-level violation frequencies vs theory-change threshold."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


DEFAULT_OUTPUT = Path(
    "results/theory/frequency_figure_data/profile_conditioned_on_theory_change_effect_0p01.png"
)
DEFAULT_SVG_OUTPUT = Path(
    "results/theory/frequency_figure_data/profile_conditioned_on_theory_change_effect_0p01.svg"
)
DEFAULT_PLOT_DATA = Path(
    "results/theory/frequency_figure_data/profile_conditioned_on_theory_change_effect_0p01_plot_data.csv"
)

MODEL_STYLES = {
    "nemo_base_strip_identity": {"label": "Nemo", "color": "#1f77b4"},
    "qwen25_base_strip_identity": {"label": "Qwen2.5", "color": "#d62728"},
    "qwen3_base_strip_identity": {"label": "Qwen3", "color": "#2ca02c"},
}

PANELS = [
    ("nlhf_tie_norm", "monotonicity", "NLHF Monotonicity Violation", "tau", "0.01"),
    ("nlhf_tie_norm", "involvement", "NLHF Involvement Violation", "tau", "0.01"),
    ("rtbt", "involvement", "RTBT Involvement Violation", "beta", "0.1"),
]


def load_rows(path: Path, effect_threshold: float) -> list[dict]:
    rows: list[dict] = []
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            if float(row["effect_threshold"]) != effect_threshold:
                continue
            rows.append(
                {
                    "change_threshold": float(row["change_threshold"]),
                    "effect_threshold": float(row["effect_threshold"]),
                    "model_alias": row["model_alias"],
                    "rule": row["rule"],
                    "axiom": row["axiom"],
                    "param_name": row["param_name"],
                    "param_value": float(row["param_value"]),
                    "profiles_eligible": int(row["profiles_eligible"]),
                    "profiles_with_witness": int(row["profiles_with_witness"]),
                    "percent_with_witness": float(row["percent_with_witness"]),
                }
            )
    return rows


def write_plot_data(path: Path, rows: list[dict]) -> None:
    fieldnames = [
        "panel",
        "model",
        "change_threshold",
        "profiles_eligible",
        "profiles_with_witness",
        "percent_with_witness",
    ]
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for rule, axiom, title, _param_name, param_value in PANELS:
            for model_alias, style in MODEL_STYLES.items():
                subset = [
                    row
                    for row in rows
                    if row["model_alias"] == model_alias
                    and row["rule"] == rule
                    and row["axiom"] == axiom
                    and f"{row['param_value']:g}" == param_value
                ]
                subset.sort(key=lambda row: row["change_threshold"])
                for row in subset:
                    writer.writerow(
                        {
                            "panel": title,
                            "model": style["label"],
                            "change_threshold": row["change_threshold"],
                            "profiles_eligible": row["profiles_eligible"],
                            "profiles_with_witness": row["profiles_with_witness"],
                            "percent_with_witness": row["percent_with_witness"],
                        }
                    )


def plot_rows(rows: list[dict], output: Path, svg_output: Path | None, effect_threshold: float) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(12.0, 3.8), constrained_layout=True, sharey=True)

    for ax, (rule, axiom, title, _param_name, param_value) in zip(axes, PANELS):
        panel_max = 0.0
        for model_alias, style in MODEL_STYLES.items():
            subset = [
                row
                for row in rows
                if row["model_alias"] == model_alias
                and row["rule"] == rule
                and row["axiom"] == axiom
                and f"{row['param_value']:g}" == param_value
            ]
            subset.sort(key=lambda row: row["change_threshold"])
            if not subset:
                continue
            xs = [row["change_threshold"] for row in subset]
            ys = [row["percent_with_witness"] for row in subset]
            panel_max = max(panel_max, max(ys))
            ax.plot(
                xs,
                ys,
                marker="o",
                linewidth=2.0,
                markersize=5,
                label=style["label"],
                color=style["color"],
            )
        ax.set_xscale("log")
        ax.set_xlabel("single-voter sensitivity threshold")
        ax.set_title(title, fontsize=11)
        ax.grid(True, alpha=0.3)
        ax.set_ylim(0.0, panel_max + max(0.25, 0.08 * panel_max))
    axes[0].set_ylabel("% of sensitive CoVal profiles")
    axes[0].legend(frameon=False, loc="best")
    fig.suptitle(rf"Profile-level violations with magnitude $\Delta \geq {effect_threshold:g}$", fontsize=11)

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=220, bbox_inches="tight")
    if svg_output is not None:
        fig.savefig(svg_output, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True,
                        help="CSV with effect_threshold and change_threshold columns; use the audited profile_conditioned_on_theory_change.csv.")
    parser.add_argument("--effect-threshold", type=float, default=0.01)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--svg-output", type=Path, default=DEFAULT_SVG_OUTPUT)
    parser.add_argument("--plot-data-output", type=Path, default=DEFAULT_PLOT_DATA)
    parser.add_argument("--no-svg", action="store_true")
    args = parser.parse_args()

    rows = load_rows(args.input, args.effect_threshold)
    write_plot_data(args.plot_data_output, rows)
    plot_rows(rows, args.output, None if args.no_svg else args.svg_output, args.effect_threshold)
    print(f"Wrote {args.plot_data_output}")
    print(f"Wrote {args.output}")
    if not args.no_svg:
        print(f"Wrote {args.svg_output}")


if __name__ == "__main__":
    main()
