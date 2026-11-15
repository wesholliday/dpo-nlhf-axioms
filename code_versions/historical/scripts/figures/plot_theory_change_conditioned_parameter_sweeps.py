#!/usr/bin/env python3
"""Plot parameter sweeps conditioned on single-voter sensitivity."""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


DEFAULT_INPUT = Path(
    "results/theory/frequency_figure_data/profile_conditioned_summary.csv"
)
DEFAULT_OUTPUT = Path(
    "results/theory/frequency_figure_data/"
    "model_only_reference_involvement_parameter_sweeps_conditioned_theory_change_0p01_min_effect_0p01.png"
)
DEFAULT_SVG_OUTPUT = Path(
    "results/theory/frequency_figure_data/"
    "model_only_reference_involvement_parameter_sweeps_conditioned_theory_change_0p01_min_effect_0p01.svg"
)
DEFAULT_PLOT_DATA = Path(
    "results/theory/frequency_figure_data/"
    "model_only_reference_involvement_parameter_sweeps_conditioned_theory_change_0p01_min_effect_0p01_plot_data.csv"
)

MODEL_STYLES = {
    "nemo_base_strip_identity": {"label": "Nemo", "color": "#1f77b4"},
    "qwen25_base_strip_identity": {"label": "Qwen2.5", "color": "#d62728"},
    "qwen3_base_strip_identity": {"label": "Qwen3", "color": "#2ca02c"},
    "nemo_temperature_2": {"label": "Nemo T=2", "color": "#1f77b4", "linestyle": "--"},
    "qwen25_temperature_2": {"label": "Qwen2.5 T=2", "color": "#d62728", "linestyle": "--"},
    "qwen3_temperature_2": {"label": "Qwen3 T=2", "color": "#2ca02c", "linestyle": "--"},
    "nemo_clipped_eps_0p01": {"label": "Nemo clipped", "color": "#1f77b4", "linestyle": ":"},
    "qwen25_clipped_eps_0p01": {"label": "Qwen2.5 clipped", "color": "#d62728", "linestyle": ":"},
    "qwen3_clipped_eps_0p01": {"label": "Qwen3 clipped", "color": "#2ca02c", "linestyle": ":"},
}

PANELS = [
    ("nlhf_tie_norm", "monotonicity", "NLHF Monotonicity Violation", "tau"),
    ("nlhf_tie_norm", "involvement", "NLHF Involvement Violation", "tau"),
    ("rtbt", "involvement", "RTBT Involvement Violation", "beta"),
]


def load_rows(path: Path, effect_threshold: float, change_threshold: float) -> list[dict]:
    rows: list[dict] = []
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            if not math.isclose(float(row["effect_threshold"]), effect_threshold, rel_tol=0.0, abs_tol=1e-12):
                continue
            if not math.isclose(float(row["change_threshold"]), change_threshold, rel_tol=0.0, abs_tol=1e-12):
                continue
            rows.append(
                {
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
        "param_name",
        "param_value",
        "profiles_eligible",
        "profiles_with_witness",
        "percent_with_witness",
    ]
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
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
                            "profiles_eligible": row["profiles_eligible"],
                            "profiles_with_witness": row["profiles_with_witness"],
                            "percent_with_witness": row["percent_with_witness"],
                        }
                    )


def plot_rows(
    rows: list[dict],
    output: Path,
    svg_output: Path | None,
    effect_threshold: float,
    change_threshold: float,
    title: str | None = None,
) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(12.0, 3.9), constrained_layout=True, sharey=True)
    global_max = max((row["percent_with_witness"] for row in rows), default=0.0)
    for ax, (rule, axiom, panel_title, param_name) in zip(axes, PANELS):
        for model_alias, style in MODEL_STYLES.items():
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
            ax.plot(
                xs,
                ys,
                marker="o",
                linewidth=2.0,
                markersize=5,
                color=style["color"],
                linestyle=style.get("linestyle", "-"),
                label=style["label"],
            )
        ax.set_xscale("log")
        ax.set_xlabel(param_name)
        ax.set_title(panel_title, fontsize=11)
        ax.grid(True, alpha=0.3)
    axes[0].set_ylim(0.0, global_max + max(0.25, 0.08 * global_max))
    axes[0].set_ylabel("% of sensitive CoVal profiles")
    axes[0].legend(frameon=False, loc="best")
    if title is None:
        title = rf"Violations with magnitude $\Delta \geq {effect_threshold:g}$, among profiles sensitive to a single voter at threshold ${change_threshold:g}$"
    fig.suptitle(title, fontsize=11)

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=220, bbox_inches="tight")
    if svg_output is not None:
        fig.savefig(svg_output, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--effect-threshold", type=float, default=0.01)
    parser.add_argument("--change-threshold", type=float, default=0.01)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--svg-output", type=Path, default=DEFAULT_SVG_OUTPUT)
    parser.add_argument("--plot-data-output", type=Path, default=DEFAULT_PLOT_DATA)
    parser.add_argument("--title", type=str, default=None)
    parser.add_argument("--no-svg", action="store_true")
    args = parser.parse_args()

    rows = load_rows(args.input, args.effect_threshold, args.change_threshold)
    write_plot_data(args.plot_data_output, rows)
    plot_rows(
        rows,
        args.output,
        None if args.no_svg else args.svg_output,
        args.effect_threshold,
        args.change_threshold,
        title=args.title,
    )
    print(f"Wrote {args.plot_data_output}")
    print(f"Wrote {args.output}")
    if not args.no_svg:
        print(f"Wrote {args.svg_output}")


if __name__ == "__main__":
    main()
