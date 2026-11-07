#!/usr/bin/env python3
"""Plot the violation-magnitude boxplot used in the paper."""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


DEFAULT_INPUT = Path(
    "results/theory/magnitude_figure_data/"
    "effect_size_conditional_ge_0p01_lumped_involvement_with_commutativity_plot_data.csv"
)
DEFAULT_OUTPUT = Path("effect_size_conditional_ge_0p01_lumped_involvement_with_commutativity_boxplot.png")
DEFAULT_SVG_OUTPUT = Path("effect_size_conditional_ge_0p01_lumped_involvement_with_commutativity_boxplot.svg")

CATEGORY_ORDER = [
    "NLHF monotonicity",
    "NLHF involvement",
    "NLHF commutativity",
    "RTBT involvement",
]
MODEL_ORDER = ["Nemo", "Qwen2.5", "Qwen3"]
MODEL_COLORS = {
    "Nemo": "#1f77b4",
    "Qwen2.5": "#d62728",
    "Qwen3": "#2ca02c",
}


def threshold_label(value: float) -> str:
    return f"{value:.6g}"


def load_rows(path: Path) -> tuple[dict[tuple[str, str], list[float]], float | None]:
    grouped: dict[tuple[str, str], list[float]] = defaultdict(list)
    thresholds: set[float] = set()
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            model = row["model"]
            category = row["category"]
            if model not in MODEL_ORDER or category not in CATEGORY_ORDER:
                continue
            grouped[(category, model)].append(float(row["effect"]))
            if row.get("threshold"):
                thresholds.add(float(row["threshold"]))
    threshold = thresholds.pop() if len(thresholds) == 1 else None
    return grouped, threshold


def plot_boxplot(
    grouped: dict[tuple[str, str], list[float]],
    output: Path,
    svg_output: Path | None,
    threshold: float | None,
) -> None:
    rng = np.random.default_rng(0)
    fig, ax = plt.subplots(figsize=(9.0, 4.4))

    group_spacing = 0.78
    centers = np.arange(len(CATEGORY_ORDER), dtype=float) * group_spacing
    offsets = np.array([-0.18, 0.0, 0.18])
    width = 0.14

    legend_handles = []
    for model_index, model in enumerate(MODEL_ORDER):
        positions = centers + offsets[model_index]
        values = [grouped.get((category, model), []) for category in CATEGORY_ORDER]
        color = MODEL_COLORS[model]
        boxes = ax.boxplot(
            values,
            positions=positions,
            widths=width,
            patch_artist=True,
            showfliers=False,
            medianprops={"color": "black", "linewidth": 1.0},
            boxprops={"facecolor": color, "alpha": 0.28, "edgecolor": color, "linewidth": 1.0},
            whiskerprops={"color": color, "linewidth": 1.0},
            capprops={"color": color, "linewidth": 1.0},
        )
        legend_handles.append(boxes["boxes"][0])
        for position, effects in zip(positions, values):
            if not effects:
                continue
            jitter = rng.normal(0.0, width * 0.16, size=len(effects))
            ax.scatter(
                np.full(len(effects), position) + jitter,
                effects,
                s=11,
                color=color,
                alpha=0.45,
                linewidths=0,
                zorder=3,
            )

    ax.set_xticks(centers)
    ax.set_xticklabels(
        [
            "NLHF\nmonotonicity",
            "NLHF\ninvolvement",
            "NLHF\ncommutativity",
            "RTBT\ninvolvement",
        ]
    )
    ax.set_ylabel("Violation magnitude")
    if threshold is not None:
        ax.set_title(rf"Violation magnitudes conditional on $\Delta \geq {threshold_label(threshold)}$", fontsize=11, pad=7)
    else:
        ax.set_title(r"Violation magnitudes conditional on threshold", fontsize=11, pad=7)
    ax.grid(axis="y", alpha=0.25)
    ax.legend(legend_handles, MODEL_ORDER, frameon=False, loc="upper right", ncol=3)
    ax.margins(x=0.035)
    fig.tight_layout()

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=220, bbox_inches="tight")
    if svg_output is not None:
        svg_output.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(svg_output, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--svg-output", type=Path, default=DEFAULT_SVG_OUTPUT)
    parser.add_argument("--no-svg", action="store_true")
    args = parser.parse_args()

    grouped, threshold = load_rows(args.input)
    plot_boxplot(grouped, args.output, None if args.no_svg else args.svg_output, threshold)
    print(f"Wrote {args.output}")
    if not args.no_svg:
        print(f"Wrote {args.svg_output}")


if __name__ == "__main__":
    main()
