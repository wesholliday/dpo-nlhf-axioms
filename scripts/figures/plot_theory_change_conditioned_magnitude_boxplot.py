#!/usr/bin/env python3
"""Plot violation magnitudes conditioned on single-voter sensitivity."""

from __future__ import annotations

import argparse
import csv
import json
from collections import defaultdict
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


DEFAULT_INPUT = Path("results/raw/theory_change_voter_rows.jsonl")
DEFAULT_PLOT_DATA = Path("results/theory/magnitude_figure_data/violation_magnitudes_conditioned_effect_ge_0p01_theory_change_ge_0p01.csv")
DEFAULT_OUTPUT = Path("paper/figures/effect_size_conditional_ge_0p01_and_theory_change_ge_0p01_boxplot.png")
DEFAULT_SVG_OUTPUT = Path("paper/figures/effect_size_conditional_ge_0p01_and_theory_change_ge_0p01_boxplot.svg")
DEFAULT_PDF_OUTPUT = Path("paper/figures/effect_size_conditional_ge_0p01_and_theory_change_ge_0p01_boxplot.pdf")

CATEGORY_ORDER = [
    "NLHF monotonicity",
    "NLHF involvement",
    "RTBT involvement",
]
MODEL_ORDER = ["Nemo", "Qwen2.5", "Qwen3"]
MODEL_COLORS = {
    "Nemo": "#1f77b4",
    "Qwen2.5": "#d62728",
    "Qwen3": "#2ca02c",
}
MODEL_LABELS = {
    "nemo_base_strip_identity": "Nemo",
    "qwen25_base_strip_identity": "Qwen2.5",
    "qwen3_base_strip_identity": "Qwen3",
    "nemo_temperature_2": "Nemo",
    "qwen25_temperature_2": "Qwen2.5",
    "qwen3_temperature_2": "Qwen3",
}
CATEGORY_MAP = {
    ("nlhf_tie_norm", "monotonicity"): "NLHF monotonicity",
    ("nlhf_tie_norm", "involvement"): "NLHF involvement",
    ("rtbt", "involvement"): "RTBT involvement",
}


def threshold_label(value: float) -> str:
    return f"{value:.6g}"


def build_plot_data(
    input_path: Path,
    output_path: Path,
    effect_threshold: float,
    change_threshold: float,
    model_aliases: set[str] | None = None,
    nlhf_tau: float = 0.01,
    rtbt_beta: float = 0.1,
) -> list[dict]:
    profile_best: dict[tuple[str, str, str], float] = defaultdict(float)
    with input_path.open() as handle:
        for line in handle:
            if not line.strip():
                continue
            row = json.loads(line)
            target = rtbt_beta if row["rule"] == "rtbt" else nlhf_tau
            if float(row["param_value"]) != target:
                continue
            if model_aliases is not None and row["model_alias"] not in model_aliases:
                continue
            if float(row["change_threshold"]) != change_threshold:
                continue
            if not row["eligible"]:
                continue
            effect = float(row["max_effect_among_eligible_actions"])
            if effect < effect_threshold:
                continue
            category = CATEGORY_MAP.get((row["rule"], row["axiom"]))
            model = MODEL_LABELS.get(row["model_alias"])
            if category is None or model is None:
                continue
            key = (category, model, row["profile_key"])
            if effect > profile_best[key]:
                profile_best[key] = effect

    rows: list[dict] = []
    for (category, model, profile_key), effect in sorted(profile_best.items()):
        rows.append(
            {
                "category": category,
                "model": model,
                "profile_key": profile_key,
                "effect": effect,
                "threshold": effect_threshold,
                "change_threshold": change_threshold,
            }
        )

    with output_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=["category", "model", "profile_key", "effect", "threshold", "change_threshold"],
        )
        writer.writeheader()
        writer.writerows(rows)
    return rows


def load_grouped_rows(path: Path) -> tuple[dict[tuple[str, str], list[float]], float | None, float | None]:
    grouped: dict[tuple[str, str], list[float]] = defaultdict(list)
    effect_thresholds: set[float] = set()
    change_thresholds: set[float] = set()
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            model = row["model"]
            category = row["category"]
            if model not in MODEL_ORDER or category not in CATEGORY_ORDER:
                continue
            grouped[(category, model)].append(float(row["effect"]))
            effect_thresholds.add(float(row["threshold"]))
            change_thresholds.add(float(row["change_threshold"]))
    effect_threshold = effect_thresholds.pop() if len(effect_thresholds) == 1 else None
    change_threshold = change_thresholds.pop() if len(change_thresholds) == 1 else None
    return grouped, effect_threshold, change_threshold


def plot_boxplot(
    grouped: dict[tuple[str, str], list[float]],
    output: Path,
    svg_output: Path | None,
    pdf_output: Path | None,
    effect_threshold: float | None,
    change_threshold: float | None,
    title: str | None = None,
) -> None:
    rng = np.random.default_rng(0)
    fig, ax = plt.subplots(figsize=(6.6, 4.2))

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
    ax.set_xticklabels(["NLHF\nmonotonicity", "NLHF\ninvolvement", "RTBT\ninvolvement"])
    ax.set_ylabel("Violation magnitude")
    if title:
        ax.set_title(title, fontsize=11, pad=7)
    elif effect_threshold is not None and change_threshold is not None:
        ax.set_title(
            rf"Violation magnitudes conditional on $\geq {threshold_label(effect_threshold)}$ and sensitivity",
            fontsize=11,
            pad=7,
        )
    ax.grid(axis="y", alpha=0.25)
    ax.legend(legend_handles, MODEL_ORDER, frameon=False, loc="upper left", ncol=3)
    ax.set_xlim(centers[0] + offsets[0] - width * 0.8, centers[-1] + offsets[-1] + width * 0.8)
    fig.tight_layout()

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
    parser.add_argument("--nlhf-tau", type=float, default=0.01)
    parser.add_argument("--rtbt-beta", type=float, default=0.1)
    parser.add_argument("--effect-threshold", type=float, default=0.01)
    parser.add_argument("--change-threshold", type=float, default=0.01)
    parser.add_argument("--plot-data-output", type=Path, default=DEFAULT_PLOT_DATA)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--svg-output", type=Path, default=DEFAULT_SVG_OUTPUT)
    parser.add_argument("--pdf-output", type=Path, default=DEFAULT_PDF_OUTPUT)
    parser.add_argument("--title", type=str, default=None)
    parser.add_argument("--model-aliases", nargs="+", default=None)
    parser.add_argument("--no-svg", action="store_true")
    parser.add_argument("--no-pdf", action="store_true")
    args = parser.parse_args()

    if args.input.exists():
        build_plot_data(
            args.input,
            args.plot_data_output,
            args.effect_threshold,
            args.change_threshold,
            set(args.model_aliases) if args.model_aliases is not None else None,
            args.nlhf_tau,
            args.rtbt_beta,
        )
    elif not args.plot_data_output.exists():
        raise FileNotFoundError(f"Neither raw input nor plot data exists: {args.input}; {args.plot_data_output}")
    grouped, effect_threshold, change_threshold = load_grouped_rows(args.plot_data_output)
    plot_boxplot(
        grouped,
        args.output,
        None if args.no_svg else args.svg_output,
        None if args.no_pdf else args.pdf_output,
        effect_threshold,
        change_threshold,
        args.title,
    )
    print(f"Wrote {args.plot_data_output}")
    print(f"Wrote {args.output}")
    if not args.no_svg:
        print(f"Wrote {args.svg_output}")
    if not args.no_pdf:
        print(f"Wrote {args.pdf_output}")


if __name__ == "__main__":
    main()
