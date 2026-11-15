#!/usr/bin/env python3
"""Plot commutativity violation frequencies and magnitudes."""

from __future__ import annotations

import argparse
import csv
import json
import math
from collections import defaultdict
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


DEFAULT_INPUT = Path("results/theory/nlhf_tie_normalization_cache/nlhf_commutativity_violation_effects.jsonl")
DEFAULT_OUTPUT_DIR = Path("results/theory/commutativity_figure_outputs")

MODEL_ORDER = [
    "nemo_base_strip_identity",
    "qwen25_base_strip_identity",
    "qwen3_base_strip_identity",
]
MODEL_LABELS = {
    "nemo_base_strip_identity": "Nemo",
    "qwen25_base_strip_identity": "Qwen2.5",
    "qwen3_base_strip_identity": "Qwen3",
}
MODEL_COLORS = {
    "nemo_base_strip_identity": "#1f77b4",
    "qwen25_base_strip_identity": "#d62728",
    "qwen3_base_strip_identity": "#2ca02c",
}


def threshold_slug(value: float) -> str:
    return f"{value:g}".replace(".", "p").replace("-", "m")


def threshold_label(value: float) -> str:
    return f"{value:.6g}"


def tau_slug(value: float) -> str:
    return f"{value:g}".replace(".", "p")


def load_commutativity_effects(input_path: Path) -> dict[tuple[str, float, str], float]:
    """Return the best cached commutativity effect by model, tau, and profile."""

    effects: dict[tuple[str, float, str], float] = defaultdict(float)
    with input_path.open() as handle:
        for line in handle:
            if not line.strip():
                continue
            row = json.loads(line)
            if row.get("rule") != "nlhf_tie_norm":
                continue
            if row.get("axiom") != "commutativity":
                continue
            model_alias = row.get("model_alias")
            if model_alias not in MODEL_ORDER:
                continue
            tau = float(row["param_value"])
            profile_key = row["profile_key"]
            effect = float(row["effect"])
            key = (model_alias, tau, profile_key)
            if effect > effects[key]:
                effects[key] = effect
    return effects


def build_frequency_rows(
    effects: dict[tuple[str, float, str], float],
    min_effect: float,
    total_profiles: int,
) -> list[dict[str, str | float | int]]:
    rows: list[dict[str, str | float | int]] = []
    taus = sorted({tau for _, tau, _ in effects})
    for model_alias in MODEL_ORDER:
        for tau in taus:
            count = sum(
                1
                for (candidate_model, candidate_tau, _), effect in effects.items()
                if candidate_model == model_alias
                and math.isclose(candidate_tau, tau, rel_tol=0.0, abs_tol=1e-15)
                and effect >= min_effect
            )
            rows.append(
                {
                    "model_alias": model_alias,
                    "model": MODEL_LABELS[model_alias],
                    "rule": "nlhf_tie_norm",
                    "axiom": "commutativity",
                    "param_name": "tau",
                    "param_value": tau,
                    "min_effect": min_effect,
                    "profiles_total": total_profiles,
                    "profiles_with_witness": count,
                    "fraction_with_witness": count / total_profiles,
                    "percent_with_witness": 100.0 * count / total_profiles,
                }
            )
    return rows


def write_frequency_rows(rows: list[dict[str, str | float | int]], output_path: Path) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "model_alias",
                "model",
                "rule",
                "axiom",
                "param_name",
                "param_value",
                "min_effect",
                "profiles_total",
                "profiles_with_witness",
                "fraction_with_witness",
                "percent_with_witness",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)


def plot_frequency(
    rows: list[dict[str, str | float | int]],
    output_path: Path,
    svg_output_path: Path | None,
    pdf_output_path: Path | None,
    min_effect: float,
    title: str | None = None,
) -> None:
    fig, ax = plt.subplots(figsize=(5.8, 3.8))

    for model_alias in MODEL_ORDER:
        model_rows = [row for row in rows if row["model_alias"] == model_alias]
        model_rows.sort(key=lambda row: float(row["param_value"]))
        ax.plot(
            [float(row["param_value"]) for row in model_rows],
            [float(row["percent_with_witness"]) for row in model_rows],
            marker="o",
            linewidth=1.8,
            markersize=4.2,
            color=MODEL_COLORS[model_alias],
            label=MODEL_LABELS[model_alias],
        )

    ax.set_xscale("log")
    ax.set_xlabel(r"$\tau$")
    ax.set_ylabel("% of CoVal profiles")
    ax.set_title(title or rf"Commutativity violation lower bound with $\Delta \geq {threshold_label(min_effect)}$", fontsize=11, pad=7)
    ax.grid(alpha=0.25)
    ax.legend(frameon=False)
    fig.tight_layout()

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, dpi=220, bbox_inches="tight")
    if svg_output_path is not None:
        fig.savefig(svg_output_path, bbox_inches="tight")
    if pdf_output_path is not None:
        fig.savefig(pdf_output_path, bbox_inches="tight")
    plt.close(fig)


def build_magnitude_rows(
    effects: dict[tuple[str, float, str], float],
    min_effect: float,
    tau: float,
) -> list[dict[str, str | float]]:
    rows: list[dict[str, str | float]] = []
    for (model_alias, candidate_tau, profile_key), effect in sorted(effects.items()):
        if model_alias not in MODEL_ORDER:
            continue
        if not math.isclose(candidate_tau, tau, rel_tol=0.0, abs_tol=1e-15):
            continue
        if effect < min_effect:
            continue
        rows.append(
            {
                "model_alias": model_alias,
                "model": MODEL_LABELS[model_alias],
                "rule": "nlhf_tie_norm",
                "axiom": "commutativity",
                "param_name": "tau",
                "param_value": tau,
                "profile_key": profile_key,
                "effect": effect,
                "min_effect": min_effect,
            }
        )
    return rows


def write_magnitude_rows(rows: list[dict[str, str | float]], output_path: Path) -> None:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "model_alias",
                "model",
                "rule",
                "axiom",
                "param_name",
                "param_value",
                "profile_key",
                "effect",
                "min_effect",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)


def plot_magnitudes(
    rows: list[dict[str, str | float]],
    output_path: Path,
    svg_output_path: Path | None,
    pdf_output_path: Path | None,
    min_effect: float,
    tau: float,
    title: str | None = None,
) -> None:
    rng = np.random.default_rng(0)
    fig, ax = plt.subplots(figsize=(4.8, 3.8))

    values_by_model = {
        model_alias: [float(row["effect"]) for row in rows if row["model_alias"] == model_alias]
        for model_alias in MODEL_ORDER
    }
    positions = np.arange(len(MODEL_ORDER), dtype=float)
    values = [values_by_model[model_alias] for model_alias in MODEL_ORDER]

    boxes = ax.boxplot(
        values,
        positions=positions,
        widths=0.42,
        patch_artist=True,
        showfliers=False,
        medianprops={"color": "black", "linewidth": 1.0},
    )
    for patch, model_alias in zip(boxes["boxes"], MODEL_ORDER):
        patch.set_facecolor(MODEL_COLORS[model_alias])
        patch.set_alpha(0.28)
        patch.set_edgecolor(MODEL_COLORS[model_alias])
    for key in ("whiskers", "caps"):
        for line_index, line in enumerate(boxes[key]):
            model_alias = MODEL_ORDER[line_index // 2]
            line.set_color(MODEL_COLORS[model_alias])
            line.set_linewidth(1.0)

    for position, model_alias in zip(positions, MODEL_ORDER):
        effects = values_by_model[model_alias]
        if not effects:
            continue
        jitter = rng.normal(0.0, 0.045, size=len(effects))
        ax.scatter(
            np.full(len(effects), position) + jitter,
            effects,
            s=10,
            color=MODEL_COLORS[model_alias],
            alpha=0.42,
            linewidths=0,
            zorder=3,
        )

    ax.set_xticks(positions)
    ax.set_xticklabels([MODEL_LABELS[model_alias] for model_alias in MODEL_ORDER])
    ax.set_xlim(positions[0] - 0.45, positions[-1] + 0.45)
    ax.set_ylabel("Violation magnitude (TV distance)")
    ax.set_title(
        title
        or rf"Magnitude of commutativity violations ($\geq {threshold_label(min_effect)}$)",
        fontsize=11,
        pad=7,
    )
    ax.grid(axis="y", alpha=0.25)
    fig.tight_layout()

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, dpi=220, bbox_inches="tight")
    if svg_output_path is not None:
        fig.savefig(svg_output_path, bbox_inches="tight")
    if pdf_output_path is not None:
        fig.savefig(pdf_output_path, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--min-effect", type=float, default=0.01)
    parser.add_argument("--boxplot-tau", type=float, default=0.01)
    parser.add_argument("--total-profiles", type=int, default=1399)
    parser.add_argument("--frequency-title", type=str, default=None)
    parser.add_argument("--magnitude-title", type=str, default=None)
    parser.add_argument("--no-svg", action="store_true")
    parser.add_argument("--no-pdf", action="store_true")
    args = parser.parse_args()

    effects = load_commutativity_effects(args.input)
    min_slug = threshold_slug(args.min_effect)
    tau_slug_value = tau_slug(args.boxplot_tau)

    frequency_rows = build_frequency_rows(effects, args.min_effect, args.total_profiles)
    frequency_csv = args.output_dir / f"commutativity_frequency_min_effect_{min_slug}_plot_data.csv"
    frequency_png = args.output_dir / f"commutativity_frequency_min_effect_{min_slug}.png"
    frequency_svg = None if args.no_svg else args.output_dir / f"commutativity_frequency_min_effect_{min_slug}.svg"
    frequency_pdf = None if args.no_pdf else args.output_dir / f"commutativity_frequency_min_effect_{min_slug}.pdf"
    write_frequency_rows(frequency_rows, frequency_csv)
    plot_frequency(frequency_rows, frequency_png, frequency_svg, frequency_pdf, args.min_effect, args.frequency_title)

    magnitude_rows = build_magnitude_rows(effects, args.min_effect, args.boxplot_tau)
    magnitude_csv = args.output_dir / f"commutativity_magnitude_tau{tau_slug_value}_min_effect_{min_slug}_plot_data.csv"
    magnitude_png = args.output_dir / f"commutativity_magnitude_tau{tau_slug_value}_min_effect_{min_slug}_boxplot.png"
    magnitude_svg = None if args.no_svg else args.output_dir / f"commutativity_magnitude_tau{tau_slug_value}_min_effect_{min_slug}_boxplot.svg"
    magnitude_pdf = None if args.no_pdf else args.output_dir / f"commutativity_magnitude_tau{tau_slug_value}_min_effect_{min_slug}_boxplot.pdf"
    write_magnitude_rows(magnitude_rows, magnitude_csv)
    plot_magnitudes(
        magnitude_rows,
        magnitude_png,
        magnitude_svg,
        magnitude_pdf,
        args.min_effect,
        args.boxplot_tau,
        args.magnitude_title,
    )

    print(f"Wrote {frequency_csv}")
    print(f"Wrote {frequency_png}")
    if frequency_svg is not None:
        print(f"Wrote {frequency_svg}")
    if frequency_pdf is not None:
        print(f"Wrote {frequency_pdf}")
    print(f"Wrote {magnitude_csv}")
    print(f"Wrote {magnitude_png}")
    if magnitude_svg is not None:
        print(f"Wrote {magnitude_svg}")
    if magnitude_pdf is not None:
        print(f"Wrote {magnitude_pdf}")


if __name__ == "__main__":
    main()
