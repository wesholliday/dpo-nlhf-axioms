#!/usr/bin/env python3
"""Three-panel NLHF/Nash-MD commutativity agreement plot."""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import statistics
from dataclasses import dataclass
from pathlib import Path

Path("/tmp/matplotlib-codex").mkdir(parents=True, exist_ok=True)
Path("/tmp/codex-xdg-cache").mkdir(parents=True, exist_ok=True)
os.environ.setdefault("MPLCONFIGDIR", "/tmp/matplotlib-codex")
os.environ.setdefault("XDG_CACHE_HOME", "/tmp/codex-xdg-cache")

import matplotlib.pyplot as plt
from matplotlib.lines import Line2D


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "paper/figures/nlhf_commutativity_single_profile_nashmd_agreement.svg"
DEFAULT_PDF_OUTPUT = ROOT / "paper/figures/nlhf_commutativity_single_profile_nashmd_agreement.pdf"
DEFAULT_PLOT_DATA = ROOT / "results/figure_plot_data/nlhf_commutativity_single_profile_nashmd_agreement_plot_data.csv"
MODEL_ORDER = ["Qwen2.5", "Nemo", "Qwen3"]
MODEL_COLORS = {
    "Nemo": "#1f77b4",
    "Qwen2.5": "#d62728",
    "Qwen3": "#2ca02c",
}
THRESHOLD = 0.01


@dataclass(frozen=True)
class ModelSpec:
    label: str
    summaries: tuple[Path, ...]
    expected_indices: tuple[int, ...] | None


@dataclass(frozen=True)
class Point:
    model: str
    witness_index: int
    prompt_id: str
    block_name: str
    theory_magnitude: float
    empirical_magnitude: float
    abs_error: float
    empirical_violation: bool
    theory_source: str


DEFAULT_MODELS = [
    ModelSpec(
        "Qwen2.5",
        (ROOT / "results/empirical/nlhf_nashmd/commutativity_witnesses/qwen25_summary.csv",),
        tuple(range(1, 89)),
    ),
    ModelSpec(
        "Nemo",
        (ROOT / "results/empirical/nlhf_nashmd/commutativity_witnesses/nemo_summary.csv",),
        tuple(range(1, 86)),
    ),
    ModelSpec(
        "Qwen3",
        (ROOT / "results/empirical/nlhf_nashmd/commutativity_witnesses/qwen3_summary.csv",),
        tuple(range(1, 79)),
    ),
]


def correlation(xs: list[float], ys: list[float]) -> float:
    if len(xs) < 2:
        return float("nan")
    mean_x = statistics.mean(xs)
    mean_y = statistics.mean(ys)
    cov = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    var_x = sum((x - mean_x) ** 2 for x in xs)
    var_y = sum((y - mean_y) ** 2 for y in ys)
    if var_x == 0.0 or var_y == 0.0:
        return float("nan")
    return cov / math.sqrt(var_x * var_y)


def is_finite_point(point: Point) -> bool:
    return (
        math.isfinite(point.theory_magnitude)
        and math.isfinite(point.empirical_magnitude)
        and math.isfinite(point.abs_error)
    )


def format_stat(value: float) -> str:
    return "n/a" if not math.isfinite(value) else f"{value:.3f}"


def nice_tick_label(value: float) -> str:
    if abs(value) < 1e-12:
        return "0"
    return f"{value:.2g}"


def probs_tv(left: dict[str, float] | None, right: dict[str, float] | None) -> float | None:
    if left is None or right is None:
        return None
    labels = ("A", "B", "C", "D")
    return 0.5 * sum(abs(float(left.get(label, 0.0)) - float(right.get(label, 0.0))) for label in labels)


def commutativity_magnitudes(row: dict[str, str]) -> tuple[float, float, str]:
    order12_probs = json.loads(row["empirical_order12_json"])
    order21_probs = json.loads(row["empirical_order21_json"])
    empirical = probs_tv(order12_probs, order21_probs)
    if empirical is None:
        empirical = float(row["empirical_commutativity_magnitude"])

    return float(row["theory_commutativity_magnitude"]), empirical, "summary"


def load_points(spec: ModelSpec) -> list[Point]:
    rows_by_index: dict[int, dict[str, str]] = {}
    for summary in spec.summaries:
        if not summary.exists():
            raise FileNotFoundError(summary)
        with summary.open() as handle:
            for row in csv.DictReader(handle):
                idx = int(row["witness_index"])
                if idx not in rows_by_index:
                    rows_by_index[idx] = row
    if spec.expected_indices is not None:
        missing = [idx for idx in spec.expected_indices if idx not in rows_by_index]
        if missing:
            raise ValueError(f"missing {spec.label} witness indices: {missing}")
        ordered = [rows_by_index[idx] for idx in spec.expected_indices]
    else:
        ordered = [rows_by_index[idx] for idx in sorted(rows_by_index)]
    points: list[Point] = []
    for row in ordered:
        theory, empirical, theory_source = commutativity_magnitudes(row)
        points.append(
            Point(
                model=spec.label,
                witness_index=int(row["witness_index"]),
                prompt_id=row["prompt_id"],
                block_name=row["block_name"],
                theory_magnitude=theory,
                empirical_magnitude=empirical,
                abs_error=abs(empirical - theory),
                empirical_violation=empirical >= THRESHOLD,
                theory_source=theory_source,
            )
        )
    return points



def write_plot_data(path: Path, points_by_model: dict[str, list[Point]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "model",
                "witness_index",
                "prompt_id",
                "block_name",
                "theory_commutativity_magnitude",
                "empirical_commutativity_magnitude",
                "abs_error",
                "empirical_violation",
                "theory_source",
            ],
        )
        writer.writeheader()
        for model in MODEL_ORDER:
            for point in points_by_model.get(model, []):
                writer.writerow(
                    {
                        "model": point.model,
                        "witness_index": point.witness_index,
                        "prompt_id": point.prompt_id,
                        "block_name": point.block_name,
                        "theory_commutativity_magnitude": point.theory_magnitude,
                        "empirical_commutativity_magnitude": point.empirical_magnitude,
                        "abs_error": point.abs_error,
                        "empirical_violation": point.empirical_violation,
                        "theory_source": point.theory_source,
                    }
                )


def render(
    points_by_model: dict[str, list[Point]],
    output: Path,
    pdf_output: Path | None,
    x_axis_label: str,
    title: str,
) -> None:
    all_points = [point for points in points_by_model.values() for point in points]
    if not all_points:
        raise ValueError("No completed commutativity rows found")
    finite_all_points = [point for point in all_points if is_finite_point(point)]
    if not finite_all_points:
        raise ValueError("No finite completed commutativity rows found")

    axis_min = -0.1
    max_value = max(
        1.0,
        *(point.theory_magnitude for point in finite_all_points),
        *(point.empirical_magnitude for point in finite_all_points),
    )
    axis_max = max(1.05, math.ceil((max_value + 0.03) * 20.0) / 20.0)
    ticks = [tick for tick in [-0.1, 0.0, 0.25, 0.5, 0.75, 1.0] if axis_min <= tick <= axis_max]

    canvas_width = 943
    canvas_height = 448
    panel_size = 245
    gap = 48
    left = 78
    right = 34
    top_margin = 105
    bottom_margin = 98
    fig, axes = plt.subplots(
        1,
        len(MODEL_ORDER),
        figsize=(canvas_width / 72.0, canvas_height / 72.0),
        constrained_layout=False,
    )
    fig.set_layout_engine(None)

    for ax_index, (ax, model) in enumerate(zip(axes, MODEL_ORDER)):
        model_points = points_by_model.get(model, [])
        ax.plot([axis_min, axis_max], [axis_min, axis_max], color="#808080", linestyle="--", linewidth=1.1)
        color = MODEL_COLORS.get(model, "#7f7f7f")
        for point in model_points:
            if not is_finite_point(point):
                continue
            reproduces = point.empirical_violation
            ax.scatter(
                [point.theory_magnitude],
                [point.empirical_magnitude],
                marker="o",
                s=50 if reproduces else 66,
                facecolor=color if reproduces else "#ffffff",
                edgecolor="#000000" if reproduces else color,
                linewidth=0.65 if reproduces else 1.1,
                alpha=0.82 if reproduces else 1.0,
                zorder=3,
            )
            if not reproduces:
                x = point.theory_magnitude
                y = point.empirical_magnitude
                ax.plot([x - 0.018, x + 0.018], [y - 0.018, y + 0.018], color=color, linewidth=1.1, zorder=4)
                ax.plot([x - 0.018, x + 0.018], [y + 0.018, y - 0.018], color=color, linewidth=1.1, zorder=4)

        ax.set_xlim(axis_min, axis_max)
        ax.set_ylim(axis_min, axis_max)
        ax.set_xticks(ticks)
        ax.set_yticks(ticks)
        ax.set_xticklabels([nice_tick_label(tick) for tick in ticks])
        ax.set_yticklabels([nice_tick_label(tick) for tick in ticks])
        ax.set_aspect("equal", adjustable="box")
        ax.grid(True, color="#d9d9d9", linewidth=0.8, alpha=0.65)
        ax.set_title(model, fontsize=15, loc="left", pad=36)
        if model_points:
            finite_points = [point for point in model_points if is_finite_point(point)]
            xs = [point.theory_magnitude for point in finite_points]
            ys = [point.empirical_magnitude for point in finite_points]
            matches = sum(point.empirical_violation for point in finite_points)
            abs_errors = [point.abs_error for point in finite_points]
            mae = statistics.mean(abs_errors) if abs_errors else float("nan")
            sd_abs_error = statistics.pstdev(abs_errors) if len(abs_errors) > 1 else float("nan")
            corr = correlation(xs, ys)
            summary = (
                f"{matches}/{len(finite_points)} empirical >= 0.01\n"
                f"r={format_stat(corr)}; MAE={format_stat(mae)}; SD|err|={format_stat(sd_abs_error)}"
            )
        else:
            summary = "No empirical rows"
            ax.text(
                0.5,
                0.5,
                "no rows",
                transform=ax.transAxes,
                fontsize=18,
                color="#666666",
                ha="center",
                va="center",
            )
        ax.text(0.0, 1.04, summary, transform=ax.transAxes, fontsize=11, ha="left", va="bottom")
        ax.set_xlabel(x_axis_label, fontsize=13, labelpad=10)
        if ax_index == 0:
            ax.set_ylabel("Nash-MD-trained commutativity magnitude", fontsize=13, labelpad=10)
        else:
            ax.set_ylabel("")
        ax.tick_params(labelsize=10)

    legend_handles = [
        Line2D(
            [0],
            [0],
            marker="o",
            color="none",
            label="Empirical magnitude >= 0.01",
            markerfacecolor="#7f7f7f",
            markeredgecolor="#000000",
            markersize=7,
        ),
        Line2D(
            [0],
            [0],
            marker="o",
            color="#7f7f7f",
            label="Empirical magnitude < 0.01",
            markerfacecolor="#ffffff",
            markeredgecolor="#7f7f7f",
            markersize=8,
            linestyle="None",
        ),
    ]
    fig.legend(handles=legend_handles, loc="lower left", bbox_to_anchor=(left / canvas_width, 0.02), ncol=2, frameon=False, fontsize=11)
    fig.suptitle(title, fontsize=20, y=1.0 - 34 / canvas_height)
    fig.subplots_adjust(
        left=left / canvas_width,
        right=(canvas_width - right) / canvas_width,
        top=(canvas_height - top_margin) / canvas_height,
        bottom=bottom_margin / canvas_height,
        wspace=gap / panel_size,
    )

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output)
    if pdf_output is not None:
        pdf_output.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(pdf_output)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--pdf-output", type=Path, default=None)
    parser.add_argument("--plot-data-output", type=Path, default=None)
    parser.add_argument("--no-pdf", action="store_true")
    args = parser.parse_args()

    args.output = args.output or DEFAULT_OUTPUT
    args.pdf_output = args.pdf_output or DEFAULT_PDF_OUTPUT
    args.plot_data_output = args.plot_data_output or DEFAULT_PLOT_DATA

    points_by_model = {spec.label: load_points(spec) for spec in DEFAULT_MODELS}
    write_plot_data(args.plot_data_output, points_by_model)
    render(
        points_by_model,
        args.output,
        None if args.no_pdf else args.pdf_output,
        x_axis_label="NLHF-predicted commutativity magnitude",
        title="NLHF vs. Nash-MD: commutativity violations",
    )
    print(f"wrote {args.output}")
    if not args.no_pdf:
        print(f"wrote {args.pdf_output}")
    print(f"wrote {args.plot_data_output}")
    for model in MODEL_ORDER:
        points = points_by_model.get(model, [])
        if points:
            empirical = sum(point.empirical_violation for point in points)
            print(f"{model}: rows={len(points)} empirical_violations={empirical}")
        else:
            print(f"{model}: rows=0")


if __name__ == "__main__":
    main()
