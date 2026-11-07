#!/usr/bin/env python3
"""Plot the four-panel violation-frequency figure used in the paper."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


DEFAULT_CONDITIONED_INPUT = Path(
    "results/theory/frequency_figure_data/"
    "violation_frequency_conditioned_theory_change_ge_0p01_min_effect_0p01.csv"
)
DEFAULT_COMMUTATIVITY_INPUT = Path(
    "results/theory/frequency_figure_data/nlhf_commutativity_frequency_min_effect_0p01.csv"
)
DEFAULT_OUTPUT = Path("paper/figures/violation_frequency_four_panel_min_effect_0p01.png")
DEFAULT_SVG_OUTPUT = Path("paper/figures/violation_frequency_four_panel_min_effect_0p01.svg")
DEFAULT_PDF_OUTPUT = Path("paper/figures/violation_frequency_four_panel_min_effect_0p01.pdf")
DEFAULT_PLOT_DATA = Path("results/theory/commutativity_figure_outputs/violation_frequency_four_panel_min_effect_0p01_plot_data.csv")

MODEL_ORDER = ["Nemo", "Qwen2.5", "Qwen3"]
MODEL_COLORS = {
    "Nemo": "#1f77b4",
    "Qwen2.5": "#d62728",
    "Qwen3": "#2ca02c",
}

PANELS = [
    {
        "key": "NLHF Monotonicity Violation",
        "title": "NLHF Monotonicity Violation",
        "param_name": "tau",
        "source": "conditioned",
    },
    {
        "key": "NLHF Involvement Violation",
        "title": "NLHF Involvement Violation",
        "param_name": "tau",
        "source": "conditioned",
    },
    {
        "key": "RTBT Involvement Violation",
        "title": "RTBT Involvement Violation",
        "param_name": "beta",
        "source": "conditioned",
    },
    {
        "key": "NLHF Commutativity Violation Lower Bound",
        "title": "NLHF Commutativity Violation Lower Bound",
        "param_name": "tau",
        "source": "commutativity",
    },
]


def load_conditioned_rows(path: Path) -> list[dict]:
    rows: list[dict] = []
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            rows.append(
                {
                    "panel": row["panel"],
                    "model": row["model"],
                    "param_name": row["param_name"],
                    "param_value": float(row["param_value"]),
                    "profiles_denominator": int(row["profiles_eligible"]),
                    "profiles_with_witness": int(row["profiles_with_witness"]),
                    "percent_with_witness": float(row["percent_with_witness"]),
                    "condition": "sensitive to a single voter at threshold 0.01",
                }
            )
    return rows


def load_commutativity_rows(path: Path) -> list[dict]:
    rows: list[dict] = []
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            rows.append(
                {
                    "panel": "NLHF Commutativity Violation Lower Bound",
                    "model": row["model"],
                    "param_name": row["param_name"],
                    "param_value": float(row["param_value"]),
                    "profiles_denominator": int(row["profiles_total"]),
                    "profiles_with_witness": int(row["profiles_with_witness"]),
                    "percent_with_witness": float(row["percent_with_witness"]),
                    "condition": "unconditioned lower bound",
                }
            )
    return rows


def write_plot_data(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "panel",
                "model",
                "param_name",
                "param_value",
                "profiles_denominator",
                "profiles_with_witness",
                "percent_with_witness",
                "condition",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)


def plot_rows(rows: list[dict], output: Path, svg_output: Path | None, pdf_output: Path | None, title: str | None = None) -> None:
    fig, axes = plt.subplots(2, 2, figsize=(8.8, 6.1), constrained_layout=True)
    axes_flat = axes.ravel()

    for ax, panel in zip(axes_flat, PANELS):
        panel_rows = [row for row in rows if row["panel"] == panel["key"]]
        panel_max = 0.0
        for model in MODEL_ORDER:
            subset = [row for row in panel_rows if row["model"] == model]
            subset.sort(key=lambda row: row["param_value"])
            if not subset:
                continue
            xs = [row["param_value"] for row in subset]
            ys = [row["percent_with_witness"] for row in subset]
            panel_max = max(panel_max, max(ys))
            (line,) = ax.plot(
                xs,
                ys,
                marker="o",
                linewidth=1.8,
                markersize=4.2,
                color=MODEL_COLORS[model],
                label=model,
            )

        ax.set_xscale("log")
        ax.set_xlabel(panel["param_name"])
        ax.set_ylabel("% of profiles")
        ax.set_title(panel["title"], fontsize=10.5)
        ax.grid(True, alpha=0.28)
        ax.set_ylim(0.0, panel_max + max(0.35, 0.08 * panel_max))

    axes_flat[0].legend(frameon=False, loc="upper right")
    if title:
        fig.suptitle(title, fontsize=11)
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=220, bbox_inches="tight")
    if svg_output is not None:
        fig.savefig(svg_output, bbox_inches="tight")
    if pdf_output is not None:
        fig.savefig(pdf_output, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--conditioned-input", type=Path, default=DEFAULT_CONDITIONED_INPUT)
    parser.add_argument("--commutativity-input", type=Path, default=DEFAULT_COMMUTATIVITY_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--svg-output", type=Path, default=DEFAULT_SVG_OUTPUT)
    parser.add_argument("--pdf-output", type=Path, default=DEFAULT_PDF_OUTPUT)
    parser.add_argument("--plot-data-output", type=Path, default=DEFAULT_PLOT_DATA)
    parser.add_argument("--title", type=str, default=r"Violations conditional on $\geq 0.01$")
    parser.add_argument("--no-svg", action="store_true")
    parser.add_argument("--no-pdf", action="store_true")
    args = parser.parse_args()

    rows = load_conditioned_rows(args.conditioned_input) + load_commutativity_rows(args.commutativity_input)
    write_plot_data(args.plot_data_output, rows)
    plot_rows(
        rows,
        args.output,
        None if args.no_svg else args.svg_output,
        None if args.no_pdf else args.pdf_output,
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
