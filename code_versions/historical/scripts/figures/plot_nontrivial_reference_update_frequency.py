#!/usr/bin/env python3
"""Plot how often NLHF/RTBT nontrivially update model reference distributions."""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from scripts.figures.plot_reference_update_size_sweeps import (
    MODEL_STYLES,
    compute_rows,
    parse_float_list,
)
from scripts.theory.sweep_new_nlhf_tie_normalization_parameters import (
    DEFAULT_NLHF_TAUS,
    DEFAULT_RTBT_BETAS,
)


DEFAULT_OUTPUT = Path("paper/figures/nontrivial_reference_update_frequency.pdf")


def plot_rows(rows: list[dict], output: Path, threshold: float) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(8.8, 3.6), constrained_layout=True, sharey=True)
    panels = [
        ("nlhf_tie_norm", "tau", rf"NLHF: $\mathrm{{TV}}(\rho,F(\mathbf{{R}},\rho)) \geq {threshold:g}$"),
        ("rtbt", "beta", rf"RTBT: $\mathrm{{TV}}(\rho,F(\mathbf{{R}},\rho)) \geq {threshold:g}$"),
    ]

    for ax, (rule, xlabel, title) in zip(axes, panels):
        panel_max = 0.0
        for model_alias, style in MODEL_STYLES.items():
            subset = [
                row for row in rows if row["model_alias"] == model_alias and row["rule"] == rule
            ]
            subset.sort(key=lambda row: float(row["param_value"]))
            if not subset:
                continue
            xs = [float(row["param_value"]) for row in subset]
            ys = [float(row["percent_tv_ge_threshold"]) for row in subset]
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
        ax.set_xlabel(xlabel)
        ax.set_title(title, fontsize=10.5)
        ax.grid(True, alpha=0.3)
        ax.set_ylim(0.0, panel_max + max(2.0, 0.08 * panel_max))

    axes[0].set_ylabel("% of profiles")
    axes[0].legend(frameon=False, loc="best")
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--nlhf-taus", type=parse_float_list, default=DEFAULT_NLHF_TAUS)
    parser.add_argument("--rtbt-betas", type=parse_float_list, default=DEFAULT_RTBT_BETAS)
    parser.add_argument("--threshold", type=float, default=0.01)
    parser.add_argument(
        "--nemo-rho-cache",
        type=Path,
        default=Path("results/reference_distributions/nemo_pytorch_rho_strip_identity.jsonl"),
    )
    parser.add_argument(
        "--qwen25-rho-cache",
        type=Path,
        default=Path("results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl"),
    )
    parser.add_argument(
        "--qwen3-rho-cache",
        type=Path,
        default=Path("results/reference_distributions/qwen3_pytorch_rho_strip_identity.jsonl"),
    )
    args = parser.parse_args()

    rows = compute_rows(
        args.dataset,
        args.nlhf_taus,
        args.rtbt_betas,
        args.threshold,
        args.nemo_rho_cache,
        args.qwen25_rho_cache,
        args.qwen3_rho_cache,
    )
    plot_rows(rows, args.output, args.threshold)
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
