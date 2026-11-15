#!/usr/bin/env python3
"""Plot how strongly NLHF/RTBT move the reference distribution."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from scripts.theory.nlhf_tie_normalization import load_cases_tie_norm, solve_nlhf_tie_norm
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases as load_rtbt_cases
from scripts.theory.search_model_reference_violation_counts import load_rho_cache as load_rtbt_rho_cache
from scripts.theory.search_model_reference_violation_counts import rho_for_case as rtbt_rho_for_case
from scripts.theory.search_nlhf_tie_normalization_examples import ReferenceConfig, load_rho_cache, rho_for_case
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda
from scripts.theory.sweep_nlhf_tie_normalization_parameters import DEFAULT_NLHF_TAUS, DEFAULT_RTBT_BETAS


MODEL_STYLES = {
    "nemo_base_strip_identity": {"label": "Nemo", "color": "#1f77b4"},
    "qwen25_base_strip_identity": {"label": "Qwen2.5", "color": "#d62728"},
    "qwen3_base_strip_identity": {"label": "Qwen3", "color": "#2ca02c"},
}


def parse_float_list(text: str) -> list[float]:
    return [float(part.strip()) for part in text.split(",") if part.strip()]


def tv_distance(p: np.ndarray, q: np.ndarray) -> float:
    return 0.5 * float(np.sum(np.abs(p - q)))


def summarize(values: list[float], frac_threshold: float) -> dict[str, float]:
    arr = np.asarray(values, dtype=float)
    return {
        "n_profiles": int(arr.size),
        "mean_tv": float(np.mean(arr)),
        "median_tv": float(np.median(arr)),
        "p90_tv": float(np.quantile(arr, 0.9)),
        "max_tv": float(np.max(arr)),
        "frac_tv_ge_threshold": float(np.mean(arr >= frac_threshold)),
        "percent_tv_ge_threshold": 100.0 * float(np.mean(arr >= frac_threshold)),
    }


def compute_rows(
    dataset: Path,
    nlhf_taus: list[float],
    rtbt_betas: list[float],
    frac_threshold: float,
    nemo_rho_cache: Path,
    qwen25_rho_cache: Path,
    qwen3_rho_cache: Path,
) -> list[dict]:
    nlhf_cases = load_cases_tie_norm(dataset, ["world", "personal"])
    rtbt_cases = load_rtbt_cases(dataset, ["world", "personal"])

    refs = [
        ReferenceConfig("nemo_base_strip_identity", nemo_rho_cache),
        ReferenceConfig("qwen25_base_strip_identity", qwen25_rho_cache),
        ReferenceConfig("qwen3_base_strip_identity", qwen3_rho_cache),
    ]

    rows: list[dict] = []
    for ref in refs:
        nlhf_cache = load_rho_cache(ref.rho_cache)
        rtbt_cache = load_rtbt_rho_cache(ref.rho_cache)

        for tau in nlhf_taus:
            values: list[float] = []
            for case in nlhf_cases:
                try:
                    rho, _ = rho_for_case(case, ref, nlhf_cache)
                except KeyError:
                    continue
                theory = solve_nlhf_tie_norm(
                    tau,
                    np.asarray(case.total_wins, dtype=float),
                    np.asarray(case.total_ties, dtype=float),
                    rho,
                )
                if theory is None:
                    continue
                values.append(tv_distance(theory, rho))
            if values:
                row = {
                    "model_alias": ref.name,
                    "rule": "nlhf_tie_norm",
                    "param_name": "tau",
                    "param_value": tau,
                    "frac_threshold": frac_threshold,
                }
                row.update(summarize(values, frac_threshold))
                rows.append(row)

        for beta in rtbt_betas:
            values = []
            for case in rtbt_cases:
                record = rtbt_cache.get(case.prompt_id)
                if record is None:
                    continue
                rho = rtbt_rho_for_case(case, record)
                theory = solve_weighted_logistic_borda(
                    beta,
                    np.asarray(case.total_wins, dtype=float),
                    rho,
                )
                if theory is None:
                    continue
                values.append(tv_distance(theory, rho))
            if values:
                row = {
                    "model_alias": ref.name,
                    "rule": "rtbt",
                    "param_name": "beta",
                    "param_value": beta,
                    "frac_threshold": frac_threshold,
                }
                row.update(summarize(values, frac_threshold))
                rows.append(row)
    return rows


def write_rows(rows: list[dict], csv_path: Path, json_path: Path) -> None:
    with csv_path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    with json_path.open("w") as handle:
        json.dump(rows, handle, indent=2)
        handle.write("\n")


def plot_rows(
    rows: list[dict],
    output: Path,
    svg_output: Path | None,
    pdf_output: Path | None,
    frac_threshold: float,
) -> None:
    fig, axes = plt.subplots(2, 2, figsize=(12, 7.5), constrained_layout=True)
    panels = [
        ("nlhf_tie_norm", "mean_tv", rf"NLHF Mean $\mathrm{{TV}}(\rho, F(\mathbf{{R}},\rho))$", "tau"),
        ("rtbt", "mean_tv", rf"RTBT Mean $\mathrm{{TV}}(\rho, F(\mathbf{{R}},\rho))$", "beta"),
        ("nlhf_tie_norm", "percent_tv_ge_threshold", rf"NLHF Profiles with $\mathrm{{TV}} \geq {frac_threshold:g}$", "tau"),
        ("rtbt", "percent_tv_ge_threshold", rf"RTBT Profiles with $\mathrm{{TV}} \geq {frac_threshold:g}$", "beta"),
    ]

    for ax, (rule, metric, title, xlabel) in zip(axes.flat, panels):
        panel_max = 0.0
        for model_alias, style in MODEL_STYLES.items():
            subset = [
                row for row in rows if row["model_alias"] == model_alias and row["rule"] == rule
            ]
            subset.sort(key=lambda row: float(row["param_value"]))
            if not subset:
                continue
            xs = [float(row["param_value"]) for row in subset]
            ys = [float(row[metric]) for row in subset]
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
        ax.set_title(title, fontsize=11)
        ax.set_xlabel(xlabel)
        ax.grid(True, alpha=0.3)
        ax.set_ylim(0.0, panel_max + max(0.02, 0.08 * panel_max))
    axes[0, 0].set_ylabel("mean TV")
    axes[1, 0].set_ylabel("% of CoVal profiles")
    axes[0, 0].legend(frameon=False, loc="best")

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, dpi=220, bbox_inches="tight")
    if svg_output is not None:
        fig.savefig(svg_output, bbox_inches="tight")
    if pdf_output is not None:
        fig.savefig(pdf_output, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--output-dir", type=Path, default=Path("results/theory/reference_update_size_sweeps"))
    parser.add_argument("--nlhf-taus", type=parse_float_list, default=DEFAULT_NLHF_TAUS)
    parser.add_argument("--rtbt-betas", type=parse_float_list, default=DEFAULT_RTBT_BETAS)
    parser.add_argument("--frac-threshold", type=float, default=0.01)
    parser.add_argument("--nemo-rho-cache", type=Path, default=Path("results/reference_distributions/nemo_pytorch_rho_strip_identity_float32.jsonl"))
    parser.add_argument("--qwen25-rho-cache", type=Path, default=Path("results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl"))
    parser.add_argument("--qwen3-rho-cache", type=Path, default=Path("results/reference_distributions/qwen3_pytorch_rho_strip_identity.jsonl"))
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows = compute_rows(
        args.dataset,
        args.nlhf_taus,
        args.rtbt_betas,
        args.frac_threshold,
        args.nemo_rho_cache,
        args.qwen25_rho_cache,
        args.qwen3_rho_cache,
    )
    csv_path = args.output_dir / "reference_update_size_sweeps.csv"
    json_path = args.output_dir / "reference_update_size_sweeps.json"
    png_path = args.output_dir / "reference_update_size_sweeps.png"
    svg_path = args.output_dir / "reference_update_size_sweeps.svg"
    pdf_path = args.output_dir / "reference_update_size_sweeps.pdf"
    write_rows(rows, csv_path, json_path)
    plot_rows(rows, png_path, svg_path, pdf_path, args.frac_threshold)
    print(f"Wrote {csv_path}")
    print(f"Wrote {json_path}")
    print(f"Wrote {png_path}")
    print(f"Wrote {svg_path}")
    print(f"Wrote {pdf_path}")


if __name__ == "__main__":
    main()
