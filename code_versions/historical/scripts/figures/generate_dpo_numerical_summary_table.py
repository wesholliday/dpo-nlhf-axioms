#!/usr/bin/env python3
"""Generate the DPO numerical summary table from filtered sweep JSONL files."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


DEFAULT_INPUT_DIR = Path("results/empirical/dpo_rtbt/filtered_profile_sweeps")
DEFAULT_OUTPUT = Path("results/empirical/dpo_rtbt/filtered_profile_sweeps/dpo_numerical_summary_table.tex")

MODELS = [
    ("Qwen2.5", "qwen25.jsonl"),
    ("Qwen3", "qwen3.jsonl"),
    ("Mistral-Nemo-Base-2407", "nemo.jsonl"),
]


def load_jsonl(path: Path) -> list[dict]:
    with path.open() as handle:
        return [json.loads(line) for line in handle if line.strip()]


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    if not ordered:
        raise ValueError("Cannot take percentile of empty list")
    k = (len(ordered) - 1) * q
    lo = math.floor(k)
    hi = math.ceil(k)
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - k) + ordered[hi] * (k - lo)


def top_candidate(probs: dict[str, float]) -> str:
    return max(probs, key=lambda label: float(probs[label]))


def format_scientific(value: float) -> str:
    if value == 0:
        return "$0$"
    exponent = math.floor(math.log10(abs(value)))
    mantissa = value / (10**exponent)
    return rf"${mantissa:.2f}\cdot 10^{{{exponent}}}$"


def summarize(path: Path) -> dict[str, float | int]:
    rows = load_jsonl(path)
    tvs = [float(row["tv_to_theory"]) for row in rows]
    top1 = sum(
        1
        for row in rows
        if top_candidate(row["theoretical_probs"]) == top_candidate(row["final_probs"])
    )
    return {
        "n": len(rows),
        "median_tv": percentile(tvs, 0.5),
        "mean_tv": sum(tvs) / len(tvs),
        "p90_tv": percentile(tvs, 0.9),
        "top1": top1,
    }


def render_table(input_dir: Path) -> str:
    lines = [
        r"\begin{table}[h!]",
        r"\centering",
        r"\small",
        r"\begin{tabular}{lrrrrr}",
        r"\hline",
        r"Model & $n$ & Median TV & Mean TV & 90th pct. TV & Top-1 agreement \\",
        r"\hline",
    ]
    for model_name, filename in MODELS:
        stats = summarize(input_dir / filename)
        n = int(stats["n"])
        top1 = int(stats["top1"])
        lines.append(
            f"{model_name} & {n} & "
            f"{format_scientific(float(stats['median_tv']))} & "
            f"{format_scientific(float(stats['mean_tv']))} & "
            f"{format_scientific(float(stats['p90_tv']))} & "
            f"{top1}/{n} \\\\"
        )
    lines.extend(
        [
            r"\hline",
            r"\end{tabular}",
            r"\vspace{1em}",
            (
                r"\caption{Summary of DPO sweeps over the $n$ profiles $\mathbf{R}$ "
                r"for which $\mathrm{TV}(\mathrm{RTBT}_{0.1}(\mathbf{R},\rho),\rho)"
                r"\geq 0.01$. TV denotes "
                r"$\mathrm{TV}(\pi,\mathrm{RTBT}_{0.1}(\mathbf{R},\rho))$, where "
                r"$\pi$ is the distribution of the DPO-trained model. Top-1 agreement "
                r"occurs when $\mathrm{RTBT}_{0.1}(\mathbf{R},\rho)$ and $\pi$ assign "
                r"maximum probability to the same candidate.}"
            ),
            r"\label{dpo-numerical-summary}",
            r"\end{table}",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input-dir", type=Path, default=DEFAULT_INPUT_DIR)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    table = render_table(args.input_dir)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(table)
    print(table)
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
