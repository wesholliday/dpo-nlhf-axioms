#!/usr/bin/env python3
"""Generate LaTeX tables for the frequency data underlying Figure FreqFig.

The paper currently contains these tables inline.  This script is retained so
the pasted table entries can be regenerated from the curated CSV data.
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path


DEFAULT_INPUT = Path(
    "results/theory/frequency_figure_data/"
    "violation_frequency_conditioned_theory_change_ge_0p01_min_effect_0p01.csv"
)
DEFAULT_UNCONDITIONED_INPUT = Path("results/theory/frequency_figure_data/profile_conditioned_summary.csv")
DEFAULT_OUTPUT = Path("results/theory/frequency_figure_data/freqfig_nlhf_frequency_table.tex")
DEFAULT_UNCONDITIONED_OUTPUT = Path(
    "results/theory/frequency_figure_data/freqfig_nlhf_frequency_unconditioned_table.tex"
)
DEFAULT_RTBT_OUTPUT = Path("results/theory/frequency_figure_data/freqfig_rtbt_frequency_table.tex")
DEFAULT_RTBT_UNCONDITIONED_OUTPUT = Path(
    "results/theory/frequency_figure_data/freqfig_rtbt_frequency_unconditioned_table.tex"
)

MODEL_ORDER = ["Nemo", "Qwen2.5", "Qwen3"]
TAU_ORDER = [0.0005, 0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5]
BETA_ORDER = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0]
RTBT_DOMAIN_PROFILES = 1320
PANEL_TO_AXIOM = {
    "NLHF Monotonicity Violation": "Monotonicity",
    "NLHF Involvement Violation": "Involvement",
}


def fmt_tau(value: float) -> str:
    text = f"{value:g}"
    if text.startswith("0."):
        return "." + text[2:]
    return text


def fmt_percent(value: float) -> str:
    return f"{value:.2f}"


def load_nlhf_rows(path: Path) -> dict[tuple[str, str, float], dict]:
    out: dict[tuple[str, str, float], dict] = {}
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            panel = row["panel"]
            if panel not in PANEL_TO_AXIOM:
                continue
            if row["param_name"] != "tau":
                continue
            key = (PANEL_TO_AXIOM[panel], row["model"], float(row["param_value"]))
            out[key] = {
                "witnesses": int(row["profiles_with_witness"]),
                "denominator": int(row["profiles_eligible"]),
                "percent": float(row["percent_with_witness"]),
            }
    return out


def load_unconditioned_nlhf_rows(path: Path) -> dict[tuple[str, str, float], dict]:
    out: dict[tuple[str, str, float], dict] = {}
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            if row["condition"] != "all":
                continue
            if row["source"] != "single_voter":
                continue
            if row["threshold"] != "0.01":
                continue
            if row["rule"] != "nlhf_tie_norm":
                continue
            if row["axiom"] not in {"monotonicity", "involvement"}:
                continue
            key = (row["axiom"].capitalize(), row["model_alias"], float(row["param_value"]))
            out[key] = {
                "witnesses": int(row["profiles_with_witness"]),
                "denominator": int(row["profiles_total"]),
                "percent": float(row["percent_with_witness"]),
            }
    alias_to_model = {
        "nemo_base_strip_identity": "Nemo",
        "qwen25_base_strip_identity": "Qwen2.5",
        "qwen3_base_strip_identity": "Qwen3",
    }
    return {
        (axiom, alias_to_model[model_alias], tau): value
        for (axiom, model_alias, tau), value in out.items()
    }


def load_rtbt_rows(path: Path) -> dict[tuple[str, str, float], dict]:
    out: dict[tuple[str, str, float], dict] = {}
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            if row["panel"] != "RTBT Involvement Violation":
                continue
            if row["param_name"] != "beta":
                continue
            key = ("Involvement", row["model"], float(row["param_value"]))
            out[key] = {
                "witnesses": int(row["profiles_with_witness"]),
                "denominator": int(row["profiles_eligible"]),
                "percent": float(row["percent_with_witness"]),
            }
    return out


def load_unconditioned_rtbt_rows(path: Path) -> dict[tuple[str, str, float], dict]:
    out: dict[tuple[str, str, float], dict] = {}
    alias_to_model = {
        "nemo_base_strip_identity": "Nemo",
        "qwen25_base_strip_identity": "Qwen2.5",
        "qwen3_base_strip_identity": "Qwen3",
    }
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            if row["condition"] != "all":
                continue
            if row["source"] != "single_voter":
                continue
            if row["threshold"] != "0.01":
                continue
            if row["rule"] != "rtbt":
                continue
            if row["axiom"] != "involvement":
                continue
            key = ("Involvement", alias_to_model[row["model_alias"]], float(row["param_value"]))
            witnesses = int(row["profiles_with_witness"])
            out[key] = {
                "witnesses": witnesses,
                "denominator": RTBT_DOMAIN_PROFILES,
                "percent": 100.0 * witnesses / RTBT_DOMAIN_PROFILES,
            }
    return out


def render_table(
    rows: dict[tuple[str, str, float], dict],
    *,
    param_name: str,
    param_order: list[float],
    axiom_order: list[str],
    caption: str,
    label: str,
) -> str:
    lines = [
        r"\begin{table}[h!]",
        r"\centering",
        r"\scriptsize",
        r"\setlength{\tabcolsep}{3pt}",
        r"\resizebox{\textwidth}{!}{%",
        r"\begin{tabular}{llcccccccccc}",
        r"\hline",
        r"Axiom & Model & "
        + " & ".join([rf"${param_name}={fmt_tau(param)}$" for param in param_order])
        + r" \\",
        r"\hline",
    ]
    for index, axiom in enumerate(axiom_order):
        for model in MODEL_ORDER:
            cells = []
            for param in param_order:
                row = rows[(axiom, model, param)]
                cells.append(
                    f"{row['witnesses']}/{row['denominator']} ({fmt_percent(row['percent'])})"
                )
            lines.append(f"{axiom} & {model} & " + " & ".join(cells) + r" \\")
        if index < len(axiom_order) - 1:
            lines.append(r"\hline")
    lines.extend(
        [
            r"\hline",
            r"\end{tabular}%",
            r"}",
            r"\vspace{0.5em}",
            caption,
            rf"\label{{{label}}}",
            r"\end{table}",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--unconditioned-input", type=Path, default=DEFAULT_UNCONDITIONED_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--unconditioned-output", type=Path, default=DEFAULT_UNCONDITIONED_OUTPUT)
    parser.add_argument("--rtbt-output", type=Path, default=DEFAULT_RTBT_OUTPUT)
    parser.add_argument(
        "--rtbt-unconditioned-output",
        type=Path,
        default=DEFAULT_RTBT_UNCONDITIONED_OUTPUT,
    )
    args = parser.parse_args()

    rows = load_nlhf_rows(args.input)
    unconditioned_rows = load_unconditioned_nlhf_rows(args.unconditioned_input)
    rtbt_rows = load_rtbt_rows(args.input)
    unconditioned_rtbt_rows = load_unconditioned_rtbt_rows(args.unconditioned_input)
    missing = [
        (axiom, model, tau)
        for axiom in ["Monotonicity", "Involvement"]
        for model in MODEL_ORDER
        for tau in TAU_ORDER
        if (axiom, model, tau) not in rows
    ]
    if missing:
        raise SystemExit(f"Missing rows: {missing}")
    missing_unconditioned = [
        (axiom, model, tau)
        for axiom in ["Monotonicity", "Involvement"]
        for model in MODEL_ORDER
        for tau in TAU_ORDER
        if (axiom, model, tau) not in unconditioned_rows
    ]
    if missing_unconditioned:
        raise SystemExit(f"Missing unconditioned rows: {missing_unconditioned}")
    missing_rtbt = [
        (model, beta)
        for model in MODEL_ORDER
        for beta in BETA_ORDER
        if ("Involvement", model, beta) not in rtbt_rows
    ]
    if missing_rtbt:
        raise SystemExit(f"Missing RTBT rows: {missing_rtbt}")
    missing_unconditioned_rtbt = [
        (model, beta)
        for model in MODEL_ORDER
        for beta in BETA_ORDER
        if ("Involvement", model, beta) not in unconditioned_rtbt_rows
    ]
    if missing_unconditioned_rtbt:
        raise SystemExit(f"Missing unconditioned RTBT rows: {missing_unconditioned_rtbt}")

    table = render_table(
        rows,
        param_name=r"\tau",
        param_order=TAU_ORDER,
        axiom_order=["Monotonicity", "Involvement"],
        caption=(
            r"\caption{Data underlying the NLHF monotonicity and involvement panels of "
            r"Figure~\ref{FreqFig}. Each entry has the form witnesses/denominator "
            r"(percentage), where the denominator is the number of CoVal profiles "
            r"$\mathbf{R}$ that are sensitive to a single voter as defined in "
            r"Section~\ref{EmpiricEval}. The minimum violation magnitude is $0.01$.}"
        ),
        label="nlhf-frequency-data",
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(table)
    unconditioned_table = render_table(
        unconditioned_rows,
        param_name=r"\tau",
        param_order=TAU_ORDER,
        axiom_order=["Monotonicity", "Involvement"],
        caption=(
            r"\caption{Unconditioned version of Table~\ref{nlhf-frequency-data}. "
            r"Each entry has the form witnesses/1399 (percentage), where the denominator "
            r"is all CoVal profiles. The minimum violation magnitude is $0.01$.}"
        ),
        label="nlhf-frequency-data-unconditioned",
    )
    args.unconditioned_output.parent.mkdir(parents=True, exist_ok=True)
    args.unconditioned_output.write_text(unconditioned_table)
    rtbt_table = render_table(
        rtbt_rows,
        param_name=r"\beta",
        param_order=BETA_ORDER,
        axiom_order=["Involvement"],
        caption=(
            r"\caption{Data underlying the RTBT involvement panel of Figure~\ref{FreqFig}. "
            r"Each entry has the form witnesses/denominator (percentage), where the "
            r"denominator is the number of CoVal profiles $\mathbf{R}$ that are sensitive "
            r"to a single voter as defined in Section~\ref{EmpiricEval}. The minimum "
            r"violation magnitude is $0.01$.}"
        ),
        label="rtbt-frequency-data",
    )
    args.rtbt_output.parent.mkdir(parents=True, exist_ok=True)
    args.rtbt_output.write_text(rtbt_table)
    unconditioned_rtbt_table = render_table(
        unconditioned_rtbt_rows,
        param_name=r"\beta",
        param_order=BETA_ORDER,
        axiom_order=["Involvement"],
        caption=(
            r"\caption{Unconditioned version of Table~\ref{rtbt-frequency-data}. "
            r"Each entry has the form witnesses/1320 (percentage), where the denominator "
            r"is the number of CoVal profiles in the domain of RTBT. The minimum violation "
            r"magnitude is $0.01$.}"
        ),
        label="rtbt-frequency-data-unconditioned",
    )
    args.rtbt_unconditioned_output.parent.mkdir(parents=True, exist_ok=True)
    args.rtbt_unconditioned_output.write_text(unconditioned_rtbt_table)
    print(table)
    print(f"Wrote {args.output}")
    print(unconditioned_table)
    print(f"Wrote {args.unconditioned_output}")
    print(rtbt_table)
    print(f"Wrote {args.rtbt_output}")
    print(unconditioned_rtbt_table)
    print(f"Wrote {args.rtbt_unconditioned_output}")


if __name__ == "__main__":
    main()
