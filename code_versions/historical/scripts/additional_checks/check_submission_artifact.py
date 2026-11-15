#!/usr/bin/env python3
"""Lightweight pre-submission checks for the supplementary artifact.

This script intentionally avoids GPU/model-loading work.  It checks that the
curated data files parse, key paper counts match the included CoVal data, paper
figure PDFs are present, and the fast smoke test passes.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.coval.profiles import load_cases_tie_norm
from scripts.theory.count_rtbt_domain_profiles import (
    iter_profile_counts,
    strongly_connected,
)


EXPECTED_COVAL_PROFILES = 1399
EXPECTED_RTBT_DOMAIN_PROFILES = 1320
EXPECTED_PAPER_FIGURES = {
    "commutativity_magnitude_tau0p01_min_effect_0p01_boxplot.pdf",
    "effect_size_conditional_ge_0p01_and_theory_change_ge_0p01_boxplot.pdf",
    "filtered_nemo_dpo_bubble_agreement.pdf",
    "filtered_nemo_nlhf_bubble_agreement.pdf",
    "filtered_qwen25_dpo_bubble_agreement.pdf",
    "filtered_qwen25_nlhf_bubble_agreement.pdf",
    "filtered_qwen3_dpo_bubble_agreement.pdf",
    "filtered_qwen3_nlhf_bubble_agreement.pdf",
    "joint_qwen25_dpo_bubble_agreement.pdf",
    "nlhf_commutativity_single_profile_nashmd_agreement.pdf",
    "nontrivial_reference_update_frequency.pdf",
    "rtbt_involvement_single_profile_dpo_agreement.pdf",
    "temperature_2_commutativity_magnitude_tau0p01_min_effect_0p01_boxplot.pdf",
    "temperature_2_effect_size_conditional_ge_0p01_and_theory_change_ge_0p01_boxplot.pdf",
    "temperature_2_violation_frequency_four_panel_min_effect_0p01.pdf",
    "violation_frequency_four_panel_min_effect_0p01.pdf",
    "violation_frequency_unconditioned_three_panel_min_effect_0p01.pdf",
}


def parse_json_file(path: Path) -> None:
    with path.open() as handle:
        json.load(handle)


def parse_jsonl_file(path: Path) -> None:
    with path.open() as handle:
        for line_number, line in enumerate(handle, start=1):
            if line.strip():
                try:
                    json.loads(line)
                except json.JSONDecodeError as exc:
                    raise AssertionError(f"{path}:{line_number}: {exc}") from exc


def parse_csv_file(path: Path) -> None:
    with path.open(newline="") as handle:
        reader = csv.reader(handle)
        next(reader, None)
        for _row in reader:
            pass


def check_curated_results_parse() -> tuple[int, int, int]:
    json_count = jsonl_count = csv_count = 0
    for path in sorted((REPO_ROOT / "results").rglob("*")):
        if not path.is_file():
            continue
        if path.suffix == ".json":
            parse_json_file(path)
            json_count += 1
        elif path.suffix == ".jsonl":
            parse_jsonl_file(path)
            jsonl_count += 1
        elif path.suffix == ".csv":
            parse_csv_file(path)
            csv_count += 1
    return json_count, jsonl_count, csv_count


def check_coval_counts() -> None:
    cases = load_cases_tie_norm(REPO_ROOT / "data/coval_comparisons.jsonl", ["world", "personal"])
    if len(cases) != EXPECTED_COVAL_PROFILES:
        raise AssertionError(f"expected {EXPECTED_COVAL_PROFILES} CoVal profiles, got {len(cases)}")

    profiles = list(
        iter_profile_counts(REPO_ROOT / "data/coval_comparisons.jsonl", ["world", "personal"])
    )
    rtbt_domain_count = sum(1 for profile in profiles if strongly_connected(profile.counts))
    if rtbt_domain_count != EXPECTED_RTBT_DOMAIN_PROFILES:
        raise AssertionError(
            f"expected {EXPECTED_RTBT_DOMAIN_PROFILES} RTBT-domain profiles, got {rtbt_domain_count}"
        )


def check_paper_figures() -> int:
    main_tex = REPO_ROOT / "paper/main.tex"
    if main_tex.exists():
        figure_names = sorted(
            set(re.findall(r"\\includegraphics(?:\[[^\]]*\])?\{figures/([^}]+)\}", main_tex.read_text()))
        )
    else:
        figure_names = sorted(EXPECTED_PAPER_FIGURES)
    missing = [name for name in figure_names if not (REPO_ROOT / "paper/figures" / name).exists()]
    if missing:
        raise AssertionError(f"paper references missing figures: {missing}")
    return len(figure_names)


def check_reference_cache_lengths() -> None:
    expected_rows = {
        "qwen25_pytorch_rho_strip_identity.jsonl": 1078,
        "qwen3_pytorch_rho_strip_identity.jsonl": 1078,
        "nemo_pytorch_rho_strip_identity_float32.jsonl": 1078,
    }
    base = REPO_ROOT / "results/reference_distributions"
    for filename, expected in expected_rows.items():
        path = base / filename
        rows = sum(1 for _ in path.open())
        if rows != expected:
            raise AssertionError(f"{path} has {rows} rows, expected {expected}")


def run_smoke_test() -> None:
    subprocess.run(
        [sys.executable, "-m", "scripts.additional_checks.smoke_test_reproducibility"],
        cwd=REPO_ROOT,
        check=True,
    )


def run_lean_check_if_requested(run_lean: bool) -> None:
    if not run_lean:
        return
    subprocess.run(["scripts/check_artifact.sh"], cwd=REPO_ROOT / "formalization", check=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--run-lean",
        action="store_true",
        help="Also run formalization/scripts/check_artifact.sh; requires Lake/Lean.",
    )
    args = parser.parse_args()

    json_count, jsonl_count, csv_count = check_curated_results_parse()
    check_coval_counts()
    check_reference_cache_lengths()
    figure_count = check_paper_figures()
    run_smoke_test()
    run_lean_check_if_requested(args.run_lean)

    print(
        "artifact checks passed: "
        f"{json_count} JSON, {jsonl_count} JSONL, {csv_count} CSV files; "
        f"{figure_count} paper figures"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
