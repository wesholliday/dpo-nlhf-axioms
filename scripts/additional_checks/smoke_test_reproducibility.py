#!/usr/bin/env python3
"""Fast local smoke checks for the reproducibility package."""

from __future__ import annotations

import csv
import sys
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.theory.nlhf_tie_normalization import solve_nlhf_tie_norm


REQUIRED_SUMMARY_COLUMNS = {
    "case_key",
    "duration_seconds",
    "tv_to_theory",
    "tv_theory_to_reference",
    "max_abs_error",
    "reference_top",
    "theory_top",
    "final_top",
    "theory_available",
    "error",
}


def check_nlhf_zero_margin() -> None:
    wins = np.zeros((3, 3), dtype=float)
    ties = np.zeros((3, 3), dtype=float)
    rho = np.array([0.2, 0.3, 0.5], dtype=float)
    pi = solve_nlhf_tie_norm(tau=0.01, wins=wins, ties=ties, rho=rho)
    if pi is None:
        raise AssertionError("NLHF solver returned None on zero-margin instance")
    if not np.allclose(pi, rho, atol=1e-10):
        raise AssertionError(f"zero-margin NLHF should equal rho, got {pi}")


def check_summary_csv(path: Path) -> None:
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        missing = REQUIRED_SUMMARY_COLUMNS.difference(reader.fieldnames or [])
        if missing:
            raise AssertionError(f"{path} missing columns: {sorted(missing)}")
        rows = list(reader)
    if not rows:
        raise AssertionError(f"{path} has no data rows")
    numeric_columns = ["tv_to_theory", "tv_theory_to_reference", "max_abs_error"]
    for row in rows:
        for column in numeric_columns:
            value = row.get(column, "")
            if value:
                float(value)


def main() -> None:
    check_nlhf_zero_margin()
    summary_paths = sorted(Path("results/empirical").glob("*/filtered_profile_sweeps/*_summary.csv"))
    if not summary_paths:
        raise AssertionError("No empirical summary CSV files found")
    for path in summary_paths:
        check_summary_csv(path)
    print(f"smoke checks passed: {len(summary_paths)} summary CSV files")


if __name__ == "__main__":
    main()
