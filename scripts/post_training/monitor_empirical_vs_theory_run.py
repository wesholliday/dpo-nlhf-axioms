#!/usr/bin/env python3
"""Summarize a live empirical-vs-theory JSONL run.

Writes:
- a per-row CSV summary
- a compact machine-readable JSON summary
- a human-readable text summary
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from statistics import mean, median


def top_entry(probs: dict[str, float] | None) -> tuple[str, float]:
    if not probs:
        return "", float("nan")
    label, value = max(probs.items(), key=lambda item: float(item[1]))
    return label, float(value)


def safe_float(value) -> float | None:
    if value is None:
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def tv_distance_probs(
    p: dict[str, float] | None,
    q: dict[str, float] | None,
) -> float | None:
    if not p or not q:
        return None
    labels = set(p) | set(q)
    return 0.5 * sum(abs(float(p.get(label, 0.0)) - float(q.get(label, 0.0))) for label in labels)


def percentile(sorted_values: list[float], q: float) -> float:
    if not sorted_values:
        return float("nan")
    if len(sorted_values) == 1:
        return float(sorted_values[0])
    q = max(0.0, min(1.0, q))
    pos = q * (len(sorted_values) - 1)
    lower = int(math.floor(pos))
    upper = int(math.ceil(pos))
    if lower == upper:
        return float(sorted_values[lower])
    frac = pos - lower
    return float(sorted_values[lower] * (1.0 - frac) + sorted_values[upper] * frac)


def load_rows(path: Path) -> tuple[list[dict], int]:
    rows: list[dict] = []
    truncated_lines = 0
    with path.open() as handle:
        for line_number, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                truncated_lines += 1
                continue
            ref_top, ref_top_prob = top_entry(record.get("reference_probs"))
            theory_top, theory_top_prob = top_entry(record.get("theoretical_probs"))
            final_top, final_top_prob = top_entry(record.get("final_probs"))
            row = {
                "row_number": line_number,
                "index": record.get("index"),
                "prompt_id": record.get("prompt_id"),
                "block_name": record.get("block_name"),
                "case_key": record.get("case_key"),
                "duration_seconds": safe_float(record.get("duration_seconds")),
                "train_seconds": safe_float(record.get("train_seconds")),
                "tv_to_theory": safe_float(record.get("tv_to_theory")),
                "tv_theory_to_reference": tv_distance_probs(
                    record.get("theoretical_probs"),
                    record.get("reference_probs"),
                ),
                "tv_final_to_reference": tv_distance_probs(
                    record.get("final_probs"),
                    record.get("reference_probs"),
                ),
                "max_abs_error": safe_float(record.get("max_abs_error")),
                "reference_top": ref_top,
                "reference_top_prob": ref_top_prob,
                "theory_top": theory_top,
                "theory_top_prob": theory_top_prob,
                "final_top": final_top,
                "final_top_prob": final_top_prob,
                "theory_available": bool(record.get("theory_available")),
                "error": record.get("error", ""),
            }
            rows.append(row)
    return rows, truncated_lines


def maybe_load_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    with path.open() as handle:
        return json.load(handle)


def write_row_csv(path: Path, rows: list[dict]) -> None:
    fieldnames = [
        "row_number",
        "index",
        "prompt_id",
        "block_name",
        "case_key",
        "duration_seconds",
        "train_seconds",
        "tv_to_theory",
        "tv_theory_to_reference",
        "tv_final_to_reference",
        "max_abs_error",
        "reference_top",
        "reference_top_prob",
        "theory_top",
        "theory_top_prob",
        "final_top",
        "final_top_prob",
        "theory_available",
        "error",
    ]
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def seconds_to_hours(seconds: float | None) -> float | None:
    if seconds is None or math.isnan(seconds):
        return None
    return seconds / 3600.0


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input_jsonl", type=Path)
    parser.add_argument("--output-csv", type=Path, default=None)
    parser.add_argument("--output-json", type=Path, default=None)
    parser.add_argument("--output-text", type=Path, default=None)
    parser.add_argument("--top-k", type=int, default=10)
    args = parser.parse_args()

    input_path = args.input_jsonl
    output_csv = args.output_csv or input_path.with_suffix(".summary.csv")
    output_json = args.output_json or input_path.with_suffix(".monitor.json")
    output_text = args.output_text or input_path.with_suffix(".monitor.txt")

    rows, truncated_lines = load_rows(input_path)
    write_row_csv(output_csv, rows)

    status = maybe_load_json(input_path.with_suffix(".status.json")) or {}
    meta = maybe_load_json(input_path.with_suffix(".meta.json")) or {}

    total_cases = status.get("total_cases") or meta.get("total_cases")
    completed = len(rows)
    remaining = None if total_cases is None else max(int(total_cases) - completed, 0)

    duration_rows = [row for row in rows if row["duration_seconds"] is not None]
    train_rows = [row for row in rows if row["train_seconds"] is not None]
    theory_rows = [row for row in rows if row["theory_available"] and row["tv_to_theory"] is not None]
    error_rows = [row for row in rows if row["error"]]

    durations = [row["duration_seconds"] for row in duration_rows]
    train_seconds = [row["train_seconds"] for row in train_rows]
    tvs = sorted(row["tv_to_theory"] for row in theory_rows if row["tv_to_theory"] is not None)
    tv_theory_ref = sorted(
        row["tv_theory_to_reference"]
        for row in theory_rows
        if row["tv_theory_to_reference"] is not None
    )
    tv_final_ref = sorted(
        row["tv_final_to_reference"]
        for row in theory_rows
        if row["tv_final_to_reference"] is not None
    )
    max_errs = sorted(row["max_abs_error"] for row in theory_rows if row["max_abs_error"] is not None)

    top_match_rows = [
        row for row in theory_rows
        if row["theory_top"] and row["final_top"]
    ]
    top_match_count = sum(1 for row in top_match_rows if row["theory_top"] == row["final_top"])

    summary = {
        "input_jsonl": str(input_path),
        "completed_rows": completed,
        "theory_rows": len(theory_rows),
        "error_rows": len(error_rows),
        "truncated_lines_ignored": truncated_lines,
        "total_cases": total_cases,
        "remaining_cases": remaining,
        "last_case_key": rows[-1]["case_key"] if rows else None,
        "duration_seconds": {
            "sum": sum(durations) if durations else None,
            "sum_hours": seconds_to_hours(sum(durations)) if durations else None,
            "mean": mean(durations) if durations else None,
            "median": median(durations) if durations else None,
            "p90": percentile(sorted(durations), 0.90) if durations else None,
            "p95": percentile(sorted(durations), 0.95) if durations else None,
            "max": max(durations) if durations else None,
            "last5_mean": mean(durations[-5:]) if durations else None,
        },
        "train_seconds": {
            "sum": sum(train_seconds) if train_seconds else None,
            "sum_hours": seconds_to_hours(sum(train_seconds)) if train_seconds else None,
            "mean": mean(train_seconds) if train_seconds else None,
            "median": median(train_seconds) if train_seconds else None,
            "p90": percentile(sorted(train_seconds), 0.90) if train_seconds else None,
            "p95": percentile(sorted(train_seconds), 0.95) if train_seconds else None,
            "max": max(train_seconds) if train_seconds else None,
        },
        "tv_to_theory": {
            "mean": mean(tvs) if tvs else None,
            "median": median(tvs) if tvs else None,
            "p90": percentile(tvs, 0.90) if tvs else None,
            "p95": percentile(tvs, 0.95) if tvs else None,
            "p99": percentile(tvs, 0.99) if tvs else None,
            "max": max(tvs) if tvs else None,
        },
        "tv_theory_to_reference": {
            "mean": mean(tv_theory_ref) if tv_theory_ref else None,
            "median": median(tv_theory_ref) if tv_theory_ref else None,
            "p90": percentile(tv_theory_ref, 0.90) if tv_theory_ref else None,
            "p95": percentile(tv_theory_ref, 0.95) if tv_theory_ref else None,
            "p99": percentile(tv_theory_ref, 0.99) if tv_theory_ref else None,
            "max": max(tv_theory_ref) if tv_theory_ref else None,
        },
        "tv_final_to_reference": {
            "mean": mean(tv_final_ref) if tv_final_ref else None,
            "median": median(tv_final_ref) if tv_final_ref else None,
            "p90": percentile(tv_final_ref, 0.90) if tv_final_ref else None,
            "p95": percentile(tv_final_ref, 0.95) if tv_final_ref else None,
            "p99": percentile(tv_final_ref, 0.99) if tv_final_ref else None,
            "max": max(tv_final_ref) if tv_final_ref else None,
        },
        "max_abs_error": {
            "mean": mean(max_errs) if max_errs else None,
            "median": median(max_errs) if max_errs else None,
            "p90": percentile(max_errs, 0.90) if max_errs else None,
            "p95": percentile(max_errs, 0.95) if max_errs else None,
            "p99": percentile(max_errs, 0.99) if max_errs else None,
            "max": max(max_errs) if max_errs else None,
        },
        "top_choice_agreement": {
            "count": top_match_count,
            "total": len(top_match_rows),
            "rate": (top_match_count / len(top_match_rows)) if top_match_rows else None,
        },
        "eta_hours": {
            "by_mean_duration": (
                seconds_to_hours(mean(durations) * remaining)
                if durations and remaining is not None
                else None
            ),
            "by_last5_mean_duration": (
                seconds_to_hours(mean(durations[-5:]) * remaining)
                if durations and remaining is not None
                else None
            ),
        },
        "slowest_cases": [
            {
                "case_key": row["case_key"],
                "duration_seconds": row["duration_seconds"],
                "train_seconds": row["train_seconds"],
                "tv_to_theory": row["tv_to_theory"],
            }
            for row in sorted(duration_rows, key=lambda row: row["duration_seconds"], reverse=True)[: args.top_k]
        ],
        "largest_tv_cases": [
            {
                "case_key": row["case_key"],
                "tv_to_theory": row["tv_to_theory"],
                "tv_theory_to_reference": row["tv_theory_to_reference"],
                "tv_final_to_reference": row["tv_final_to_reference"],
                "max_abs_error": row["max_abs_error"],
                "duration_seconds": row["duration_seconds"],
                "theory_top": row["theory_top"],
                "final_top": row["final_top"],
            }
            for row in sorted(theory_rows, key=lambda row: row["tv_to_theory"], reverse=True)[: args.top_k]
        ],
        "largest_tv_theory_to_reference_cases": [
            {
                "case_key": row["case_key"],
                "tv_theory_to_reference": row["tv_theory_to_reference"],
                "tv_final_to_reference": row["tv_final_to_reference"],
                "tv_to_theory": row["tv_to_theory"],
                "duration_seconds": row["duration_seconds"],
                "theory_top": row["theory_top"],
                "final_top": row["final_top"],
            }
            for row in sorted(
                theory_rows,
                key=lambda row: row["tv_theory_to_reference"] if row["tv_theory_to_reference"] is not None else float("-inf"),
                reverse=True,
            )[: args.top_k]
        ],
        "largest_max_abs_error_cases": [
            {
                "case_key": row["case_key"],
                "max_abs_error": row["max_abs_error"],
                "tv_to_theory": row["tv_to_theory"],
                "tv_theory_to_reference": row["tv_theory_to_reference"],
                "tv_final_to_reference": row["tv_final_to_reference"],
                "duration_seconds": row["duration_seconds"],
                "theory_top": row["theory_top"],
                "final_top": row["final_top"],
            }
            for row in sorted(theory_rows, key=lambda row: row["max_abs_error"], reverse=True)[: args.top_k]
        ],
    }

    with output_json.open("w") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True)

    lines = [
        f"input_jsonl: {input_path}",
        f"completed_rows: {completed}",
        f"total_cases: {total_cases}",
        f"remaining_cases: {remaining}",
        f"theory_rows: {len(theory_rows)}",
        f"error_rows: {len(error_rows)}",
        f"truncated_lines_ignored: {truncated_lines}",
        f"last_case_key: {summary['last_case_key']}",
        "",
        f"duration_sum_hours: {summary['duration_seconds']['sum_hours']}",
        f"duration_mean_seconds: {summary['duration_seconds']['mean']}",
        f"duration_median_seconds: {summary['duration_seconds']['median']}",
        f"duration_p90_seconds: {summary['duration_seconds']['p90']}",
        f"duration_p95_seconds: {summary['duration_seconds']['p95']}",
        f"duration_max_seconds: {summary['duration_seconds']['max']}",
        f"duration_last5_mean_seconds: {summary['duration_seconds']['last5_mean']}",
        "",
        f"tv_mean: {summary['tv_to_theory']['mean']}",
        f"tv_median: {summary['tv_to_theory']['median']}",
        f"tv_p90: {summary['tv_to_theory']['p90']}",
        f"tv_p95: {summary['tv_to_theory']['p95']}",
        f"tv_p99: {summary['tv_to_theory']['p99']}",
        f"tv_max: {summary['tv_to_theory']['max']}",
        "",
        f"tv_theory_to_reference_mean: {summary['tv_theory_to_reference']['mean']}",
        f"tv_theory_to_reference_median: {summary['tv_theory_to_reference']['median']}",
        f"tv_theory_to_reference_p90: {summary['tv_theory_to_reference']['p90']}",
        f"tv_theory_to_reference_p95: {summary['tv_theory_to_reference']['p95']}",
        f"tv_theory_to_reference_p99: {summary['tv_theory_to_reference']['p99']}",
        f"tv_theory_to_reference_max: {summary['tv_theory_to_reference']['max']}",
        "",
        f"tv_final_to_reference_mean: {summary['tv_final_to_reference']['mean']}",
        f"tv_final_to_reference_median: {summary['tv_final_to_reference']['median']}",
        f"tv_final_to_reference_p90: {summary['tv_final_to_reference']['p90']}",
        f"tv_final_to_reference_p95: {summary['tv_final_to_reference']['p95']}",
        f"tv_final_to_reference_p99: {summary['tv_final_to_reference']['p99']}",
        f"tv_final_to_reference_max: {summary['tv_final_to_reference']['max']}",
        "",
        f"max_abs_error_mean: {summary['max_abs_error']['mean']}",
        f"max_abs_error_median: {summary['max_abs_error']['median']}",
        f"max_abs_error_p90: {summary['max_abs_error']['p90']}",
        f"max_abs_error_p95: {summary['max_abs_error']['p95']}",
        f"max_abs_error_p99: {summary['max_abs_error']['p99']}",
        f"max_abs_error_max: {summary['max_abs_error']['max']}",
        "",
        f"top_choice_agreement_count: {summary['top_choice_agreement']['count']}",
        f"top_choice_agreement_total: {summary['top_choice_agreement']['total']}",
        f"top_choice_agreement_rate: {summary['top_choice_agreement']['rate']}",
        "",
        f"eta_hours_mean_duration: {summary['eta_hours']['by_mean_duration']}",
        f"eta_hours_last5_mean_duration: {summary['eta_hours']['by_last5_mean_duration']}",
        "",
        "slowest_cases:",
    ]
    for row in summary["slowest_cases"]:
        lines.append(
            f"  - {row['case_key']} duration={row['duration_seconds']} "
            f"train={row['train_seconds']} tv={row['tv_to_theory']}"
        )
    lines.append("")
    lines.append("largest_tv_cases:")
    for row in summary["largest_tv_cases"]:
        lines.append(
            f"  - {row['case_key']} tv={row['tv_to_theory']} "
            f"tv_theory_ref={row['tv_theory_to_reference']} "
            f"tv_final_ref={row['tv_final_to_reference']} "
            f"max_abs={row['max_abs_error']} duration={row['duration_seconds']} "
            f"theory_top={row['theory_top']} final_top={row['final_top']}"
        )
    lines.append("")
    lines.append("largest_tv_theory_to_reference_cases:")
    for row in summary["largest_tv_theory_to_reference_cases"]:
        lines.append(
            f"  - {row['case_key']} tv_theory_ref={row['tv_theory_to_reference']} "
            f"tv_final_ref={row['tv_final_to_reference']} tv={row['tv_to_theory']} "
            f"duration={row['duration_seconds']} theory_top={row['theory_top']} "
            f"final_top={row['final_top']}"
        )
    lines.append("")
    lines.append("largest_max_abs_error_cases:")
    for row in summary["largest_max_abs_error_cases"]:
        lines.append(
            f"  - {row['case_key']} max_abs={row['max_abs_error']} "
            f"tv={row['tv_to_theory']} tv_theory_ref={row['tv_theory_to_reference']} "
            f"tv_final_ref={row['tv_final_to_reference']} duration={row['duration_seconds']} "
            f"theory_top={row['theory_top']} final_top={row['final_top']}"
        )

    with output_text.open("w") as handle:
        handle.write("\n".join(lines) + "\n")

    print(f"Wrote {output_csv}")
    print(f"Wrote {output_json}")
    print(f"Wrote {output_text}")


if __name__ == "__main__":
    main()
