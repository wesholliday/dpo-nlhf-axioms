#!/usr/bin/env python3
"""Condition violation frequencies on theory-predicted nontrivial change.

This script focuses on single-voter monotonicity / involvement opportunities.
For each voter, it checks whether there exists an admissible action whose
theory-predicted candidate-probability change is at least a chosen threshold,
and whether among such actions there exists a violation of at least a chosen
magnitude. It then aggregates to voter- and profile-level conditional
frequencies.
"""

from __future__ import annotations

import argparse
import csv
import json
import multiprocessing as mp
from pathlib import Path
from typing import Sequence

import numpy as np

from scripts.theory.nlhf_tie_normalization import (
    TieNormCase,
    load_cases_tie_norm,
    parse_ranking,
    ranking_to_wins_and_ties,
    solve_nlhf_tie_norm,
)
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases as load_rtbt_cases
from scripts.theory.search_coval_violation_counts import ranking_to_wins
from scripts.theory.search_model_reference_violation_counts import rho_for_case as rtbt_rho_for_case
from scripts.theory.search_new_nlhf_tie_normalization_examples import (
    ReferenceConfig,
    demotions,
    improvements,
    load_rho_cache,
    monotonicity_move_valid,
    rho_for_case,
    strictly_last_candidate,
)
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda


_CASES: Sequence = ()
_REF: ReferenceConfig | None = None
_RHO_CACHE: dict[str, dict] = {}
_PARAM = 0.01
_RULE = "nlhf_tie_norm"
_AXIOM = "monotonicity"
_CHANGE_THRESHOLDS: tuple[float, ...] = (0.01,)


def parse_float_list(text: str) -> list[float]:
    return [float(part.strip()) for part in text.split(",") if part.strip()]


def parse_reference_spec(text: str, defaults: dict[str, ReferenceConfig]) -> ReferenceConfig:
    if text in defaults:
        return defaults[text]
    if text == "uniform":
        return ReferenceConfig("uniform", None)
    if "=" not in text:
        raise argparse.ArgumentTypeError(
            f"Reference must be one of {sorted(defaults)}, 'uniform', or alias=path: {text}"
        )
    alias, path = text.split("=", 1)
    alias = alias.strip()
    path = path.strip()
    if not alias or not path:
        raise argparse.ArgumentTypeError(f"Invalid reference spec: {text}")
    return ReferenceConfig(alias, Path(path))


def profile_key(case) -> str:
    return f"{case.prompt_id}:{case.block_name}"


def voter_key(case, voter_index: int) -> str:
    return f"{profile_key(case)}:{voter_index}"


def top_candidate(ranking: str) -> str | None:
    blocks = parse_ranking(ranking)
    if not blocks or len(blocks[0]) != 1:
        return None
    return blocks[0][0]


def solve_rtbt(beta: float, wins: np.ndarray, rho: np.ndarray) -> np.ndarray | None:
    return solve_weighted_logistic_borda(beta, wins, rho)


def blank_threshold_maps() -> tuple[dict[float, bool], dict[float, float]]:
    return (
        {threshold: False for threshold in _CHANGE_THRESHOLDS},
        {threshold: 0.0 for threshold in _CHANGE_THRESHOLDS},
    )


def update_threshold_maps(
    eligible: dict[float, bool],
    max_effect: dict[float, float],
    predicted_change: float,
    violation_effect: float,
) -> None:
    for threshold in _CHANGE_THRESHOLDS:
        if predicted_change >= threshold:
            eligible[threshold] = True
            if violation_effect > max_effect[threshold]:
                max_effect[threshold] = violation_effect


def voter_monotonicity_stats(case: TieNormCase, voter_index: int, tau: float, rho: np.ndarray) -> tuple[dict[float, bool], dict[float, float]]:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total_wins = np.asarray(case.total_wins, dtype=float)
    total_ties = np.asarray(case.total_ties, dtype=float)
    wins_per = [np.asarray(w, dtype=float) for w in case.wins_per_ranking]
    ties_per = [np.asarray(t, dtype=float) for t in case.ties_per_ranking]
    observed = solve_nlhf_tie_norm(tau, total_wins, total_ties, rho)
    eligible, max_effect = blank_threshold_maps()
    if observed is None:
        return eligible, max_effect

    ranking = case.rankings[voter_index]
    blocks = parse_ranking(ranking)
    present = {cand for block in blocks for cand in block}
    for cand in labels:
        if cand not in present:
            continue
        idx = index[cand]
        for new_ranking in improvements(blocks, cand):
            new_blocks = parse_ranking(new_ranking)
            if not monotonicity_move_valid(blocks, new_blocks, cand, labels):
                continue
            new_wins, new_ties = ranking_to_wins_and_ties(new_ranking, index)
            after = solve_nlhf_tie_norm(
                tau,
                total_wins - wins_per[voter_index] + new_wins,
                total_ties - ties_per[voter_index] + new_ties,
                rho,
            )
            if after is None:
                continue
            predicted_change = abs(float(observed[idx] - after[idx]))
            violation_effect = max(0.0, float(observed[idx] - after[idx]))
            update_threshold_maps(eligible, max_effect, predicted_change, violation_effect)
        for new_ranking in demotions(blocks, cand):
            new_blocks = parse_ranking(new_ranking)
            if not monotonicity_move_valid(new_blocks, blocks, cand, labels):
                continue
            new_wins, new_ties = ranking_to_wins_and_ties(new_ranking, index)
            before = solve_nlhf_tie_norm(
                tau,
                total_wins - wins_per[voter_index] + new_wins,
                total_ties - ties_per[voter_index] + new_ties,
                rho,
            )
            if before is None:
                continue
            predicted_change = abs(float(before[idx] - observed[idx]))
            violation_effect = max(0.0, float(before[idx] - observed[idx]))
            update_threshold_maps(eligible, max_effect, predicted_change, violation_effect)
    return eligible, max_effect


def voter_nlhf_involvement_stats(case: TieNormCase, voter_index: int, tau: float, rho: np.ndarray) -> tuple[dict[float, bool], dict[float, float]]:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total_wins = np.asarray(case.total_wins, dtype=float)
    total_ties = np.asarray(case.total_ties, dtype=float)
    wins_per = [np.asarray(w, dtype=float) for w in case.wins_per_ranking]
    ties_per = [np.asarray(t, dtype=float) for t in case.ties_per_ranking]
    observed = solve_nlhf_tie_norm(tau, total_wins, total_ties, rho)
    eligible, max_effect = blank_threshold_maps()
    if observed is None:
        return eligible, max_effect

    ranking = case.rankings[voter_index]
    reduced = solve_nlhf_tie_norm(
        tau,
        total_wins - wins_per[voter_index],
        total_ties - ties_per[voter_index],
        rho,
    )
    if reduced is None:
        return eligible, max_effect

    cand = top_candidate(ranking)
    if cand is not None:
        idx = index[cand]
        predicted_change = abs(float(reduced[idx] - observed[idx]))
        violation_effect = max(0.0, float(reduced[idx] - observed[idx]))
        update_threshold_maps(eligible, max_effect, predicted_change, violation_effect)

    cand = strictly_last_candidate(ranking, labels)
    if cand is not None:
        idx = index[cand]
        predicted_change = abs(float(observed[idx] - reduced[idx]))
        violation_effect = max(0.0, float(observed[idx] - reduced[idx]))
        update_threshold_maps(eligible, max_effect, predicted_change, violation_effect)

    return eligible, max_effect


def voter_rtbt_involvement_stats(case, voter_index: int, beta: float, rho: np.ndarray) -> tuple[dict[float, bool], dict[float, float]]:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total_wins = np.asarray(case.total_wins, dtype=float)
    wins_per = [np.asarray(w, dtype=float) for w in case.wins_per_ranking]
    observed = solve_rtbt(beta, total_wins, rho)
    eligible, max_effect = blank_threshold_maps()
    if observed is None:
        return eligible, max_effect

    reduced = solve_rtbt(beta, total_wins - wins_per[voter_index], rho)
    if reduced is None:
        return eligible, max_effect

    ranking = case.rankings[voter_index]
    cand = top_candidate(ranking)
    if cand is not None:
        idx = index[cand]
        predicted_change = abs(float(reduced[idx] - observed[idx]))
        violation_effect = max(0.0, float(reduced[idx] - observed[idx]))
        update_threshold_maps(eligible, max_effect, predicted_change, violation_effect)

    cand = strictly_last_candidate(ranking, labels)
    if cand is not None:
        idx = index[cand]
        predicted_change = abs(float(observed[idx] - reduced[idx]))
        violation_effect = max(0.0, float(observed[idx] - reduced[idx]))
        update_threshold_maps(eligible, max_effect, predicted_change, violation_effect)

    return eligible, max_effect


def init_worker(
    cases: Sequence,
    ref: ReferenceConfig,
    rho_cache: dict[str, dict],
    param: float,
    rule: str,
    axiom: str,
    change_thresholds: Sequence[float],
) -> None:
    global _CASES, _REF, _RHO_CACHE, _PARAM, _RULE, _AXIOM, _CHANGE_THRESHOLDS
    _CASES = cases
    _REF = ref
    _RHO_CACHE = rho_cache
    _PARAM = param
    _RULE = rule
    _AXIOM = axiom
    _CHANGE_THRESHOLDS = tuple(sorted(float(x) for x in change_thresholds))


def worker(indices: Sequence[int]) -> list[dict]:
    assert _REF is not None
    rows: list[dict] = []
    for case_index in indices:
        case = _CASES[case_index]
        try:
            if _RULE == "nlhf_tie_norm":
                rho, _ = rho_for_case(case, _REF, _RHO_CACHE)
            elif _REF.rho_cache is None:
                rho = np.full(len(case.response_indices), 1.0 / len(case.response_indices), dtype=float)
            else:
                record = _RHO_CACHE.get(case.prompt_id)
                if record is None:
                    continue
                rho = rtbt_rho_for_case(case, record)
        except KeyError:
            continue

        for voter_index in range(len(case.rankings)):
            if _RULE == "nlhf_tie_norm" and _AXIOM == "monotonicity":
                eligible, max_effect = voter_monotonicity_stats(case, voter_index, _PARAM, rho)
            elif _RULE == "nlhf_tie_norm" and _AXIOM == "involvement":
                eligible, max_effect = voter_nlhf_involvement_stats(case, voter_index, _PARAM, rho)
            elif _RULE == "rtbt" and _AXIOM == "involvement":
                eligible, max_effect = voter_rtbt_involvement_stats(case, voter_index, _PARAM, rho)
            else:
                raise ValueError(f"Unsupported combination: {_RULE}/{_AXIOM}")

            for threshold in _CHANGE_THRESHOLDS:
                rows.append(
                    {
                        "model_alias": _REF.name,
                        "rule": _RULE,
                        "axiom": _AXIOM,
                        "param_name": "tau" if _RULE == "nlhf_tie_norm" else "beta",
                        "param_value": _PARAM,
                        "prompt_id": case.prompt_id,
                        "block_name": case.block_name,
                        "profile_key": profile_key(case),
                        "voter_index": voter_index,
                        "voter_key": voter_key(case, voter_index),
                        "change_threshold": threshold,
                        "eligible": bool(eligible[threshold]),
                        "max_effect_among_eligible_actions": float(max_effect[threshold]),
                    }
                )
    return rows


def run_rows(
    cases: Sequence,
    ref: ReferenceConfig,
    rho_cache: dict[str, dict],
    param: float,
    rule: str,
    axiom: str,
    change_thresholds: Sequence[float],
    workers: int,
) -> list[dict]:
    chunks: list[list[int]] = [[] for _ in range(workers)]
    for i in range(len(cases)):
        chunks[i % workers].append(i)
    ctx = mp.get_context("fork")
    with ctx.Pool(
        workers,
        initializer=init_worker,
        initargs=(cases, ref, rho_cache, param, rule, axiom, change_thresholds),
    ) as pool:
        pieces = pool.map(worker, chunks)
    return [row for piece in pieces for row in piece]


def append_jsonl(path: Path, rows: Sequence[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")


def load_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    with path.open() as handle:
        return [json.loads(line) for line in handle if line.strip()]


def write_voter_summary(
    path: Path,
    rows: Sequence[dict],
    effect_thresholds: Sequence[float],
    model_aliases: Sequence[str],
    nlhf_taus: Sequence[float],
    rtbt_betas: Sequence[float],
    change_thresholds: Sequence[float],
) -> None:
    fieldnames = [
        "change_threshold",
        "effect_threshold",
        "model_alias",
        "rule",
        "axiom",
        "param_name",
        "param_value",
        "voters_eligible",
        "voters_with_witness",
        "percent_with_witness",
    ]
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for change_threshold in change_thresholds:
            for effect_threshold in effect_thresholds:
                for alias in model_aliases:
                    for tau in nlhf_taus:
                        for axiom in ("monotonicity", "involvement"):
                            subset = [
                                row
                                for row in rows
                                if row["model_alias"] == alias
                                and row["rule"] == "nlhf_tie_norm"
                                and row["axiom"] == axiom
                                and float(row["param_value"]) == float(tau)
                                and float(row["change_threshold"]) == float(change_threshold)
                            ]
                            eligible = sum(1 for row in subset if row["eligible"])
                            witness = sum(
                                1
                                for row in subset
                                if row["eligible"] and float(row["max_effect_among_eligible_actions"]) >= effect_threshold
                            )
                            writer.writerow(
                                {
                                    "change_threshold": change_threshold,
                                    "effect_threshold": effect_threshold,
                                    "model_alias": alias,
                                    "rule": "nlhf_tie_norm",
                                    "axiom": axiom,
                                    "param_name": "tau",
                                    "param_value": tau,
                                    "voters_eligible": eligible,
                                    "voters_with_witness": witness,
                                    "percent_with_witness": 100.0 * witness / eligible if eligible else 0.0,
                                }
                            )
                    for beta in rtbt_betas:
                        subset = [
                            row
                            for row in rows
                            if row["model_alias"] == alias
                            and row["rule"] == "rtbt"
                            and row["axiom"] == "involvement"
                            and float(row["param_value"]) == float(beta)
                            and float(row["change_threshold"]) == float(change_threshold)
                        ]
                        eligible = sum(1 for row in subset if row["eligible"])
                        witness = sum(
                            1
                            for row in subset
                            if row["eligible"] and float(row["max_effect_among_eligible_actions"]) >= effect_threshold
                        )
                        writer.writerow(
                            {
                                "change_threshold": change_threshold,
                                "effect_threshold": effect_threshold,
                                "model_alias": alias,
                                "rule": "rtbt",
                                "axiom": "involvement",
                                "param_name": "beta",
                                "param_value": beta,
                                "voters_eligible": eligible,
                                "voters_with_witness": witness,
                                "percent_with_witness": 100.0 * witness / eligible if eligible else 0.0,
                            }
                        )


def write_profile_summary(
    path: Path,
    rows: Sequence[dict],
    effect_thresholds: Sequence[float],
    model_aliases: Sequence[str],
    nlhf_taus: Sequence[float],
    rtbt_betas: Sequence[float],
    change_thresholds: Sequence[float],
) -> None:
    fieldnames = [
        "change_threshold",
        "effect_threshold",
        "model_alias",
        "rule",
        "axiom",
        "param_name",
        "param_value",
        "profiles_eligible",
        "profiles_with_witness",
        "percent_with_witness",
    ]
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for change_threshold in change_thresholds:
            for effect_threshold in effect_thresholds:
                for alias in model_aliases:
                    for tau in nlhf_taus:
                        for axiom in ("monotonicity", "involvement"):
                            subset = [
                                row
                                for row in rows
                                if row["model_alias"] == alias
                                and row["rule"] == "nlhf_tie_norm"
                                and row["axiom"] == axiom
                                and float(row["param_value"]) == float(tau)
                                and float(row["change_threshold"]) == float(change_threshold)
                            ]
                            eligible_profiles = {
                                row["profile_key"] for row in subset if row["eligible"]
                            }
                            witness_profiles = {
                                row["profile_key"]
                                for row in subset
                                if row["eligible"] and float(row["max_effect_among_eligible_actions"]) >= effect_threshold
                            }
                            writer.writerow(
                                {
                                    "change_threshold": change_threshold,
                                    "effect_threshold": effect_threshold,
                                    "model_alias": alias,
                                    "rule": "nlhf_tie_norm",
                                    "axiom": axiom,
                                    "param_name": "tau",
                                    "param_value": tau,
                                    "profiles_eligible": len(eligible_profiles),
                                    "profiles_with_witness": len(witness_profiles),
                                    "percent_with_witness": 100.0 * len(witness_profiles) / len(eligible_profiles) if eligible_profiles else 0.0,
                                }
                            )
                    for beta in rtbt_betas:
                        subset = [
                            row
                            for row in rows
                            if row["model_alias"] == alias
                            and row["rule"] == "rtbt"
                            and row["axiom"] == "involvement"
                            and float(row["param_value"]) == float(beta)
                            and float(row["change_threshold"]) == float(change_threshold)
                        ]
                        eligible_profiles = {row["profile_key"] for row in subset if row["eligible"]}
                        witness_profiles = {
                            row["profile_key"]
                            for row in subset
                            if row["eligible"] and float(row["max_effect_among_eligible_actions"]) >= effect_threshold
                        }
                        writer.writerow(
                            {
                                "change_threshold": change_threshold,
                                "effect_threshold": effect_threshold,
                                "model_alias": alias,
                                "rule": "rtbt",
                                "axiom": "involvement",
                                "param_name": "beta",
                                "param_value": beta,
                                "profiles_eligible": len(eligible_profiles),
                                "profiles_with_witness": len(witness_profiles),
                                "percent_with_witness": 100.0 * len(witness_profiles) / len(eligible_profiles) if eligible_profiles else 0.0,
                            }
                        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/theory_change_conditioned_violation_frequencies"))
    parser.add_argument("--cache-path", type=Path, default=None)
    parser.add_argument("--nemo-rho-cache", type=Path, default=Path("results/reference_distributions/nemo_pytorch_rho_strip_identity.jsonl"))
    parser.add_argument("--qwen25-rho-cache", type=Path, default=Path("results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl"))
    parser.add_argument("--qwen3-rho-cache", type=Path, default=Path("results/reference_distributions/qwen3_pytorch_rho_strip_identity.jsonl"))
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--effect-thresholds", type=parse_float_list, default=[0.01])
    parser.add_argument("--change-thresholds", type=parse_float_list, default=[0.001, 0.01, 0.05])
    parser.add_argument("--nlhf-taus", type=parse_float_list, default=[0.01])
    parser.add_argument("--rtbt-betas", type=parse_float_list, default=[0.1])
    parser.add_argument(
        "--include-uniform-reference",
        action="store_true",
        help="Also run the same conditioned frequency/magnitude scan with a uniform reference distribution.",
    )
    parser.add_argument(
        "--references",
        nargs="+",
        default=None,
        help=(
            "Optional reference set. Entries may be default aliases "
            "(nemo_base_strip_identity, qwen25_base_strip_identity, qwen3_base_strip_identity), "
            "'uniform', or alias=path. If omitted, the three model references are used."
        ),
    )
    parser.add_argument("--recompute", action="store_true")
    args = parser.parse_args()

    output_dir = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)
    cache_path = args.cache_path or (output_dir / "theory_change_voter_rows.jsonl")

    default_refs = {
        "nemo_base_strip_identity": ReferenceConfig("nemo_base_strip_identity", args.nemo_rho_cache),
        "qwen25_base_strip_identity": ReferenceConfig("qwen25_base_strip_identity", args.qwen25_rho_cache),
        "qwen3_base_strip_identity": ReferenceConfig("qwen3_base_strip_identity", args.qwen3_rho_cache),
    }
    if args.references is None:
        model_refs = list(default_refs.values())
        if args.include_uniform_reference:
            model_refs = [ReferenceConfig("uniform", None), *model_refs]
    else:
        model_refs = [parse_reference_spec(spec, default_refs) for spec in args.references]
    model_aliases = [ref.name for ref in model_refs]
    nlhf_cases = load_cases_tie_norm(args.dataset, ["world", "personal"])
    rtbt_cases = load_rtbt_cases(args.dataset, ["world", "personal"])

    if args.recompute or not cache_path.exists():
        cache_path.write_text("")
        for ref in model_refs:
            rho_cache = {} if ref.rho_cache is None else load_rho_cache(ref.rho_cache)
            for tau in args.nlhf_taus:
                for axiom in ("monotonicity", "involvement"):
                    rows = run_rows(
                        nlhf_cases,
                        ref,
                        rho_cache,
                        tau,
                        "nlhf_tie_norm",
                        axiom,
                        args.change_thresholds,
                        args.workers,
                    )
                    append_jsonl(cache_path, rows)
                    print(
                        json.dumps(
                            {
                                "model_alias": ref.name,
                                "rule": "nlhf_tie_norm",
                                "axiom": axiom,
                                "param_value": tau,
                                "rows": len(rows),
                            },
                            sort_keys=True,
                        ),
                        flush=True,
                    )
            for beta in args.rtbt_betas:
                rows = run_rows(
                    rtbt_cases,
                    ref,
                    rho_cache,
                    beta,
                    "rtbt",
                    "involvement",
                    args.change_thresholds,
                    args.workers,
                )
                append_jsonl(cache_path, rows)
                print(
                    json.dumps(
                        {
                            "model_alias": ref.name,
                            "rule": "rtbt",
                            "axiom": "involvement",
                            "param_value": beta,
                            "rows": len(rows),
                        },
                        sort_keys=True,
                    ),
                    flush=True,
                )

    rows = load_jsonl(cache_path)
    profile_summary_path = output_dir / "profile_conditioned_on_theory_change.csv"
    voter_summary_path = output_dir / "voter_conditioned_on_theory_change.csv"
    write_profile_summary(
        profile_summary_path,
        rows,
        args.effect_thresholds,
        model_aliases,
        args.nlhf_taus,
        args.rtbt_betas,
        args.change_thresholds,
    )
    write_voter_summary(
        voter_summary_path,
        rows,
        args.effect_thresholds,
        model_aliases,
        args.nlhf_taus,
        args.rtbt_betas,
        args.change_thresholds,
    )
    metadata = {
        "cache": str(cache_path),
        "effect_thresholds": args.effect_thresholds,
        "change_thresholds": args.change_thresholds,
        "profile_summary": str(profile_summary_path),
        "references": [ref.name for ref in model_refs],
        "voter_summary": str(voter_summary_path),
        "rows": len(rows),
    }
    with (output_dir / "metadata.json").open("w") as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True)
        handle.write("\n")
    print(json.dumps(metadata, sort_keys=True))


if __name__ == "__main__":
    main()
