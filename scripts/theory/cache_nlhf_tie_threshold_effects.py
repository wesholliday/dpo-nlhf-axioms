#!/usr/bin/env python3
"""Cache violation magnitudes once, then plot arbitrary magnitude thresholds."""

from __future__ import annotations

import argparse
from collections import Counter
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
    ranking_to_string,
    ranking_to_wins_and_ties,
    solve_nlhf_tie_norm,
)
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases as load_rtbt_cases
from scripts.theory.search_model_reference_violation_counts import Scenario, load_rho_cache as load_rtbt_rho_cache
from scripts.theory.search_nlhf_tie_normalization_examples import (
    ReferenceConfig,
    best_monotonicity_witness,
    best_negative_involvement_witness,
    best_positive_involvement_witness,
    load_rho_cache,
    rho_for_case,
)
from scripts.theory.sweep_nlhf_tie_normalization_parameters import (
    DEFAULT_NLHF_TAUS,
    DEFAULT_RTBT_BETAS,
    grouped_masks,
    plot_rows,
    run_rtbt_scenario,
)


_NLHF_CASES: Sequence[TieNormCase] = ()
_REF: ReferenceConfig | None = None
_RHO_CACHE: dict[str, dict] = {}
_TAU = 0.01
_AXIOM = "monotonicity"
_COMM_MAX_UNIQUE = 12
_COMM_STOP_EFFECT = 1e-2


def parse_float_list(text: str) -> list[float]:
    return [float(part.strip()) for part in text.split(",") if part.strip()]


def parse_axiom_list(text: str) -> list[str]:
    allowed = {"monotonicity", "positive_involvement", "negative_involvement", "commutativity"}
    axioms = [part.strip() for part in text.split(",") if part.strip()]
    unknown = sorted(set(axioms) - allowed)
    if unknown:
        raise argparse.ArgumentTypeError(f"Unknown NLHF axioms: {', '.join(unknown)}")
    return axioms


def init_worker(
    cases: Sequence[TieNormCase],
    ref: ReferenceConfig,
    rho_cache: dict[str, dict],
    tau: float,
    axiom: str,
    comm_max_unique: int,
    comm_stop_effect: float,
) -> None:
    global _NLHF_CASES, _REF, _RHO_CACHE, _TAU, _AXIOM, _COMM_MAX_UNIQUE, _COMM_STOP_EFFECT
    _NLHF_CASES = cases
    _REF = ref
    _RHO_CACHE = rho_cache
    _TAU = tau
    _AXIOM = axiom
    _COMM_MAX_UNIQUE = comm_max_unique
    _COMM_STOP_EFFECT = comm_stop_effect


def compact_unique_ranking_count(case: TieNormCase) -> int:
    return len({ranking_to_string(parse_ranking(ranking)) for ranking in case.rankings})


def grouped_commutativity_capped_witness(
    case: TieNormCase,
    tau: float,
    rho: np.ndarray,
    ref: ReferenceConfig,
    rho_record: dict | None,
    max_unique_rankings: int,
    stop_effect: float,
) -> dict | None:
    counts = Counter(ranking_to_string(parse_ranking(ranking)) for ranking in case.rankings)
    unique_rankings = sorted(counts)
    if len(unique_rankings) < 2 or len(unique_rankings) > max_unique_rankings:
        return None

    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    shape = (len(labels), len(labels))
    wins_per: list[np.ndarray] = []
    ties_per: list[np.ndarray] = []
    for ranking in unique_rankings:
        wins, ties = ranking_to_wins_and_ties(ranking, index)
        wins_per.append(counts[ranking] * wins)
        ties_per.append(counts[ranking] * ties)

    best: dict | None = None
    for mask in grouped_masks(len(unique_rankings)):
        left_wins = np.zeros(shape, dtype=float)
        left_ties = np.zeros(shape, dtype=float)
        right_wins = np.zeros(shape, dtype=float)
        right_ties = np.zeros(shape, dtype=float)
        for i, (wins, ties) in enumerate(zip(wins_per, ties_per)):
            if mask & (1 << i):
                left_wins += wins
                left_ties += ties
            else:
                right_wins += wins
                right_ties += ties

        left_ref = solve_nlhf_tie_norm(tau, left_wins, left_ties, rho)
        right_ref = solve_nlhf_tie_norm(tau, right_wins, right_ties, rho)
        if left_ref is None or right_ref is None:
            continue
        left_then_right = solve_nlhf_tie_norm(tau, right_wins, right_ties, left_ref)
        right_then_left = solve_nlhf_tie_norm(tau, left_wins, left_ties, right_ref)
        if left_then_right is None or right_then_left is None:
            continue

        tv = 0.5 * float(np.sum(np.abs(left_then_right - right_then_left)))
        if tv <= 0:
            continue
        rankings_left = [unique_rankings[i] for i in range(len(unique_rankings)) if mask & (1 << i)]
        rankings_right = [unique_rankings[i] for i in range(len(unique_rankings)) if not (mask & (1 << i))]
        witness = {
            "prompt_id": case.prompt_id,
            "block_name": case.block_name,
            "reference": ref.name,
            "rho_source": str(ref.rho_cache) if ref.rho_cache is not None else "uniform",
            "rho": rho.tolist(),
            "response_logprobs": rho_record.get("response_logprobs") if rho_record else None,
            "axiom": "commutativity",
            "rule": "nlhf_tie_norm",
            "param": tau,
            "effect": tv,
            "n_assessments": len(case.rankings),
            "n_unique_rankings": len(unique_rankings),
            "rankings_left": rankings_left,
            "rankings_right": rankings_right,
        }
        if best is None or tv > best["effect"]:
            best = witness
            if tv >= stop_effect:
                return best
    return best


def nlhf_worker(indices: Sequence[int]) -> list[dict]:
    assert _REF is not None
    rows: list[dict] = []
    for index in indices:
        case = _NLHF_CASES[index]
        try:
            rho, rho_record = rho_for_case(case, _REF, _RHO_CACHE)
        except KeyError:
            continue
        if _AXIOM == "monotonicity":
            witness = best_monotonicity_witness(case, _TAU, rho, _REF, rho_record)
        elif _AXIOM == "positive_involvement":
            witness = best_positive_involvement_witness(case, _TAU, rho, _REF, rho_record)
        elif _AXIOM == "negative_involvement":
            witness = best_negative_involvement_witness(case, _TAU, rho, _REF, rho_record)
        elif _AXIOM == "commutativity":
            witness = grouped_commutativity_capped_witness(
                case, _TAU, rho, _REF, rho_record, _COMM_MAX_UNIQUE, _COMM_STOP_EFFECT
            )
        else:
            raise ValueError(_AXIOM)
        if witness is None or witness["effect"] <= 0:
            continue
        rows.append(
            {
                "model_alias": _REF.name,
                "rule": "nlhf_tie_norm",
                "axiom": _AXIOM,
                "param_name": "tau",
                "param_value": _TAU,
                "prompt_id": witness["prompt_id"],
                "block_name": witness["block_name"],
                "profile_key": f"{witness['prompt_id']}:{witness['block_name']}",
                "effect": float(witness["effect"]),
            }
        )
    return rows


def run_nlhf_effects(
    cases: Sequence[TieNormCase],
    ref: ReferenceConfig,
    rho_cache: dict[str, dict],
    tau: float,
    axiom: str,
    workers: int,
    comm_max_unique: int,
    comm_stop_effect: float,
) -> list[dict]:
    chunks: list[list[int]] = [[] for _ in range(workers)]
    for i in range(len(cases)):
        chunks[i % workers].append(i)
    ctx = mp.get_context("fork")
    with ctx.Pool(
        workers,
        initializer=init_worker,
        initargs=(cases, ref, rho_cache, tau, axiom, comm_max_unique, comm_stop_effect),
    ) as pool:
        pieces = pool.map(nlhf_worker, chunks)
    return [row for piece in pieces for row in piece]


def append_jsonl(path: Path, rows: Sequence[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")


def load_effect_rows(path: Path) -> list[dict]:
    with path.open() as handle:
        return [json.loads(line) for line in handle if line.strip()]


def make_summary_row(
    effect_rows: Sequence[dict],
    model_alias: str,
    rule: str,
    axiom: str,
    param_name: str,
    param_value: float,
    threshold: float,
    profiles_total: int,
) -> dict:
    keys = {
        row["profile_key"]
        for row in effect_rows
        if row["model_alias"] == model_alias
        and row["rule"] == rule
        and row["axiom"] == axiom
        and row["param_value"] == param_value
        and row["effect"] >= threshold
    }
    fraction = len(keys) / profiles_total if profiles_total else 0.0
    return {
        "model_alias": model_alias,
        "rule": rule,
        "axiom": axiom,
        "param_name": param_name,
        "param_value": param_value,
        "min_effect": threshold,
        "profiles_total": profiles_total,
        "profiles_with_witness": len(keys),
        "fraction_with_witness": fraction,
        "percent_with_witness": 100.0 * fraction,
        "by_block": {},
        "strongest_witness": None,
    }


def threshold_rows(
    effect_rows: Sequence[dict],
    model_aliases: Sequence[str],
    nlhf_taus: Sequence[float],
    rtbt_betas: Sequence[float],
    threshold: float,
    nlhf_total: int,
    rtbt_total: int,
) -> list[dict]:
    rows: list[dict] = []
    for alias in model_aliases:
        for tau in nlhf_taus:
            rows.append(make_summary_row(effect_rows, alias, "nlhf_tie_norm", "monotonicity", "tau", tau, threshold, nlhf_total))
            pos = make_summary_row(effect_rows, alias, "nlhf_tie_norm", "positive_involvement", "tau", tau, threshold, nlhf_total)
            neg = make_summary_row(effect_rows, alias, "nlhf_tie_norm", "negative_involvement", "tau", tau, threshold, nlhf_total)
            involved_keys = {
                row["profile_key"]
                for row in effect_rows
                if row["model_alias"] == alias
                and row["rule"] == "nlhf_tie_norm"
                and row["axiom"] in {"positive_involvement", "negative_involvement"}
                and row["param_value"] == tau
                and row["effect"] >= threshold
            }
            fraction = len(involved_keys) / nlhf_total if nlhf_total else 0.0
            rows.append({
                **pos,
                "axiom": "involvement",
                "profiles_with_witness": len(involved_keys),
                "fraction_with_witness": fraction,
                "percent_with_witness": 100.0 * fraction,
            })
            rows.append(make_summary_row(effect_rows, alias, "nlhf_tie_norm", "commutativity", "tau", tau, threshold, nlhf_total))
        for beta in rtbt_betas:
            involved_keys = {
                row["profile_key"]
                for row in effect_rows
                if row["model_alias"] == alias
                and row["rule"] == "rtbt"
                and row["axiom"] in {"positive_involvement", "negative_involvement"}
                and row["param_value"] == beta
                and row["effect"] >= threshold
            }
            fraction = len(involved_keys) / rtbt_total if rtbt_total else 0.0
            rows.append({
                "model_alias": alias,
                "rule": "rtbt",
                "axiom": "involvement",
                "param_name": "beta",
                "param_value": beta,
                "min_effect": threshold,
                "profiles_total": rtbt_total,
                "profiles_with_witness": len(involved_keys),
                "fraction_with_witness": fraction,
                "percent_with_witness": 100.0 * fraction,
                "by_block": {},
                "strongest_witness": None,
            })
    return rows


def write_threshold_outputs(rows: Sequence[dict], output_dir: Path, threshold: float) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    slug = f"{threshold:g}".replace(".", "p")
    json_path = output_dir / f"model_only_threshold_rows_min_effect_{slug}.json"
    csv_path = output_dir / f"model_only_threshold_rows_min_effect_{slug}.csv"
    with json_path.open("w") as handle:
        json.dump(list(rows), handle, indent=2, sort_keys=True)
        handle.write("\n")
    with csv_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "model_alias",
                "rule",
                "axiom",
                "param_name",
                "param_value",
                "min_effect",
                "profiles_total",
                "profiles_with_witness",
                "fraction_with_witness",
                "percent_with_witness",
            ],
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({name: row[name] for name in writer.fieldnames})


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--output-dir", type=Path, default=Path("results/theory/nlhf_tie_normalization_cache"))
    parser.add_argument("--cache-path", type=Path, default=None)
    parser.add_argument("--nemo-rho-cache", type=Path, default=Path("results/reference_distributions/nemo_pytorch_rho_strip_identity_float32.jsonl"))
    parser.add_argument("--qwen25-rho-cache", type=Path, default=Path("results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl"))
    parser.add_argument("--qwen3-rho-cache", type=Path, default=Path("results/reference_distributions/qwen3_pytorch_rho_strip_identity.jsonl"))
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--thresholds", type=parse_float_list, default=[1e-6, 1e-5, 1e-4, 1e-3, 1e-2])
    parser.add_argument("--nlhf-taus", type=parse_float_list, default=DEFAULT_NLHF_TAUS)
    parser.add_argument("--rtbt-betas", type=parse_float_list, default=DEFAULT_RTBT_BETAS)
    parser.add_argument(
        "--nlhf-axioms",
        type=parse_axiom_list,
        default=["monotonicity", "positive_involvement", "negative_involvement", "commutativity"],
        help="Comma-separated NLHF axioms to cache.",
    )
    parser.add_argument("--skip-rtbt", action="store_true", help="Skip RTBT involvement caching.")
    parser.add_argument("--comm-max-unique-rankings", type=int, default=12)
    parser.add_argument("--recompute", action="store_true")
    args = parser.parse_args()

    cache_path = args.cache_path or (args.output_dir / "violation_effects.jsonl")
    model_refs = [
        ReferenceConfig("nemo_base_strip_identity", args.nemo_rho_cache),
        ReferenceConfig("qwen25_base_strip_identity", args.qwen25_rho_cache),
        ReferenceConfig("qwen3_base_strip_identity", args.qwen3_rho_cache),
    ]
    model_aliases = [ref.name for ref in model_refs]
    nlhf_cases = load_cases_tie_norm(args.dataset, ["world", "personal"])
    rtbt_cases = load_rtbt_cases(args.dataset, ["world", "personal"])

    if args.recompute or not cache_path.exists():
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        cache_path.write_text("")
        comm_stop_effect = max(args.thresholds)
        for ref in model_refs:
            rho_cache = load_rho_cache(ref.rho_cache)
            rtbt_cache = load_rtbt_rho_cache(ref.rho_cache)
            for tau in args.nlhf_taus:
                for axiom in args.nlhf_axioms:
                    rows = run_nlhf_effects(
                        nlhf_cases,
                        ref,
                        rho_cache,
                        tau,
                        axiom,
                        args.workers,
                        args.comm_max_unique_rankings,
                        comm_stop_effect,
                    )
                    append_jsonl(cache_path, rows)
                    print(json.dumps({"model_alias": ref.name, "rule": "nlhf_tie_norm", "axiom": axiom, "param_value": tau, "cached_witnesses": len(rows)}, sort_keys=True), flush=True)
            if args.skip_rtbt:
                continue
            for beta in args.rtbt_betas:
                for axiom in ("positive_involvement", "negative_involvement"):
                    scenario = Scenario(
                        name=f"{ref.name}_rtbt_{axiom}_beta_{beta}",
                        axiom=axiom,
                        rule="rtbt",
                        param=beta,
                        model_alias=ref.name,
                        rho_source=str(ref.rho_cache),
                        ppi_mode="removal_only",
                    )
                    witnesses = run_rtbt_scenario(rtbt_cases, rtbt_cache, scenario, args.workers)
                    rows = [
                        {
                            "model_alias": ref.name,
                            "rule": "rtbt",
                            "axiom": axiom,
                            "param_name": "beta",
                            "param_value": beta,
                            "prompt_id": witness["prompt_id"],
                            "block_name": witness["block_name"],
                            "profile_key": f"{witness['prompt_id']}:{witness['block_name']}",
                            "effect": float(witness["effect"]),
                        }
                        for witness in witnesses
                        if witness["effect"] > 0
                    ]
                    append_jsonl(cache_path, rows)
                    print(json.dumps({"model_alias": ref.name, "rule": "rtbt", "axiom": axiom, "param_value": beta, "cached_witnesses": len(rows)}, sort_keys=True), flush=True)

    effect_rows = load_effect_rows(cache_path)
    for threshold in args.thresholds:
        rows = threshold_rows(
            effect_rows,
            model_aliases,
            args.nlhf_taus,
            args.rtbt_betas,
            threshold,
            len(nlhf_cases),
            len(rtbt_cases),
        )
        write_threshold_outputs(rows, args.output_dir, threshold)
        plot_rows(rows, args.output_dir, "model_only_reference_involvement_parameter_sweeps")
    print(json.dumps({"cache": str(cache_path), "thresholds": args.thresholds, "effect_rows": len(effect_rows)}, sort_keys=True))


if __name__ == "__main__":
    main()
