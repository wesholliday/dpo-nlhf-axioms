#!/usr/bin/env python3
"""Search CoVal for violations under fixed model-induced reference distributions."""

from __future__ import annotations

import argparse
import csv
import json
import multiprocessing as mp
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

import numpy as np

from scripts.theory.analyze_coval_lb_vs_pb import solve_nlhf
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases
from scripts.theory.search_coval_violation_counts import (
    demotions,
    improvements,
    monotonicity_move_valid,
    ranking_to_wins,
    singleton_top_ballots,
)
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda


@dataclass(frozen=True)
class Scenario:
    name: str
    axiom: str
    rule: str
    param: float
    model_alias: str
    rho_source: str
    ppi_mode: str = "both"


def solve_rule(rule: str, param: float, wins: np.ndarray, rho: np.ndarray) -> np.ndarray | None:
    if rule == "nlhf":
        return solve_nlhf(param, wins, rho)
    if rule == "rtbt":
        return solve_weighted_logistic_borda(param, wins, rho)
    raise ValueError(f"Unknown rule: {rule}")


def load_rho_cache(path: Path) -> dict[str, dict]:
    out: dict[str, dict] = {}
    with path.open() as handle:
        for line in handle:
            obj = json.loads(line)
            prompt_id = obj.get("prompt_id")
            rho = obj.get("rho")
            if not isinstance(prompt_id, str) or not isinstance(rho, dict):
                continue
            out[prompt_id] = obj
    return out


def rho_for_case(case, rho_record: dict) -> np.ndarray:
    labels = case.response_indices
    rho_map = rho_record["rho"]
    rho = np.asarray([float(rho_map[label]) for label in labels], dtype=float)
    total = float(np.sum(rho))
    if total <= 0:
        raise ValueError(f"Nonpositive rho mass for prompt {case.prompt_id}")
    return rho / total


def best_monotonicity_witness(case, scenario: Scenario, rho_record: dict) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total = np.array(case.total_wins, dtype=float)
    wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]
    rho = rho_for_case(case, rho_record)
    observed = solve_rule(scenario.rule, scenario.param, total, rho)
    if observed is None:
        return None

    best: dict | None = None
    for ai, ranking in enumerate(case.rankings):
        old_blocks = [block.split("=") for block in ranking.replace(" ", "").split(">")]

        for cand in labels:
            idx = index[cand]

            for new_ranking in improvements(old_blocks, cand):
                new_blocks = [block.split("=") for block in new_ranking.replace(" ", "").split(">")]
                if not monotonicity_move_valid(old_blocks, new_blocks, cand, labels):
                    continue
                modified = total - wins_per[ai] + ranking_to_wins(new_ranking, index)
                after = solve_rule(scenario.rule, scenario.param, modified, rho)
                if after is None:
                    continue
                drop = float(observed[idx] - after[idx])
                if drop <= 0:
                    continue
                witness = {
                    "prompt_id": case.prompt_id,
                    "block_name": case.block_name,
                    "prompt": case.prompt,
                    "scenario": scenario.name,
                    "axiom": scenario.axiom,
                    "rule": scenario.rule,
                    "param": scenario.param,
                    "model_alias": scenario.model_alias,
                    "rho_source": scenario.rho_source,
                    "rho": rho.tolist(),
                    "response_logprobs": rho_record.get("response_logprobs"),
                    "effect": drop,
                    "candidate": cand,
                    "observed_role": "P",
                    "assessment_index": ai,
                    "old_ranking": ranking,
                    "new_ranking": new_ranking,
                    "before": observed.tolist(),
                    "after": after.tolist(),
                    "response_indices": labels,
                    "n_assessments": len(case.rankings),
                }
                if best is None or drop > best["effect"]:
                    best = witness

            for new_ranking in demotions(old_blocks, cand):
                new_blocks = [block.split("=") for block in new_ranking.replace(" ", "").split(">")]
                if not monotonicity_move_valid(new_blocks, old_blocks, cand, labels):
                    continue
                modified = total - wins_per[ai] + ranking_to_wins(new_ranking, index)
                before = solve_rule(scenario.rule, scenario.param, modified, rho)
                if before is None:
                    continue
                drop = float(before[idx] - observed[idx])
                if drop <= 0:
                    continue
                witness = {
                    "prompt_id": case.prompt_id,
                    "block_name": case.block_name,
                    "prompt": case.prompt,
                    "scenario": scenario.name,
                    "axiom": scenario.axiom,
                    "rule": scenario.rule,
                    "param": scenario.param,
                    "model_alias": scenario.model_alias,
                    "rho_source": scenario.rho_source,
                    "rho": rho.tolist(),
                    "response_logprobs": rho_record.get("response_logprobs"),
                    "effect": drop,
                    "candidate": cand,
                    "observed_role": "Pplus",
                    "assessment_index": ai,
                    "old_ranking": new_ranking,
                    "new_ranking": ranking,
                    "before": before.tolist(),
                    "after": observed.tolist(),
                    "response_indices": labels,
                    "n_assessments": len(case.rankings),
                }
                if best is None or drop > best["effect"]:
                    best = witness

    return best


def best_positive_involvement_witness(case, scenario: Scenario, rho_record: dict) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total = np.array(case.total_wins, dtype=float)
    wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]
    rho = rho_for_case(case, rho_record)
    observed = solve_rule(scenario.rule, scenario.param, total, rho)
    if observed is None:
        return None

    best: dict | None = None
    ppi_mode = scenario.ppi_mode
    if ppi_mode not in {"both", "removal_only", "addition_only"}:
        raise ValueError(f"Unknown ppi_mode: {ppi_mode}")

    if ppi_mode in {"both", "removal_only"}:
        for ai, ranking in enumerate(case.rankings):
            blocks = [block.split("=") for block in ranking.replace(" ", "").split(">")]
            if not blocks or len(blocks[0]) != 1:
                continue
            cand = blocks[0][0]
            reduced = total - wins_per[ai]
            before = solve_rule(scenario.rule, scenario.param, reduced, rho)
            if before is None:
                continue
            idx = index[cand]
            drop = float(before[idx] - observed[idx])
            if drop <= 0:
                continue
            witness = {
                "prompt_id": case.prompt_id,
                "block_name": case.block_name,
                "prompt": case.prompt,
                "scenario": scenario.name,
                "axiom": scenario.axiom,
                "rule": scenario.rule,
                "param": scenario.param,
                "model_alias": scenario.model_alias,
                "rho_source": scenario.rho_source,
                "rho": rho.tolist(),
                "response_logprobs": rho_record.get("response_logprobs"),
                "effect": drop,
                "candidate": cand,
                "observed_role": "Pplus",
                "assessment_index": ai,
                "added_ballot": ranking,
                "before": before.tolist(),
                "after": observed.tolist(),
                "response_indices": labels,
                "n_assessments": len(case.rankings),
            }
            if best is None or drop > best["effect"]:
                best = witness

    if ppi_mode in {"both", "addition_only"}:
        top_ballots = singleton_top_ballots(labels)
        for cand in labels:
            idx = index[cand]
            for ballot in top_ballots[cand]:
                added = total + ranking_to_wins(ballot, index)
                after = solve_rule(scenario.rule, scenario.param, added, rho)
                if after is None:
                    continue
                drop = float(observed[idx] - after[idx])
                if drop <= 0:
                    continue
                witness = {
                    "prompt_id": case.prompt_id,
                    "block_name": case.block_name,
                    "prompt": case.prompt,
                    "scenario": scenario.name,
                    "axiom": scenario.axiom,
                    "rule": scenario.rule,
                    "param": scenario.param,
                    "model_alias": scenario.model_alias,
                    "rho_source": scenario.rho_source,
                    "rho": rho.tolist(),
                    "response_logprobs": rho_record.get("response_logprobs"),
                    "effect": drop,
                    "candidate": cand,
                    "observed_role": "P",
                    "added_ballot": ballot,
                    "before": observed.tolist(),
                    "after": after.tolist(),
                    "response_indices": labels,
                    "n_assessments": len(case.rankings),
                }
                if best is None or drop > best["effect"]:
                    best = witness

    return best


def strictly_last_candidate(
    ranking: str,
    labels: Sequence[str],
) -> str | None:
    blocks = [block.split("=") for block in ranking.replace(" ", "").split(">")]
    if not blocks or len(blocks[-1]) != 1:
        return None
    seen = {cand for block in blocks for cand in block}
    if set(labels) != seen:
        return None
    return blocks[-1][0]


def best_negative_involvement_witness(case, scenario: Scenario, rho_record: dict) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total = np.array(case.total_wins, dtype=float)
    wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]
    rho = rho_for_case(case, rho_record)
    observed = solve_rule(scenario.rule, scenario.param, total, rho)
    if observed is None:
        return None

    best: dict | None = None
    for ai, ranking in enumerate(case.rankings):
        cand = strictly_last_candidate(ranking, labels)
        if cand is None:
            continue
        reduced = total - wins_per[ai]
        before = solve_rule(scenario.rule, scenario.param, reduced, rho)
        if before is None:
            continue
        idx = index[cand]
        gain = float(observed[idx] - before[idx])
        if gain <= 0:
            continue
        witness = {
            "prompt_id": case.prompt_id,
            "block_name": case.block_name,
            "prompt": case.prompt,
            "scenario": scenario.name,
            "axiom": scenario.axiom,
            "rule": scenario.rule,
            "param": scenario.param,
            "model_alias": scenario.model_alias,
            "rho_source": scenario.rho_source,
            "rho": rho.tolist(),
            "response_logprobs": rho_record.get("response_logprobs"),
            "effect": gain,
            "candidate": cand,
            "observed_role": "Pplus",
            "assessment_index": ai,
            "added_ballot": ranking,
            "before": before.tolist(),
            "after": observed.tolist(),
            "response_indices": labels,
            "n_assessments": len(case.rankings),
        }
        if best is None or gain > best["effect"]:
            best = witness

    return best


def worker(
    worker_id: int,
    cases: Sequence,
    rho_cache: dict[str, dict],
    scenario: Scenario,
) -> list[dict]:
    out: list[dict] = []
    for case in cases:
        rho_record = rho_cache.get(case.prompt_id)
        if rho_record is None:
            continue
        if scenario.axiom == "monotonicity":
            witness = best_monotonicity_witness(case, scenario, rho_record)
        elif scenario.axiom == "positive_involvement":
            witness = best_positive_involvement_witness(case, scenario, rho_record)
        elif scenario.axiom == "negative_involvement":
            witness = best_negative_involvement_witness(case, scenario, rho_record)
        else:
            raise ValueError(f"Unknown axiom: {scenario.axiom}")
        if witness is not None:
            out.append(witness)
    return out


def scenario_summary(cases: Sequence, witnesses: Sequence[dict]) -> dict:
    total = len(cases)
    witness_keys = {f"{w['prompt_id']}:{w['block_name']}" for w in witnesses}
    block_totals: dict[str, int] = {}
    block_hits: dict[str, int] = {}
    for case in cases:
        key = f"{case.prompt_id}:{case.block_name}"
        block_totals[case.block_name] = block_totals.get(case.block_name, 0) + 1
        if key in witness_keys:
            block_hits[case.block_name] = block_hits.get(case.block_name, 0) + 1
    return {
        "profiles_total": total,
        "profiles_with_witness": len(witness_keys),
        "fraction_with_witness": (len(witness_keys) / total) if total else 0.0,
        "by_block": {
            block: {
                "total": block_totals.get(block, 0),
                "with_witness": block_hits.get(block, 0),
                "fraction": (
                    block_hits.get(block, 0) / block_totals.get(block, 1)
                    if block_totals.get(block, 0)
                    else 0.0
                ),
            }
            for block in sorted(block_totals)
        },
    }


def write_outputs(output_dir: Path, scenario: Scenario, witnesses: Sequence[dict], summary: dict) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    jsonl_path = output_dir / f"{scenario.name}.jsonl"
    summary_path = output_dir / f"{scenario.name}.summary.json"
    csv_path = output_dir / f"{scenario.name}.summary.csv"

    with jsonl_path.open("w") as handle:
        for witness in sorted(witnesses, key=lambda w: (w["block_name"], w["prompt_id"])):
            handle.write(json.dumps(witness, sort_keys=True) + "\n")

    with summary_path.open("w") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True)
        handle.write("\n")

    with csv_path.open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["block_name", "profiles_total", "profiles_with_witness", "fraction_with_witness"])
        for block_name, block_summary in summary["by_block"].items():
            writer.writerow(
                [
                    block_name,
                    block_summary["total"],
                    block_summary["with_witness"],
                    block_summary["fraction"],
                ]
            )
        writer.writerow(
            [
                "ALL",
                summary["profiles_total"],
                summary["profiles_with_witness"],
                summary["fraction_with_witness"],
            ]
        )


def default_scenarios(model_alias: str, rho_source: str) -> list[Scenario]:
    return [
        Scenario(
            name=f"{model_alias}_nlhf_monotonicity_tau_0.01_strict",
            axiom="monotonicity",
            rule="nlhf",
            param=0.01,
            model_alias=model_alias,
            rho_source=rho_source,
        ),
        Scenario(
            name=f"{model_alias}_nlhf_positive_involvement_tau_0.01",
            axiom="positive_involvement",
            rule="nlhf",
            param=0.01,
            model_alias=model_alias,
            rho_source=rho_source,
            ppi_mode="removal_only",
        ),
        Scenario(
            name=f"{model_alias}_rtbt_positive_involvement_beta_0.1",
            axiom="positive_involvement",
            rule="rtbt",
            param=0.1,
            model_alias=model_alias,
            rho_source=rho_source,
            ppi_mode="removal_only",
        ),
        Scenario(
            name=f"{model_alias}_nlhf_negative_involvement_tau_0.01",
            axiom="negative_involvement",
            rule="nlhf",
            param=0.01,
            model_alias=model_alias,
            rho_source=rho_source,
        ),
        Scenario(
            name=f"{model_alias}_rtbt_negative_involvement_beta_0.1",
            axiom="negative_involvement",
            rule="rtbt",
            param=0.1,
            model_alias=model_alias,
            rho_source=rho_source,
        ),
    ]


def run_scenario(cases: Sequence, rho_cache: dict[str, dict], scenario: Scenario, workers: int, output_dir: Path) -> dict:
    chunks: list[list] = [[] for _ in range(workers)]
    for i, case in enumerate(cases):
        chunks[i % workers].append(case)

    ctx = mp.get_context("fork")
    with ctx.Pool(workers) as pool:
        pieces = pool.starmap(
            worker,
            [(worker_id, chunks[worker_id], rho_cache, scenario) for worker_id in range(workers)],
        )

    witnesses = [w for piece in pieces for w in piece]
    summary = scenario_summary(cases, witnesses)
    write_outputs(output_dir, scenario, witnesses, summary)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--rho-cache", type=Path, required=True)
    parser.add_argument("--model-alias", required=True)
    parser.add_argument("--workers", type=int, default=32)
    parser.add_argument("--blocks", nargs="+", default=["world", "personal"])
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/theory/model_reference_violations"),
    )
    args = parser.parse_args()

    cases = load_cases(args.dataset, args.blocks)
    if not cases:
        raise SystemExit("No eligible CoVal cases found.")

    rho_cache = load_rho_cache(args.rho_cache)
    if not rho_cache:
        raise SystemExit("No rho records found in cache.")

    all_summary: dict[str, dict] = {}
    for scenario in default_scenarios(args.model_alias, str(args.rho_cache)):
        summary = run_scenario(cases, rho_cache, scenario, args.workers, args.output_dir)
        all_summary[scenario.name] = summary
        print(json.dumps({"scenario": scenario.name, **summary}, sort_keys=True))

    combined_path = args.output_dir / f"{args.model_alias}_all_summaries.json"
    with combined_path.open("w") as handle:
        json.dump(all_summary, handle, indent=2, sort_keys=True)
        handle.write("\n")


if __name__ == "__main__":
    main()
