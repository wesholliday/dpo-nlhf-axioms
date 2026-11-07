#!/usr/bin/env python3
"""Exhaustive CoVal witness search with one strongest witness per profile.

This script searches CoVal profiles for witnessable violations arising from
single-profile modifications:

* NLHF probabilistic monotonicity
* NLHF probabilistic positive involvement
* RTBT probabilistic positive involvement

For each search scenario, the script saves at most one strongest witness per
profile (prompt id + block name), then writes JSONL and summary files to disk.
"""

from __future__ import annotations

import argparse
import csv
import json
import multiprocessing as mp
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

from scripts.coval.profiles import strictly_first_candidate

from scripts.theory.nlhf_solver import solve_nlhf
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases, parse_ranking
from scripts.theory.search_strict_weak_positive_involvement import (
    OrderedPartition,
    ordered_partitions,
    solve_weighted_logistic_borda,
)


@dataclass(frozen=True)
class Scenario:
    name: str
    axiom: str
    rule: str
    param: float
    rho_mode: str
    rho_samples: int = 1
    rho_alpha: float = 0.2


def ranking_to_string(blocks: Sequence[Sequence[str]]) -> str:
    return ">".join("=".join(block) for block in blocks)


def ranking_to_wins(ranking: str, index: dict[str, int]) -> np.ndarray:
    wins = np.zeros((len(index), len(index)), dtype=float)
    blocks = parse_ranking(ranking)
    for i, current in enumerate(blocks):
        for later in blocks[i + 1 :]:
            for left in current:
                for right in later:
                    wins[index[left], index[right]] += 1.0
    return wins


def relation_map(blocks: Sequence[Sequence[str]], labels: Sequence[str]) -> dict[tuple[str, str], bool]:
    pos: dict[str, int] = {}
    for level, block in enumerate(blocks):
        for cand in block:
            pos[cand] = level

    rel: dict[tuple[str, str], bool] = {}
    for left in labels:
        for right in labels:
            if left == right:
                continue
            left_pos = pos.get(left)
            right_pos = pos.get(right)
            rel[(left, right)] = (
                left_pos is not None
                and right_pos is not None
                and left_pos < right_pos
            )
    return rel


def monotonicity_move_valid(
    old_blocks: Sequence[Sequence[str]],
    new_blocks: Sequence[Sequence[str]],
    cand: str,
    labels: Sequence[str],
) -> bool:
    old_rel = relation_map(old_blocks, labels)
    new_rel = relation_map(new_blocks, labels)

    for other in labels:
        if other == cand:
            continue
        if old_rel[(cand, other)] and not new_rel[(cand, other)]:
            return False
        if new_rel[(other, cand)] and not old_rel[(other, cand)]:
            return False

    for left in labels:
        if left == cand:
            continue
        for right in labels:
            if right == cand or right == left:
                continue
            if old_rel[(left, right)] != new_rel[(left, right)]:
                return False

    return True


def solve_rule(rule: str, param: float, wins: np.ndarray, rho: np.ndarray) -> np.ndarray | None:
    if rule == "nlhf":
        return solve_nlhf(param, wins, rho)
    if rule == "rtbt":
        return solve_weighted_logistic_borda(param, wins, rho)
    raise ValueError(f"Unknown rule: {rule}")


def improvements(blocks: Sequence[Sequence[str]], cand: str) -> list[str]:
    original = ranking_to_string(blocks)
    src = None
    for i, block in enumerate(blocks):
        if cand in block:
            src = i
            break

    if src is None:
        base = [list(block) for block in blocks]
        out: list[str] = []
        seen: set[str] = set()
        for pos in range(len(base) + 1):
            new_blocks = [list(block) for block in base]
            new_blocks.insert(pos, [cand])
            text = ranking_to_string(new_blocks)
            if text != original and text not in seen:
                seen.add(text)
                out.append(text)
        for pos in range(len(base)):
            new_blocks = [list(block) for block in base]
            new_blocks[pos] = new_blocks[pos] + [cand]
            text = ranking_to_string(new_blocks)
            if text != original and text not in seen:
                seen.add(text)
                out.append(text)
        return out

    base = [list(block) for block in blocks]
    base[src] = [x for x in base[src] if x != cand]
    if not base[src]:
        del base[src]

    out: list[str] = []
    seen: set[str] = set()
    for pos in range(src):
        new_blocks = [list(block) for block in base]
        new_blocks.insert(pos, [cand])
        text = ranking_to_string(new_blocks)
        if text != original and text not in seen:
            seen.add(text)
            out.append(text)
    for pos in range(src):
        new_blocks = [list(block) for block in base]
        new_blocks[pos] = new_blocks[pos] + [cand]
        text = ranking_to_string(new_blocks)
        if text != original and text not in seen:
            seen.add(text)
            out.append(text)
    return out


def demotions(blocks: Sequence[Sequence[str]], cand: str) -> list[str]:
    original = ranking_to_string(blocks)
    src = None
    for i, block in enumerate(blocks):
        if cand in block:
            src = i
            break
    if src is None:
        return []

    base = [list(block) for block in blocks]
    base[src] = [x for x in base[src] if x != cand]
    if not base[src]:
        del base[src]
        src_after = src - 1
    else:
        src_after = src

    out: list[str] = []
    seen: set[str] = set()

    # Demote by leaving the candidate unranked.
    text = ranking_to_string(base)
    if text != original:
        seen.add(text)
        out.append(text)

    # Demote by inserting into a later singleton block.
    for pos in range(src_after + 1, len(base) + 1):
        new_blocks = [list(block) for block in base]
        new_blocks.insert(pos, [cand])
        text = ranking_to_string(new_blocks)
        if text != original and text not in seen:
            seen.add(text)
            out.append(text)

    # Demote by tying with a later block.
    for pos in range(src_after + 1, len(base)):
        new_blocks = [list(block) for block in base]
        new_blocks[pos] = new_blocks[pos] + [cand]
        text = ranking_to_string(new_blocks)
        if text != original and text not in seen:
            seen.add(text)
            out.append(text)

    return out


def singleton_top_ballots(labels: Sequence[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for cand in labels:
        rest = [label for label in labels if label != cand]
        rankings: list[str] = []
        for partition in ordered_partitions(rest):
            full: OrderedPartition = ((cand,),) + partition
            rankings.append(ranking_to_string(full))
        out[cand] = rankings
    return out


def profile_key(case) -> str:
    return f"{case.prompt_id}:{case.block_name}"


def make_rhos(
    scenario: Scenario,
    labels: Sequence[str],
    seed: int,
) -> Iterable[tuple[str, np.ndarray]]:
    if scenario.rho_mode == "uniform":
        yield ("uniform", np.full(len(labels), 1.0 / len(labels), dtype=float))
        return

    if scenario.rho_mode == "dirichlet":
        rng = np.random.default_rng(seed)
        for i in range(scenario.rho_samples):
            rho = rng.dirichlet(np.full(len(labels), scenario.rho_alpha, dtype=float))
            yield (f"dirichlet_{i}", rho)
        return

    raise ValueError(f"Unknown rho mode: {scenario.rho_mode}")


def best_monotonicity_witness(case, scenario: Scenario, worker_seed: int) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total = np.array(case.total_wins, dtype=float)
    wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]
    best: dict | None = None

    for rho_name, rho in make_rhos(scenario, labels, worker_seed):
        observed = solve_rule(scenario.rule, scenario.param, total, rho)
        if observed is None:
            continue

        for ai, ranking in enumerate(case.rankings):
            blocks = parse_ranking(ranking)

            for cand in labels:
                idx = index[cand]

                for new_ranking in improvements(blocks, cand):
                    new_blocks = parse_ranking(new_ranking)
                    if not monotonicity_move_valid(blocks, new_blocks, cand, labels):
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
                        "rho_mode": scenario.rho_mode,
                        "rho_name": rho_name,
                        "rho": rho.tolist(),
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

                for new_ranking in demotions(blocks, cand):
                    new_blocks = parse_ranking(new_ranking)
                    if not monotonicity_move_valid(new_blocks, blocks, cand, labels):
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
                        "rho_mode": scenario.rho_mode,
                        "rho_name": rho_name,
                        "rho": rho.tolist(),
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


def best_positive_involvement_witness(case, scenario: Scenario, worker_seed: int) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total = np.array(case.total_wins, dtype=float)
    wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]
    top_ballots = singleton_top_ballots(labels)
    best: dict | None = None

    for rho_name, rho in make_rhos(scenario, labels, worker_seed):
        observed = solve_rule(scenario.rule, scenario.param, total, rho)
        if observed is None:
            continue

        # Observed profile serves as P^+ by deleting one top-singleton ballot.
        for ai, ranking in enumerate(case.rankings):
            blocks = parse_ranking(ranking)
            cand = strictly_first_candidate(ranking, labels)
            if cand is None:
                continue
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
                "rho_mode": scenario.rho_mode,
                "rho_name": rho_name,
                "rho": rho.tolist(),
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

        # Observed profile serves as P by adding one top-singleton ballot.
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
                    "rho_mode": scenario.rho_mode,
                    "rho_name": rho_name,
                    "rho": rho.tolist(),
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


def worker(
    worker_id: int,
    cases: Sequence,
    scenario: Scenario,
) -> list[dict]:
    out: list[dict] = []
    for j, case in enumerate(cases):
        seed = 100_000 * (worker_id + 1) + j
        if scenario.axiom == "monotonicity":
            witness = best_monotonicity_witness(case, scenario, seed)
        elif scenario.axiom == "positive_involvement":
            witness = best_positive_involvement_witness(case, scenario, seed)
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
        block_totals[case.block_name] = block_totals.get(case.block_name, 0) + 1
        if profile_key(case) in witness_keys:
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


def default_scenarios() -> list[Scenario]:
    return [
        Scenario(
            name="nlhf_monotonicity_uniform_tau_0.01_strict",
            axiom="monotonicity",
            rule="nlhf",
            param=0.01,
            rho_mode="uniform",
        ),
        Scenario(
            name="nlhf_positive_involvement_uniform_tau_0.01",
            axiom="positive_involvement",
            rule="nlhf",
            param=0.01,
            rho_mode="uniform",
        ),
        Scenario(
            name="rtbt_positive_involvement_uniform_beta_0.1",
            axiom="positive_involvement",
            rule="rtbt",
            param=0.1,
            rho_mode="uniform",
        ),
    ]


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


def run_scenario(cases: Sequence, scenario: Scenario, workers: int, output_dir: Path) -> dict:
    chunks: list[list] = [[] for _ in range(workers)]
    for i, case in enumerate(cases):
        chunks[i % workers].append(case)

    ctx = mp.get_context("fork")
    with ctx.Pool(workers) as pool:
        pieces = pool.starmap(
            worker,
            [(worker_id, chunks[worker_id], scenario) for worker_id in range(workers)],
        )

    witnesses = [w for piece in pieces for w in piece]
    summary = scenario_summary(cases, witnesses)
    write_outputs(output_dir, scenario, witnesses, summary)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--workers", type=int, default=32)
    parser.add_argument("--blocks", nargs="+", default=["world", "personal"])
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/intermediate/coval_violation_search_results"),
    )
    args = parser.parse_args()

    cases = load_cases(args.dataset, args.blocks)
    if not cases:
        raise SystemExit("No eligible CoVal cases found.")

    all_summary: dict[str, dict] = {}
    for scenario in default_scenarios():
        summary = run_scenario(cases, scenario, args.workers, args.output_dir)
        all_summary[scenario.name] = summary
        print(json.dumps({"scenario": scenario.name, **summary}, sort_keys=True))

    combined_path = args.output_dir / "all_summaries.json"
    with combined_path.open("w") as handle:
        json.dump(all_summary, handle, indent=2, sort_keys=True)
        handle.write("\n")


if __name__ == "__main__":
    main()
