#!/usr/bin/env python3
"""Search CoVal for reverse monotonicity witnesses for NLHF."""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

import numpy as np

from scripts.theory.nlhf_solver import solve_nlhf


@dataclass(frozen=True)
class Case:
    prompt_id: str
    prompt: str
    block_name: str
    response_indices: tuple[str, ...]
    rankings: tuple[str, ...]
    wins_per_ranking: tuple[tuple[tuple[float, ...], ...], ...]
    total_wins: tuple[tuple[float, ...], ...]


def parse_ranking(text: str) -> list[list[str]]:
    compact = text.replace(" ", "")
    return [block.split("=") for block in compact.split(">")]


def ranking_to_string(blocks: Sequence[Sequence[str]]) -> str:
    return ">".join("=".join(block) for block in blocks)


def ranking_to_wins(ranking: str, index: dict[str, int]) -> np.ndarray:
    wins = np.zeros((4, 4), dtype=float)
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
    for pos in range(src_after + 1, len(base) + 1):
        new_blocks = [list(block) for block in base]
        new_blocks.insert(pos, [cand])
        text = ranking_to_string(new_blocks)
        if text != original and text not in seen:
            seen.add(text)
            out.append(text)
    for pos in range(src_after + 1, len(base)):
        new_blocks = [list(block) for block in base]
        new_blocks[pos] = new_blocks[pos] + [cand]
        text = ranking_to_string(new_blocks)
        if text != original and text not in seen:
            seen.add(text)
            out.append(text)
    return out


def margin_matrix(wins: np.ndarray) -> np.ndarray:
    return wins - wins.T


def load_cases(path: Path, block_names: Sequence[str]) -> list[Case]:
    block_set = set(block_names)
    cases: list[Case] = []
    with path.open() as handle:
        for line in handle:
            obj = json.loads(line)
            responses = obj["responses"]
            if len(responses) != 4:
                continue
            response_indices = tuple(r["response_index"] for r in responses)
            index = {response_index: i for i, response_index in enumerate(response_indices)}
            grouped: dict[str, list[str]] = {name: [] for name in block_set}
            for assessment in obj.get("metadata", {}).get("assessments", []):
                for block_name in block_set:
                    for block in assessment.get("ranking_blocks", {}).get(block_name, []):
                        ranking = block.get("ranking")
                        if ranking:
                            grouped[block_name].append(ranking)
            for block_name, rankings in grouped.items():
                if not rankings:
                    continue
                wins_per = [ranking_to_wins(ranking, index) for ranking in rankings]
                total = np.sum(wins_per, axis=0)
                cases.append(
                    Case(
                        prompt_id=obj["prompt_id"],
                        prompt=obj.get("prompt", ""),
                        block_name=block_name,
                        response_indices=response_indices,
                        rankings=tuple(rankings),
                        wins_per_ranking=tuple(tuple(tuple(float(x) for x in row) for row in wins) for wins in wins_per),
                        total_wins=tuple(tuple(float(x) for x in row) for row in total),
                    )
                )
    return cases


def format_rho(rho: Sequence[float], labels: Sequence[str]) -> str:
    return ", ".join(f"{lab}={val:.12g}" for lab, val in zip(labels, rho))


def worker(
    worker_id: int,
    cases: Sequence[Case],
    tau: float,
    trials: int,
    random_rho_samples: int,
    rho_alpha: float,
) -> tuple[dict | None, dict | None]:
    rng = random.Random(30_000 + worker_id)
    np_rng = np.random.default_rng(40_000 + worker_id)
    uniform = np.full(4, 0.25, dtype=float)
    best_uniform: dict | None = None
    best_random: dict | None = None

    for _ in range(trials):
        case = cases[rng.randrange(len(cases))]
        rankings = case.rankings
        response_indices = case.response_indices
        total = np.array(case.total_wins, dtype=float)
        wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]

        ai = rng.randrange(len(rankings))
        ranking = rankings[ai]
        blocks = parse_ranking(ranking)
        present = [cand for block in blocks for cand in block]
        cand = present[rng.randrange(len(present))]
        candidates = demotions(blocks, cand)
        if not candidates:
            continue
        new_ranking = candidates[rng.randrange(len(candidates))]
        index = {response_index: i for i, response_index in enumerate(response_indices)}
        if not monotonicity_move_valid(parse_ranking(new_ranking), blocks, cand, response_indices):
            continue
        new_total = total - wins_per[ai] + ranking_to_wins(new_ranking, index)

        before = solve_nlhf(tau, total, uniform)
        after = solve_nlhf(tau, new_total, uniform)
        if before is not None and after is not None:
            idx = index[cand]
            inc = float(after[idx] - before[idx])
            if best_uniform is None or inc > best_uniform["increase"]:
                best_uniform = {
                    "increase": inc,
                    "prompt_id": case.prompt_id,
                    "block_name": case.block_name,
                    "candidate": cand,
                    "old_ranking": ranking,
                    "new_ranking": new_ranking,
                    "before": before.tolist(),
                    "after": after.tolist(),
                    "n_assessments": len(rankings),
                    "response_indices": response_indices,
                    "prompt": case.prompt,
                }

        for _ in range(random_rho_samples):
            rho = np_rng.dirichlet(np.full(4, rho_alpha))
            before = solve_nlhf(tau, total, rho)
            after = solve_nlhf(tau, new_total, rho)
            if before is None or after is None:
                continue
            idx = index[cand]
            inc = float(after[idx] - before[idx])
            if best_random is None or inc > best_random["increase"]:
                best_random = {
                    "increase": inc,
                    "prompt_id": case.prompt_id,
                    "block_name": case.block_name,
                    "candidate": cand,
                    "old_ranking": ranking,
                    "new_ranking": new_ranking,
                    "before": before.tolist(),
                    "after": after.tolist(),
                    "rho": rho.tolist(),
                    "n_assessments": len(rankings),
                    "response_indices": response_indices,
                    "prompt": case.prompt,
                }

    return best_uniform, best_random


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--tau", type=float, default=0.01)
    parser.add_argument("--workers", type=int, default=32)
    parser.add_argument("--trials-per-worker", type=int, default=5000)
    parser.add_argument("--random-rho-samples", type=int, default=6)
    parser.add_argument("--rho-alpha", type=float, default=0.2)
    parser.add_argument("--blocks", nargs="+", default=["world", "personal"])
    args = parser.parse_args()

    cases = load_cases(args.dataset, args.blocks)
    if not cases:
        raise SystemExit("No eligible CoVal cases found.")

    ctx = mp.get_context("fork")
    with ctx.Pool(args.workers) as pool:
        results = pool.starmap(
            worker,
            [
                (
                    worker_id,
                    cases,
                    args.tau,
                    args.trials_per_worker,
                    args.random_rho_samples,
                    args.rho_alpha,
                )
                for worker_id in range(args.workers)
            ],
        )

    best_uniform = max(
        (item[0] for item in results if item[0] is not None),
        key=lambda witness: witness["increase"],
        default=None,
    )
    best_random = max(
        (item[1] for item in results if item[1] is not None),
        key=lambda witness: witness["increase"],
        default=None,
    )

    print(f"cases={len(cases)} tau={args.tau}")
    print("BEST_UNIFORM")
    print(json.dumps(best_uniform, indent=2))
    print("BEST_RANDOM")
    print(json.dumps(best_random, indent=2))
    if best_random is not None:
        print("BEST_RANDOM_RHO")
        print(format_rho(best_random["rho"], best_random["response_indices"]))


if __name__ == "__main__":
    main()
