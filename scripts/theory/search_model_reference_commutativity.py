#!/usr/bin/env python3
"""Legacy no-tie, balanced-assessment-split commutativity search.

This is not the paper's type-preserving, tie-normalized computation. For the
camera-ready results use scripts.additional_checks.audit_commutativity,
which canonicalizes tied ranking types and composes updates in log space.

For each real CoVal profile P = P1 + P2, where P1 and P2 are a balanced split
of the observed rankings, compare

  NLHF_tau(P2, NLHF_tau(P1, rho))

against

  NLHF_tau(P1, NLHF_tau(P2, rho))

using a fixed per-prompt reference distribution rho loaded from a model cache.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

from scripts.theory.nlhf_solver import solve_nlhf
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases
from scripts.theory.search_model_reference_violation_counts import load_rho_cache, rho_for_case


@dataclass(frozen=True)
class Job:
    prompt_id: str
    prompt: str
    block_name: str
    rankings: tuple[str, ...]
    wins_per_ranking: tuple[tuple[tuple[float, ...], ...], ...]
    response_indices: tuple[str, ...]


def balanced_masks(n: int) -> Iterable[int]:
    """Yield one representative per unordered near-half split.

    We require ranking 0 to lie in the left split, so complements are not
    duplicated. For even n, both sides have size n/2. For odd n, the left side
    has size ceil(n/2) and the right side floor(n/2).
    """

    if n < 2:
        return
    target = (n + 1) // 2

    def rec(start: int, chosen: int, need: int) -> Iterable[int]:
        if need == 0:
            yield chosen
            return
        # Inclusive upper bound leaves enough positions to finish the subset.
        last = n - need
        for idx in range(start, last + 1):
            yield from rec(idx + 1, chosen | (1 << idx), need - 1)

    yield from rec(1, 1, target - 1)


def sampled_balanced_masks(n: int, count: int, rng: np.random.Generator) -> Iterable[int]:
    if n < 2:
        return
    target = (n + 1) // 2
    seen: set[tuple[int, ...]] = set()
    while len(seen) < count:
        tail = rng.choice(np.arange(1, n), size=target - 1, replace=False)
        chosen = tuple(sorted(int(x) for x in tail))
        if chosen in seen:
            continue
        seen.add(chosen)
        mask = 1
        for idx in chosen:
            mask |= 1 << idx
        yield mask


def wins_from_mask(wins_per: Sequence[np.ndarray], mask: int) -> tuple[np.ndarray, np.ndarray]:
    shape = wins_per[0].shape
    wins_left = np.zeros(shape, dtype=float)
    wins_right = np.zeros(shape, dtype=float)
    for i, wins in enumerate(wins_per):
        if mask & (1 << i):
            wins_left += wins
        else:
            wins_right += wins
    return wins_left, wins_right


def evaluate_split(
    tau: float,
    wins_left: np.ndarray,
    wins_right: np.ndarray,
    rho: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray] | None:
    left_ref = solve_nlhf(tau, wins_left, rho)
    if left_ref is None:
        return None
    right_ref = solve_nlhf(tau, wins_right, rho)
    if right_ref is None:
        return None
    left_then_right = solve_nlhf(tau, wins_right, left_ref)
    right_then_left = solve_nlhf(tau, wins_left, right_ref)
    if left_then_right is None or right_then_left is None:
        return None
    return left_ref, right_ref, left_then_right, right_then_left


def witness_record(
    *,
    job: Job,
    mask: int,
    rho: np.ndarray,
    response_logprobs: dict | None,
    left_ref: np.ndarray,
    right_ref: np.ndarray,
    left_then_right: np.ndarray,
    right_then_left: np.ndarray,
) -> dict:
    n = len(job.rankings)
    left_rankings = [job.rankings[i] for i in range(n) if mask & (1 << i)]
    right_rankings = [job.rankings[i] for i in range(n) if not (mask & (1 << i))]
    diff = left_then_right - right_then_left
    argmax = int(np.argmax(np.abs(diff)))
    return {
        "prompt_id": job.prompt_id,
        "prompt": job.prompt,
        "block_name": job.block_name,
        "response_indices": job.response_indices,
        "n_assessments": len(job.rankings),
        "left_size": len(left_rankings),
        "right_size": len(right_rankings),
        "rankings_left": left_rankings,
        "rankings_right": right_rankings,
        "rho": rho.tolist(),
        "response_logprobs": response_logprobs,
        "left_ref": left_ref.tolist(),
        "right_ref": right_ref.tolist(),
        "out_left_then_right": left_then_right.tolist(),
        "out_right_then_left": right_then_left.tolist(),
        "tv_distance": 0.5 * float(np.sum(np.abs(diff))),
        "max_abs_diff": float(np.max(np.abs(diff))),
        "argmax_coord": argmax,
        "argmax_candidate": job.response_indices[argmax],
        "coord_diff": float(diff[argmax]),
    }


def worker(
    worker_id: int,
    jobs: Sequence[Job],
    rho_cache: dict[str, dict],
    tau: float,
    exhaustive_cutoff: int,
    sampled_splits: int,
) -> dict | None:
    rng = np.random.default_rng(90_000 + worker_id)
    best: dict | None = None

    for job in jobs:
        rho_record = rho_cache.get(job.prompt_id)
        if rho_record is None:
            continue

        rho = rho_for_case(job, rho_record)
        wins_per = [np.array(w, dtype=float) for w in job.wins_per_ranking]
        n = len(wins_per)
        if n < 2:
            continue

        if n <= exhaustive_cutoff:
            masks = balanced_masks(n)
        else:
            masks = sampled_balanced_masks(n, sampled_splits, rng)

        for mask in masks:
            wins_left, wins_right = wins_from_mask(wins_per, mask)
            result = evaluate_split(tau, wins_left, wins_right, rho)
            if result is None:
                continue
            left_ref, right_ref, left_then_right, right_then_left = result
            witness = witness_record(
                job=job,
                mask=mask,
                rho=rho,
                response_logprobs=rho_record.get("response_logprobs"),
                left_ref=left_ref,
                right_ref=right_ref,
                left_then_right=left_then_right,
                right_then_left=right_then_left,
            )
            if best is None or witness["tv_distance"] > best["tv_distance"]:
                best = witness

    return best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--rho-cache", type=Path, required=True)
    parser.add_argument("--tau", type=float, default=0.01)
    parser.add_argument("--workers", type=int, default=32)
    parser.add_argument("--exhaustive-cutoff", type=int, default=16)
    parser.add_argument("--sampled-splits", type=int, default=1000)
    parser.add_argument("--blocks", nargs="+", default=["world", "personal"])
    parser.add_argument("--prompt-id")
    parser.add_argument("--block-name")
    parser.add_argument("--output")
    args = parser.parse_args()

    cases = load_cases(args.dataset, args.blocks)
    jobs = [
        Job(
            prompt_id=case.prompt_id,
            prompt=case.prompt,
            block_name=case.block_name,
            rankings=case.rankings,
            wins_per_ranking=case.wins_per_ranking,
            response_indices=case.response_indices,
        )
        for case in cases
        if (args.prompt_id is None or case.prompt_id == args.prompt_id)
        and (args.block_name is None or case.block_name == args.block_name)
    ]
    if not jobs:
        raise SystemExit("No eligible CoVal cases found.")

    rho_cache = load_rho_cache(args.rho_cache)
    if not rho_cache:
        raise SystemExit(f"No rho records found in cache: {args.rho_cache}")

    chunks: list[list[Job]] = [[] for _ in range(args.workers)]
    for i, job in enumerate(jobs):
        chunks[i % args.workers].append(job)

    ctx = mp.get_context("fork")
    with ctx.Pool(args.workers) as pool:
        results = pool.starmap(
            worker,
            [
                (
                    worker_id,
                    chunks[worker_id],
                    rho_cache,
                    args.tau,
                    args.exhaustive_cutoff,
                    args.sampled_splits,
                )
                for worker_id in range(args.workers)
            ],
        )

    best = max(
        (item for item in results if item is not None),
        key=lambda witness: witness["tv_distance"],
        default=None,
    )

    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with output_path.open("w") as handle:
            json.dump(best, handle, indent=2, sort_keys=True)
            handle.write("\n")

    print(
        json.dumps(
            {
                "tau": args.tau,
                "jobs": len(jobs),
                "rho_cache": str(args.rho_cache),
                "best_tv_distance": None if best is None else best["tv_distance"],
                "best_prompt_id": None if best is None else best["prompt_id"],
                "best_block_name": None if best is None else best["block_name"],
            },
            sort_keys=True,
        )
    )
    if best is not None:
        print(json.dumps(best, indent=2))


if __name__ == "__main__":
    main()
