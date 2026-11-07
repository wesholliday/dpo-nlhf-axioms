#!/usr/bin/env python3
"""Parallel search for positive-involvement counterexamples.

This script searches for profiles that maximize the drop in the Logistic-Borda
probability of a distinguished candidate x after adding one or more x-top
ballots.

The search space is stochastic but structured:

* base profiles are random mixtures of ballot types;
* added voters are random mixtures of x-top ballot types;
* each worker runs an independent random search and reports its best witness.

The ballot types may be either:

* strict weak orders (all ordered partitions), or
* linear orders (the singleton-block subfamily).
"""

from __future__ import annotations

import argparse
import itertools
import math
import multiprocessing as mp
import os
import random
from dataclasses import dataclass
from typing import Iterable, List, Sequence, Tuple

import numpy as np
from scipy.optimize import least_squares, root


OrderedPartition = Tuple[Tuple[str, ...], ...]


def parse_number(text: str) -> float:
    text = text.strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return float(num) / float(den)
    return float(text)


def format_float(x: float, digits: int = 12) -> str:
    return f"{x:.{digits}g}"


def sigma(x: float) -> float:
    if x >= 0:
        z = math.exp(-x)
        return 1.0 / (1.0 + z)
    z = math.exp(x)
    return z / (1.0 + z)


def sigmap(x: float) -> float:
    s = sigma(x)
    return s * (1.0 - s)


def ordered_partitions(items: Sequence[str]) -> Iterable[OrderedPartition]:
    if not items:
        yield ()
        return

    first = items[0]
    for partition in ordered_partitions(items[1:]):
        part = [list(block) for block in partition]

        for i in range(len(part)):
            new_part = [list(block) for block in part]
            new_part[i].append(first)
            yield canonical_partition(new_part)

        for i in range(len(part) + 1):
            new_part = [list(block) for block in part]
            new_part.insert(i, [first])
            yield canonical_partition(new_part)


def canonical_partition(partition: Sequence[Sequence[str]]) -> OrderedPartition:
    return tuple(tuple(sorted(block)) for block in partition)


def matrix_from_partition(candidates: Sequence[str], partition: OrderedPartition) -> np.ndarray:
    level = {}
    for idx, block in enumerate(partition):
        for candidate in block:
            level[candidate] = idx

    n = len(candidates)
    index = {cand: i for i, cand in enumerate(candidates)}
    matrix = np.zeros((n, n), dtype=float)
    for left in candidates:
        for right in candidates:
            if left == right:
                continue
            if level[left] < level[right]:
                matrix[index[left], index[right]] = 1.0
    return matrix


def is_linear_partition(partition: OrderedPartition) -> bool:
    return all(len(block) == 1 for block in partition)


def strongly_connected(counts: np.ndarray) -> bool:
    n = counts.shape[0]
    adj = {i: set() for i in range(n)}
    radj = {i: set() for i in range(n)}

    for i in range(n):
        for j in range(n):
            if i != j and counts[i, j] > 0:
                adj[i].add(j)
                radj[j].add(i)

    def reachable(graph: dict[int, set[int]], start: int) -> set[int]:
        seen = {start}
        stack = [start]
        while stack:
            node = stack.pop()
            for nxt in graph[node]:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return seen

    return len(reachable(adj, 0)) == n and len(reachable(radj, 0)) == n


class WeightedLogisticBordaSystem:
    def __init__(self, beta: float, wins: np.ndarray):
        if beta <= 0:
            raise ValueError("beta must be positive")
        self.beta = beta
        self.wins = wins.astype(float)
        self.weights = self.wins + self.wins.T
        self.borda = np.sum(self.wins, axis=1)
        self.n = wins.shape[0]

    def unpack(self, y: np.ndarray) -> np.ndarray:
        s = np.empty(self.n, dtype=float)
        s[:-1] = y
        s[-1] = -float(np.sum(y))
        return s

    def residual(self, y: np.ndarray) -> np.ndarray:
        s = self.unpack(y)
        out = np.empty(self.n - 1, dtype=float)
        for i in range(self.n - 1):
            total = 0.0
            for j in range(self.n):
                if i == j:
                    continue
                total += self.weights[i, j] * sigma(self.beta * (s[i] - s[j]))
            out[i] = total - self.borda[i]
        return out

    def jacobian(self, y: np.ndarray) -> np.ndarray:
        s = self.unpack(y)
        jac = np.zeros((self.n - 1, self.n - 1), dtype=float)

        def ds_dy(index: int, coord: int) -> float:
            if index == self.n - 1:
                return -1.0
            return 1.0 if index == coord else 0.0

        for i in range(self.n - 1):
            for k in range(self.n - 1):
                total = 0.0
                for j in range(self.n):
                    if i == j:
                        continue
                    coeff = (
                        self.weights[i, j]
                        * self.beta
                        * sigmap(self.beta * (s[i] - s[j]))
                    )
                    total += coeff * (ds_dy(i, k) - ds_dy(j, k))
                jac[i, k] = total
        return jac


def solve_weighted_logistic_borda(
    beta: float,
    wins: np.ndarray,
    rho: np.ndarray,
    tol: float = 1e-9,
) -> np.ndarray | None:
    if not strongly_connected(wins):
        return None

    system = WeightedLogisticBordaSystem(beta=beta, wins=wins)
    centered = system.borda - float(np.mean(system.borda))
    scale = max(1.0, float(np.max(system.weights)))
    base = (4.0 / (beta * scale)) * centered
    starts = [
        base[:-1],
        np.zeros(system.n - 1, dtype=float),
        0.5 * base[:-1],
        1.5 * base[:-1],
    ]

    for start in starts:
        root_result = root(system.residual, start, jac=system.jacobian, method="hybr")
        candidates = []
        if root_result.x is not None:
            candidates.append(np.asarray(root_result.x, dtype=float))

        lsq_result = least_squares(
            system.residual,
            start,
            jac=system.jacobian,
            xtol=tol,
            ftol=tol,
            gtol=tol,
        )
        candidates.append(np.asarray(lsq_result.x, dtype=float))

        for y in candidates:
            err = float(np.max(np.abs(system.residual(y))))
            if err <= tol:
                scores = system.unpack(y)
                shifted = scores - np.max(scores)
                weights = rho * np.exp(shifted)
                return weights / np.sum(weights)

    return None


def parse_reference(text: str, n: int) -> np.ndarray:
    if text == "uniform":
        return np.full(n, 1.0 / n, dtype=float)
    parts = [parse_number(piece) for piece in text.split(",")]
    if len(parts) != n:
        raise ValueError(f"Expected {n} reference weights, got {len(parts)}")
    rho = np.asarray(parts, dtype=float)
    if np.any(rho <= 0):
        raise ValueError("Reference weights must be strictly positive")
    return rho / np.sum(rho)


@dataclass
class SearchConfig:
    candidates: Tuple[str, ...]
    top_candidate: str
    beta: float
    rho: np.ndarray
    trials: int
    base_types_max: int
    base_weight_max: int
    added_types_max: int
    added_weight_max: int
    seed: int
    progress_every: int


@dataclass
class Witness:
    drop: float
    before: float
    after: float
    base_profile: Tuple[Tuple[OrderedPartition, int], ...]
    added_profile: Tuple[Tuple[OrderedPartition, int], ...]


def sample_profile(
    rng: random.Random,
    partitions: Sequence[OrderedPartition],
    matrices: dict[OrderedPartition, np.ndarray],
    types_max: int,
    weight_max: int,
) -> Tuple[np.ndarray, Tuple[Tuple[OrderedPartition, int], ...]]:
    num_types = rng.randint(1, types_max)
    chosen = rng.sample(list(partitions), num_types)
    weighted = []
    counts = np.zeros(next(iter(matrices.values())).shape, dtype=float)
    for part in chosen:
        weight = rng.randint(1, weight_max)
        weighted.append((part, weight))
        counts += weight * matrices[part]
    return counts, tuple(weighted)


def worker_search(
    worker_id: int,
    config: SearchConfig,
    all_partitions: Tuple[OrderedPartition, ...],
    x_top_partitions: Tuple[OrderedPartition, ...],
    matrices: dict[OrderedPartition, np.ndarray],
) -> Witness | None:
    rng = random.Random(config.seed + worker_id)
    best: Witness | None = None

    for trial in range(1, config.trials + 1):
        base_counts, base_profile = sample_profile(
            rng,
            all_partitions,
            matrices,
            config.base_types_max,
            config.base_weight_max,
        )
        added_counts, added_profile = sample_profile(
            rng,
            x_top_partitions,
            matrices,
            config.added_types_max,
            config.added_weight_max,
        )

        before = solve_weighted_logistic_borda(config.beta, base_counts, config.rho)
        if before is None:
            continue
        after = solve_weighted_logistic_borda(config.beta, base_counts + added_counts, config.rho)
        if after is None:
            continue

        top_index = config.candidates.index(config.top_candidate)
        drop = float(before[top_index] - after[top_index])
        if best is None or drop > best.drop:
            best = Witness(
                drop=drop,
                before=float(before[top_index]),
                after=float(after[top_index]),
                base_profile=base_profile,
                added_profile=added_profile,
            )

        if config.progress_every > 0 and trial % config.progress_every == 0:
            print(
                f"[worker {worker_id}] trial={trial} "
                f"best_drop={format_float(best.drop if best else 0.0)}",
                flush=True,
            )

    return best


def format_partition(partition: OrderedPartition) -> str:
    return " > ".join(",".join(block) for block in partition)


def format_weighted_profile(profile: Sequence[Tuple[OrderedPartition, int]]) -> str:
    return " ; ".join(f"{weight}*({format_partition(part)})" for part, weight in profile)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Parallel search for large positive-involvement drops at fixed beta."
    )
    parser.add_argument("--beta", type=parse_number, default=0.1)
    parser.add_argument("--num-candidates", type=int, default=4)
    parser.add_argument("--top-candidate", type=str, default=None)
    parser.add_argument("--reference", type=str, default="uniform")
    parser.add_argument(
        "--ballot-kind",
        choices=("strict-weak", "linear"),
        default="strict-weak",
        help="Search over all strict weak orders or only over linear orders.",
    )
    parser.add_argument("--workers", type=int, default=max(1, min(24, (os.cpu_count() or 1))))
    parser.add_argument("--trials-per-worker", type=int, default=2000)
    parser.add_argument("--base-types-max", type=int, default=3)
    parser.add_argument("--base-weight-max", type=int, default=8)
    parser.add_argument("--added-types-max", type=int, default=2)
    parser.add_argument("--added-weight-max", type=int, default=4)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--progress-every", type=int, default=500)
    args = parser.parse_args()

    candidates = tuple(chr(ord("a") + i) for i in range(args.num_candidates))
    top_candidate = args.top_candidate or candidates[0]
    if top_candidate not in candidates:
        raise ValueError(f"Top candidate {top_candidate!r} is not in {candidates!r}")

    all_partitions = tuple(dict.fromkeys(ordered_partitions(candidates)))
    if args.ballot_kind == "linear":
        all_partitions = tuple(part for part in all_partitions if is_linear_partition(part))
    x_top_partitions = tuple(
        part for part in all_partitions if len(part) >= 1 and part[0] == (top_candidate,)
    )
    matrices = {part: matrix_from_partition(candidates, part) for part in all_partitions}
    rho = parse_reference(args.reference, len(candidates))

    config = SearchConfig(
        candidates=candidates,
        top_candidate=top_candidate,
        beta=args.beta,
        rho=rho,
        trials=args.trials_per_worker,
        base_types_max=args.base_types_max,
        base_weight_max=args.base_weight_max,
        added_types_max=args.added_types_max,
        added_weight_max=args.added_weight_max,
        seed=args.seed,
        progress_every=args.progress_every,
    )

    print(f"Candidates: {', '.join(candidates)}")
    print(f"Top candidate: {top_candidate}")
    print(f"beta: {format_float(args.beta)}")
    print(f"reference rho: {', '.join(format_float(x) for x in rho)}")
    print(f"ballot kind: {args.ballot_kind}")
    print(f"ballot types: {len(all_partitions)}")
    print(f"{top_candidate}-top ballot types: {len(x_top_partitions)}")
    print(f"workers: {args.workers}")
    print(f"trials per worker: {args.trials_per_worker}")
    print(f"total trials: {args.workers * args.trials_per_worker}")
    print(
        "search limits: "
        f"base_types<= {args.base_types_max}, base_weight<= {args.base_weight_max}, "
        f"added_types<= {args.added_types_max}, added_weight<= {args.added_weight_max}"
    )
    print("", flush=True)

    best: Witness | None = None
    ctx = mp.get_context("fork")
    with ctx.Pool(processes=args.workers) as pool:
        jobs = [
            pool.apply_async(
                worker_search,
                args=(wid, config, all_partitions, x_top_partitions, matrices),
            )
            for wid in range(args.workers)
        ]
        for job in jobs:
            witness = job.get()
            if witness is not None and (best is None or witness.drop > best.drop):
                best = witness
                print("NEW BEST", flush=True)
                print(f"  drop:   {format_float(best.drop)}", flush=True)
                print(f"  before: {format_float(best.before)}", flush=True)
                print(f"  after:  {format_float(best.after)}", flush=True)
                print(f"  base:   {format_weighted_profile(best.base_profile)}", flush=True)
                print(f"  added:  {format_weighted_profile(best.added_profile)}", flush=True)
                print("", flush=True)

    if best is None:
        print("No admissible witness found.")
        return

    print("FINAL BEST")
    print(f"drop   = {format_float(best.drop)}")
    print(f"before = {format_float(best.before)}")
    print(f"after  = {format_float(best.after)}")
    print(f"base   = {format_weighted_profile(best.base_profile)}")
    print(f"added  = {format_weighted_profile(best.added_profile)}")


if __name__ == "__main__":
    main()
