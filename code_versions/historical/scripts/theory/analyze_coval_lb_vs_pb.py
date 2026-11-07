#!/usr/bin/env python3
"""Exploratory CoVal analysis under Logistic-Borda, PB, ML, and NLHF.

This script is retained for transparency only. It is not used to generate the
paper's figures or tables.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np
from scipy.optimize import linprog, root

from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda


def parse_number_list(text: str) -> list[float]:
    return [float(piece.strip()) for piece in text.split(",") if piece.strip()]


def parse_name_list(text: str) -> list[str]:
    return [piece.strip() for piece in text.split(",") if piece.strip()]


def parse_ranking(text: str) -> list[tuple[str, ...]]:
    compact = text.replace(" ", "")
    return [tuple(block.split("=")) for block in compact.split(">")]


@dataclass(frozen=True)
class ProfileRecord:
    prompt_id: str
    wins: np.ndarray
    num_assessments: int


def iter_profiles(path: Path, block_name: str) -> Iterable[ProfileRecord]:
    with path.open() as handle:
        for line in handle:
            obj = json.loads(line)
            responses = obj["responses"]
            if len(responses) != 4:
                continue
            index = {response["response_index"]: i for i, response in enumerate(responses)}
            wins = np.zeros((4, 4), dtype=float)
            num_assessments = 0
            for assessment in obj.get("metadata", {}).get("assessments", []):
                blocks = assessment.get("ranking_blocks", {}).get(block_name, [])
                for block in blocks:
                    ranking = block.get("ranking")
                    if not ranking:
                        continue
                    num_assessments += 1
                    strict_blocks = parse_ranking(ranking)
                    for i, current in enumerate(strict_blocks):
                        for later in strict_blocks[i + 1 :]:
                            for left in current:
                                for right in later:
                                    wins[index[left], index[right]] += 1.0
            if num_assessments > 0:
                yield ProfileRecord(
                    prompt_id=obj["prompt_id"],
                    wins=wins,
                    num_assessments=num_assessments,
                )


def proportional_borda(wins: np.ndarray) -> np.ndarray:
    borda = np.sum(wins, axis=1)
    total = float(np.sum(borda))
    if total <= 0:
        raise ValueError("Proportional Borda undefined when total Borda mass is zero.")
    return borda / total


def margin_matrix(wins: np.ndarray) -> np.ndarray:
    return wins - wins.T


def normalized_margin_matrix(wins: np.ndarray) -> np.ndarray:
    wins = np.asarray(wins, dtype=float)
    totals = wins + wins.T
    margins = wins - wins.T
    out = np.zeros_like(wins, dtype=float)
    mask = totals > 0
    out[mask] = margins[mask] / totals[mask]
    return out


def total_variation(p: np.ndarray, q: np.ndarray) -> float:
    return 0.5 * float(np.sum(np.abs(p - q)))


def max_abs_diff(p: np.ndarray, q: np.ndarray) -> float:
    return float(np.max(np.abs(p - q)))


def same_top(p: np.ndarray, q: np.ndarray, tol: float = 1e-12) -> float:
    p_top = int(np.argmax(p))
    q_max = float(np.max(q))
    return 1.0 if q[p_top] >= q_max - tol else 0.0


def summarize(values: Sequence[float]) -> dict[str, float]:
    arr = np.asarray(values, dtype=float)
    return {
        "mean": float(np.mean(arr)),
        "median": float(np.median(arr)),
        "p90": float(np.quantile(arr, 0.9)),
        "max": float(np.max(arr)),
    }


def solve_maximal_lottery(margins: np.ndarray) -> np.ndarray | None:
    n = margins.shape[0]
    c = np.zeros(n + 1, dtype=float)
    c[-1] = -1.0

    a_ub = np.zeros((n, n + 1), dtype=float)
    for j in range(n):
        a_ub[j, :n] = -margins[:, j]
        a_ub[j, -1] = 1.0

    a_eq = np.zeros((1, n + 1), dtype=float)
    a_eq[0, :n] = 1.0
    b_eq = np.array([1.0], dtype=float)

    bounds = [(0.0, None) for _ in range(n)] + [(None, None)]
    result = linprog(
        c=c,
        A_ub=a_ub,
        b_ub=np.zeros(n, dtype=float),
        A_eq=a_eq,
        b_eq=b_eq,
        bounds=bounds,
        method="highs",
    )
    if not result.success:
        return None
    p = np.asarray(result.x[:n], dtype=float)
    p = np.maximum(p, 0.0)
    total = float(np.sum(p))
    if total <= 0:
        return None
    return p / total


class CenteredNlhfFixedPointSystem:
    def __init__(self, tau: float, margins: np.ndarray, rho: np.ndarray):
        self.tau = tau
        self.margins = margins.astype(float)
        self.rho = rho.astype(float)
        self.n = margins.shape[0]

    def unpack(self, y: np.ndarray) -> np.ndarray:
        z = np.empty(self.n, dtype=float)
        z[:-1] = y
        z[-1] = 0.0
        return z

    def softmax_ref(self, z: np.ndarray) -> np.ndarray:
        support = self.rho > 0
        log_weights = np.full(self.n, -np.inf, dtype=float)
        log_weights[support] = np.log(self.rho[support]) + z[support]
        shifted = log_weights - np.max(log_weights)
        weights = np.exp(shifted)
        return weights / np.sum(weights)

    def residual(self, y: np.ndarray) -> np.ndarray:
        z = self.unpack(y)
        pi = self.softmax_ref(z)
        pay = self.margins @ pi
        out = np.empty(self.n - 1, dtype=float)
        for i in range(self.n - 1):
            out[i] = z[i] - (pay[i] - pay[-1]) / self.tau
        return out


def _solve_centered_nlhf(tau: float, margins: np.ndarray, rho: np.ndarray) -> np.ndarray | None:
    system = CenteredNlhfFixedPointSystem(tau=tau, margins=margins, rho=rho)
    starts = [
        np.zeros(system.n - 1, dtype=float),
        np.asarray((margins @ rho)[:-1] / tau, dtype=float),
    ]
    for start in starts:
        result = root(system.residual, start, method="hybr")
        if not result.success:
            continue
        err = float(np.max(np.abs(system.residual(np.asarray(result.x, dtype=float)))))
        if err <= 1e-9:
            return system.softmax_ref(system.unpack(np.asarray(result.x, dtype=float)))
    return None


def solve_nlhf(tau: float, wins: np.ndarray, rho: np.ndarray) -> np.ndarray | None:
    """Solve the paper-faithful normalized NLHF equilibrium.

    The paper defines NLHF via Gamma_tau built from normalized pairwise
    preferences \\overline{c}. Rewriting that objective using normalized margins
    \\overline{m}=2\\overline{c}-1 doubles the KL coefficient, so the centered
    margin-game solver must be called with 2*tau.
    """

    if tau <= 0:
        raise ValueError("tau must be positive")
    return _solve_centered_nlhf(2.0 * tau, normalized_margin_matrix(wins), rho)


def analyze_block(
    dataset: Path,
    block_name: str,
    betas: Sequence[float],
    random_rho_samples: int,
    rng: np.random.Generator,
) -> None:
    profiles = list(iter_profiles(dataset, block_name))
    uniform_rho = np.full(4, 0.25, dtype=float)

    print(f"block={block_name}")
    print(f"  profiles_with_4_responses={len(profiles)}")

    ml_cache = {}
    pb_cache = {}
    for profile in profiles:
        pb_cache[profile.prompt_id] = proportional_borda(profile.wins)
        ml_cache[profile.prompt_id] = solve_maximal_lottery(margin_matrix(profile.wins))

    for beta in betas:
        admissible = []
        uniform_lb_pb_tv = []
        uniform_lb_ml_tv = []
        uniform_nlhf_ml_tv = []
        uniform_lb_nlhf_tv = []
        uniform_lb_pb_top = []
        uniform_lb_ml_top = []
        uniform_nlhf_ml_top = []

        random_lb_pb_tv = []
        random_lb_nlhf_tv = []
        random_nlhf_ml_tv = []
        random_lb_pb_top = []
        random_lb_nlhf_top = []
        random_nlhf_ml_top = []

        for profile in profiles:
            pb = pb_cache[profile.prompt_id]
            ml = ml_cache[profile.prompt_id]
            if ml is None:
                continue
            lb = solve_weighted_logistic_borda(beta, profile.wins, uniform_rho)
            nlhf = solve_nlhf(beta, profile.wins, uniform_rho)
            if lb is None or nlhf is None:
                continue

            admissible.append(profile)
            uniform_lb_pb_tv.append(total_variation(lb, pb))
            uniform_lb_ml_tv.append(total_variation(lb, ml))
            uniform_nlhf_ml_tv.append(total_variation(nlhf, ml))
            uniform_lb_nlhf_tv.append(total_variation(lb, nlhf))
            uniform_lb_pb_top.append(same_top(lb, pb))
            uniform_lb_ml_top.append(same_top(lb, ml))
            uniform_nlhf_ml_top.append(same_top(nlhf, ml))

            for _ in range(random_rho_samples):
                rho = rng.dirichlet(np.ones(4))
                lb_rand = solve_weighted_logistic_borda(beta, profile.wins, rho)
                nlhf_rand = solve_nlhf(beta, profile.wins, rho)
                if lb_rand is None or nlhf_rand is None:
                    continue
                random_lb_pb_tv.append(total_variation(lb_rand, pb))
                random_lb_nlhf_tv.append(total_variation(lb_rand, nlhf_rand))
                random_nlhf_ml_tv.append(total_variation(nlhf_rand, ml))
                random_lb_pb_top.append(same_top(lb_rand, pb))
                random_lb_nlhf_top.append(same_top(lb_rand, nlhf_rand))
                random_nlhf_ml_top.append(same_top(nlhf_rand, ml))

        print(f"  beta={beta}")
        print(f"    admissible_profiles={len(admissible)} / {len(profiles)}")
        print(
            f"    uniform_lb_pb_tv={json.dumps(summarize(uniform_lb_pb_tv), sort_keys=True)}"
        )
        print(
            f"    uniform_lb_ml_tv={json.dumps(summarize(uniform_lb_ml_tv), sort_keys=True)}"
        )
        print(
            f"    uniform_nlhf_ml_tv={json.dumps(summarize(uniform_nlhf_ml_tv), sort_keys=True)}"
        )
        print(
            f"    uniform_lb_nlhf_tv={json.dumps(summarize(uniform_lb_nlhf_tv), sort_keys=True)}"
        )
        print(f"    uniform_lb_pb_top_mean={float(np.mean(uniform_lb_pb_top)):.6f}")
        print(f"    uniform_lb_ml_top_mean={float(np.mean(uniform_lb_ml_top)):.6f}")
        print(f"    uniform_nlhf_ml_top_mean={float(np.mean(uniform_nlhf_ml_top)):.6f}")
        print(
            f"    random_lb_pb_tv={json.dumps(summarize(random_lb_pb_tv), sort_keys=True)}"
        )
        print(
            f"    random_lb_nlhf_tv={json.dumps(summarize(random_lb_nlhf_tv), sort_keys=True)}"
        )
        print(
            f"    random_nlhf_ml_tv={json.dumps(summarize(random_nlhf_ml_tv), sort_keys=True)}"
        )
        print(f"    random_lb_pb_top_mean={float(np.mean(random_lb_pb_top)):.6f}")
        print(f"    random_lb_nlhf_top_mean={float(np.mean(random_lb_nlhf_top)):.6f}")
        print(f"    random_nlhf_ml_top_mean={float(np.mean(random_nlhf_ml_top)):.6f}")
        print("")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Analyze CoVal 4-candidate profiles across several probabilistic rules."
    )
    parser.add_argument(
        "--dataset",
        type=Path,
        default=Path("data/coval_comparisons.jsonl"),
        help="Path to CoVal data/coval_comparisons.jsonl",
    )
    parser.add_argument(
        "--blocks",
        type=str,
        default="world,personal",
        help="Comma-separated ranking blocks to analyze.",
    )
    parser.add_argument(
        "--betas",
        type=str,
        default="0.05,0.1,0.2,0.5,1.0",
        help="Comma-separated beta/tau values to evaluate.",
    )
    parser.add_argument(
        "--random-rho-samples",
        type=int,
        default=10,
        help="Number of Dirichlet(1) reference policies to sample per admissible profile.",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=0,
        help="Random seed for sampled reference policies.",
    )
    args = parser.parse_args()

    betas = parse_number_list(args.betas)
    blocks = parse_name_list(args.blocks)
    rng = np.random.default_rng(args.seed)

    print(f"dataset={args.dataset}")
    print(f"blocks={blocks}")
    print(f"betas={betas}")
    print(f"random_rho_samples={args.random_rho_samples}")
    print("")

    for block_name in blocks:
        analyze_block(
            dataset=args.dataset,
            block_name=block_name,
            betas=betas,
            random_rho_samples=args.random_rho_samples,
            rng=rng,
        )


if __name__ == "__main__":
    main()
