#!/usr/bin/env python3
"""Tie-normalized NLHF numerical solver from the paper."""

from __future__ import annotations

import numpy as np
from scipy.optimize import root

from scripts.coval.profiles import (
    TieNormCase,
    iter_grouped_rankings,
    load_cases_tie_norm,
    parse_ranking,
    ranking_to_string,
    ranking_to_wins_and_ties,
)


def normalized_margin_matrix_tie_norm(wins: np.ndarray, ties: np.ndarray) -> np.ndarray:
    wins = np.asarray(wins, dtype=float)
    ties = np.asarray(ties, dtype=float)
    totals = wins + wins.T + ties
    margins = wins - wins.T
    out = np.zeros_like(wins, dtype=float)
    mask = totals > 0
    out[mask] = margins[mask] / totals[mask]
    np.fill_diagonal(out, 0.0)
    return out


class CenteredNlhfFixedPointSystem:
    def __init__(self, tau: float, margins: np.ndarray, rho: np.ndarray):
        self.tau = float(tau)
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
        -np.asarray((margins @ rho)[:-1] / tau, dtype=float),
    ]
    for start in starts:
        result = root(system.residual, start, method="hybr")
        if not result.success:
            continue
        err = float(np.max(np.abs(system.residual(np.asarray(result.x, dtype=float)))))
        if err <= 1e-9:
            return system.softmax_ref(system.unpack(np.asarray(result.x, dtype=float)))
    return None


def solve_nlhf_tie_norm(
    tau: float,
    wins: np.ndarray,
    ties: np.ndarray,
    rho: np.ndarray,
) -> np.ndarray | None:
    """Solve NLHF using the normalization in the paper.

    The paper defines Gamma_tau with normalized supports cbar. Rewriting via
    normalized margins doubles the KL coefficient, so the fixed-point equation
    uses 2*tau.
    """

    if tau <= 0:
        raise ValueError("tau must be positive")
    margins = normalized_margin_matrix_tie_norm(wins, ties)
    return _solve_centered_nlhf(2.0 * tau, margins, rho)


__all__ = [
    "CenteredNlhfFixedPointSystem",
    "TieNormCase",
    "iter_grouped_rankings",
    "load_cases_tie_norm",
    "normalized_margin_matrix_tie_norm",
    "parse_ranking",
    "ranking_to_string",
    "ranking_to_wins_and_ties",
    "solve_nlhf_tie_norm",
]
