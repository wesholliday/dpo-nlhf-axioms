#!/usr/bin/env python3
"""Legacy no-tie normalized NLHF solver.

Paper-facing NLHF computations use `scripts.theory.nlhf_tie_normalization`,
which includes pairwise ties in the normalization denominator.  This module is
retained only for older helper/search code that is not the source of the
paper's current NLHF figures or tables.
"""

from __future__ import annotations

import numpy as np
from scipy.optimize import root


def normalized_margin_matrix(wins: np.ndarray) -> np.ndarray:
    wins = np.asarray(wins, dtype=float)
    totals = wins + wins.T
    margins = wins - wins.T
    out = np.zeros_like(wins, dtype=float)
    mask = totals > 0
    out[mask] = margins[mask] / totals[mask]
    return out


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
    """Solve the legacy normalized NLHF equilibrium without explicit ties.

    For current paper-facing calculations, call `solve_nlhf_tie_norm` from
    `scripts.theory.nlhf_tie_normalization` with both wins and ties.
    """

    if tau <= 0:
        raise ValueError("tau must be positive")
    return _solve_centered_nlhf(2.0 * tau, normalized_margin_matrix(wins), rho)
