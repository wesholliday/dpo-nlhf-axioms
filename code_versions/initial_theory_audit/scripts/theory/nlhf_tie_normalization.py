#!/usr/bin/env python3
"""Tie-normalized NLHF numerical solver from the paper."""

from __future__ import annotations

import numpy as np
from scipy.optimize import least_squares, root
from scipy.special import logsumexp

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
    def __init__(self, tau: float, margins: np.ndarray, rho: np.ndarray, *, log_rho=None):
        self.tau = float(tau)
        self.margins = margins.astype(float)
        self.rho = rho.astype(float)
        self.n = margins.shape[0]
        if log_rho is None:
            with np.errstate(divide="ignore"):
                self.log_rho = np.log(self.rho)
        else:
            self.log_rho = np.asarray(log_rho, dtype=float)

    def unpack(self, y: np.ndarray) -> np.ndarray:
        z = np.empty(self.n, dtype=float)
        z[:-1] = y
        z[-1] = 0.0
        return z

    def softmax_ref(self, z: np.ndarray) -> np.ndarray:
        return np.exp(self.log_softmax_ref(z))

    def log_softmax_ref(self, z: np.ndarray) -> np.ndarray:
        log_weights = self.log_rho + z
        return log_weights - logsumexp(log_weights)

    def residual(self, y: np.ndarray) -> np.ndarray:
        z = self.unpack(y)
        pi = self.softmax_ref(z)
        pay = self.margins @ pi
        return z[:-1] - (pay[:-1] - pay[-1]) / self.tau

    def jacobian(self, y: np.ndarray) -> np.ndarray:
        pi = self.softmax_ref(self.unpack(y))
        derivative = (np.diag(pi) - np.outer(pi, pi))[:, :-1]
        return np.eye(self.n - 1) - (self.margins[:-1] - self.margins[-1]) @ derivative / self.tau


def _solve_centered_nlhf(tau: float, margins: np.ndarray, rho: np.ndarray,
                         *, log_rho=None, return_log=False) -> np.ndarray | None:
    system = CenteredNlhfFixedPointSystem(tau=tau, margins=margins, rho=rho, log_rho=log_rho)
    if system.n == 1:
        return np.zeros(1) if return_log else np.ones(1)
    pay = margins @ rho
    starts = [
        np.zeros(system.n - 1, dtype=float),
        (pay[:-1] - pay[-1]) / tau,
        -(pay[:-1] - pay[-1]) / tau,
    ]

    def certified(y):
        return np.all(np.isfinite(y)) and np.max(np.abs(system.residual(y))) <= 1e-9

    def output(y):
        logs = system.log_softmax_ref(system.unpack(y))
        return logs if return_log else np.exp(logs)

    for start in starts:
        result = root(system.residual, start, jac=system.jacobian, method="hybr", options={"xtol": 1e-10})
        # MINPACK can report "no progress" at an already accurate root. The
        # residual, not its termination flag, certifies the fixed point.
        if certified(result.x):
            return output(result.x)

    # A bounded fallback prevents a numerical failure from silently becoming
    # a negative search result. Callers must still account for a returned None.
    for start in starts[:2]:
        result = least_squares(system.residual, start, jac=system.jacobian,
                               xtol=1e-12, ftol=1e-12, gtol=1e-12, max_nfev=500)
        if certified(result.x):
            return output(result.x)
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

    if not np.isfinite(tau) or tau <= 0:
        raise ValueError("tau must be positive")
    rho = np.asarray(rho, dtype=float)
    if rho.ndim != 1 or not len(rho) or not np.all(np.isfinite(rho)) or np.any(rho < 0) or rho.sum() <= 0:
        raise ValueError("rho must be a nonnegative finite vector with positive total mass")
    rho = rho / rho.sum()
    margins = normalized_margin_matrix_tie_norm(wins, ties)
    if margins.shape != (len(rho), len(rho)) or not np.all(np.isfinite(margins)):
        raise ValueError("margin matrix must be finite and match rho")
    return _solve_centered_nlhf(2.0 * tau, margins, rho)


def solve_nlhf_tie_norm_log(tau: float, wins: np.ndarray, ties: np.ndarray,
                           log_rho: np.ndarray) -> np.ndarray | None:
    """Return log probabilities, retaining tiny masses in sequential updates.

    Passing exp(log_rho) through the ordinary interface can underflow to zero
    and incorrectly eliminate candidates before the next electorate acts.
    """
    log_rho = np.asarray(log_rho, dtype=float)
    if not np.isfinite(tau) or tau <= 0 or log_rho.ndim != 1 or not len(log_rho):
        raise ValueError("positive tau and a nonempty log reference are required")
    if np.any(np.isnan(log_rho)) or np.any(np.isposinf(log_rho)) or not np.any(np.isfinite(log_rho)):
        raise ValueError("invalid log reference")
    log_rho = log_rho - logsumexp(log_rho)
    margins = normalized_margin_matrix_tie_norm(wins, ties)
    if margins.shape != (len(log_rho), len(log_rho)) or not np.all(np.isfinite(margins)):
        raise ValueError("margin matrix must be finite and match log_rho")
    return _solve_centered_nlhf(2.0 * tau, margins, np.exp(log_rho),
                                log_rho=log_rho, return_log=True)


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
    "solve_nlhf_tie_norm_log",
]
