#!/usr/bin/env python3
"""CoVal profile parsing utilities.

The CoVal input contains prompt-level candidate responses together with one or
more ranking blocks supplied by annotators. This module converts those ranking
blocks into the matrix data used by the PB, RTBT, and NLHF numerical routines.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np


@dataclass(frozen=True)
class TieNormCase:
    prompt_id: str
    prompt: dict
    block_name: str
    response_indices: tuple[str, ...]
    rankings: tuple[str, ...]
    wins_per_ranking: tuple[tuple[tuple[float, ...], ...], ...]
    ties_per_ranking: tuple[tuple[tuple[float, ...], ...], ...]
    total_wins: tuple[tuple[float, ...], ...]
    total_ties: tuple[tuple[float, ...], ...]


def parse_ranking(text: str) -> list[list[str]]:
    compact = text.replace(" ", "")
    return [block.split("=") for block in compact.split(">") if block]


def ranking_to_string(blocks: Sequence[Sequence[str]]) -> str:
    return ">".join("=".join(block) for block in blocks)


def ranking_to_wins_and_ties(
    ranking: str,
    index: dict[str, int],
) -> tuple[np.ndarray, np.ndarray]:
    n = len(index)
    wins = np.zeros((n, n), dtype=float)
    ties = np.zeros((n, n), dtype=float)
    blocks = parse_ranking(ranking)

    for current in blocks:
        for pos, left in enumerate(current):
            if left not in index:
                continue
            i = index[left]
            for right in current[pos + 1 :]:
                if right not in index:
                    continue
                j = index[right]
                ties[i, j] += 1.0
                ties[j, i] += 1.0

    for i, current in enumerate(blocks):
        for later in blocks[i + 1 :]:
            for left in current:
                if left not in index:
                    continue
                li = index[left]
                for right in later:
                    if right not in index:
                        continue
                    wins[li, index[right]] += 1.0

    return wins, ties


def load_cases_tie_norm(path: Path, block_names: Sequence[str]) -> list[TieNormCase]:
    block_set = set(block_names)
    cases: list[TieNormCase] = []
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
                wins_per: list[np.ndarray] = []
                ties_per: list[np.ndarray] = []
                for ranking in rankings:
                    wins, ties = ranking_to_wins_and_ties(ranking, index)
                    wins_per.append(wins)
                    ties_per.append(ties)
                total_wins = np.sum(wins_per, axis=0)
                total_ties = np.sum(ties_per, axis=0)
                cases.append(
                    TieNormCase(
                        prompt_id=obj["prompt_id"],
                        prompt=obj.get("prompt", {}),
                        block_name=block_name,
                        response_indices=response_indices,
                        rankings=tuple(rankings),
                        wins_per_ranking=tuple(
                            tuple(tuple(float(x) for x in row) for row in wins)
                            for wins in wins_per
                        ),
                        ties_per_ranking=tuple(
                            tuple(tuple(float(x) for x in row) for row in ties)
                            for ties in ties_per
                        ),
                        total_wins=tuple(tuple(float(x) for x in row) for row in total_wins),
                        total_ties=tuple(tuple(float(x) for x in row) for row in total_ties),
                    )
                )
    return cases


def iter_grouped_rankings(rankings: Sequence[str]) -> Iterable[tuple[str, int]]:
    counts: dict[str, int] = {}
    order: list[str] = []
    for ranking in rankings:
        compact = ranking.replace(" ", "")
        if compact not in counts:
            counts[compact] = 0
            order.append(compact)
        counts[compact] += 1
    for ranking in order:
        yield ranking, counts[ranking]
