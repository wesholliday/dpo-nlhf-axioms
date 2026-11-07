#!/usr/bin/env python3
"""Count CoVal profiles in the RTBT/DPO domain.

The paper defines G(R) as the directed graph on candidates with an edge
x -> y iff c_{x,y}(R) > 0, where c_{x,y}(R) is the number of voters who
strictly prefer x to y.  RTBT is defined on profiles for which G(R) is
strongly connected.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


@dataclass(frozen=True)
class ProfileCounts:
    prompt_id: str
    block_name: str
    num_rankings: int
    counts: tuple[tuple[int, ...], ...]


def parse_ranking(text: str) -> list[list[str]]:
    compact = text.replace(" ", "")
    return [level.split("=") for level in compact.split(">") if level]


def ranking_to_counts(ranking: str, candidate_index: dict[str, int]) -> list[list[int]]:
    n = len(candidate_index)
    counts = [[0 for _ in range(n)] for _ in range(n)]
    levels = parse_ranking(ranking)
    for left_level_index, left_level in enumerate(levels):
        for right_level in levels[left_level_index + 1 :]:
            for left in left_level:
                for right in right_level:
                    counts[candidate_index[left]][candidate_index[right]] += 1
    return counts


def add_counts(left: list[list[int]], right: Sequence[Sequence[int]]) -> None:
    for row_index, row in enumerate(right):
        for col_index, value in enumerate(row):
            left[row_index][col_index] += value


def iter_profile_counts(dataset: Path, block_names: Sequence[str]) -> Iterable[ProfileCounts]:
    block_set = set(block_names)
    with dataset.open() as handle:
        for line in handle:
            obj = json.loads(line)
            responses = obj.get("responses", [])
            if not responses:
                continue

            response_indices = tuple(response["response_index"] for response in responses)
            candidate_index = {candidate: idx for idx, candidate in enumerate(response_indices)}
            grouped: dict[str, list[str]] = {block_name: [] for block_name in block_names}

            for assessment in obj.get("metadata", {}).get("assessments", []):
                ranking_blocks = assessment.get("ranking_blocks", {})
                for block_name in block_set:
                    for block in ranking_blocks.get(block_name, []):
                        ranking = block.get("ranking")
                        if ranking:
                            grouped[block_name].append(ranking)

            for block_name in block_names:
                rankings = grouped[block_name]
                if not rankings:
                    continue

                n = len(candidate_index)
                total = [[0 for _ in range(n)] for _ in range(n)]
                for ranking in rankings:
                    add_counts(total, ranking_to_counts(ranking, candidate_index))

                yield ProfileCounts(
                    prompt_id=obj["prompt_id"],
                    block_name=block_name,
                    num_rankings=len(rankings),
                    counts=tuple(tuple(row) for row in total),
                )


def strongly_connected(counts: Sequence[Sequence[int]]) -> bool:
    n = len(counts)
    if n == 0:
        return False

    adjacency = {node: set() for node in range(n)}
    reverse_adjacency = {node: set() for node in range(n)}
    for left in range(n):
        for right in range(n):
            if left != right and counts[left][right] > 0:
                adjacency[left].add(right)
                reverse_adjacency[right].add(left)

    def reachable(graph: dict[int, set[int]]) -> set[int]:
        seen = {0}
        stack = [0]
        while stack:
            node = stack.pop()
            for next_node in graph[node]:
                if next_node not in seen:
                    seen.add(next_node)
                    stack.append(next_node)
        return seen

    return len(reachable(adjacency)) == n and len(reachable(reverse_adjacency)) == n


def format_percent(numerator: int, denominator: int) -> str:
    if denominator == 0:
        return "nan"
    return f"{100.0 * numerator / denominator:.6f}%"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument(
        "--blocks",
        nargs="+",
        default=["world", "personal"],
        help="Ranking block names to count as CoVal profiles.",
    )
    parser.add_argument(
        "--json",
        type=Path,
        default=None,
        help="Optional path to write the aggregate counts as JSON.",
    )
    args = parser.parse_args()

    profiles = list(iter_profile_counts(args.dataset, args.blocks))
    total_by_block: Counter[str] = Counter()
    domain_by_block: Counter[str] = Counter()

    for profile in profiles:
        total_by_block[profile.block_name] += 1
        if strongly_connected(profile.counts):
            domain_by_block[profile.block_name] += 1

    total = sum(total_by_block.values())
    domain = sum(domain_by_block.values())
    outside_domain = total - domain

    result = {
        "dataset": str(args.dataset),
        "blocks": list(args.blocks),
        "total_profiles": total,
        "strongly_connected_profiles": domain,
        "not_strongly_connected_profiles": outside_domain,
        "strongly_connected_percent": (100.0 * domain / total) if total else None,
        "by_block": {
            block_name: {
                "total_profiles": total_by_block[block_name],
                "strongly_connected_profiles": domain_by_block[block_name],
                "not_strongly_connected_profiles": total_by_block[block_name]
                - domain_by_block[block_name],
                "strongly_connected_percent": (
                    100.0 * domain_by_block[block_name] / total_by_block[block_name]
                    if total_by_block[block_name]
                    else None
                ),
            }
            for block_name in args.blocks
        },
    }

    print(f"dataset={args.dataset}")
    print(f"blocks={','.join(args.blocks)}")
    print(f"total_profiles={total}")
    print(f"strongly_connected_profiles={domain} ({format_percent(domain, total)})")
    print(
        f"not_strongly_connected_profiles={outside_domain} "
        f"({format_percent(outside_domain, total)})"
    )
    print("by_block:")
    for block_name in args.blocks:
        block_total = total_by_block[block_name]
        block_domain = domain_by_block[block_name]
        print(
            f"  {block_name}: {block_domain}/{block_total} "
            f"({format_percent(block_domain, block_total)})"
        )

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(result, indent=2) + "\n")
        print(f"wrote_json={args.json}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
