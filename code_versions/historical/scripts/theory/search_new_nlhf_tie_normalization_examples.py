#!/usr/bin/env python3
"""Search CoVal examples for NLHF using the paper's tie normalization.

This script is intentionally separate from the earlier search scripts. The
earlier NLHF pipeline normalized pairwise margins by c_xy + c_yx, effectively
ignoring expressed indifferences. The paper's normalization uses c_xy + c_yx +
i_xy in the denominator.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

from scripts.theory.nlhf_tie_normalization import (
    TieNormCase,
    load_cases_tie_norm,
    parse_ranking,
    ranking_to_string,
    ranking_to_wins_and_ties,
    solve_nlhf_tie_norm,
)


@dataclass(frozen=True)
class ReferenceConfig:
    name: str
    rho_cache: Path | None


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
    for pos in range(src + 1):
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


def strictly_last_candidate(ranking: str, labels: Sequence[str]) -> str | None:
    blocks = parse_ranking(ranking)
    if not blocks or len(blocks[-1]) != 1:
        return None
    seen = {cand for block in blocks for cand in block}
    if set(labels) != seen:
        return None
    return blocks[-1][0]


def load_rho_cache(path: Path) -> dict[str, dict]:
    out: dict[str, dict] = {}
    with path.open() as handle:
        for line in handle:
            obj = json.loads(line)
            prompt_id = obj.get("prompt_id")
            rho = obj.get("rho")
            if isinstance(prompt_id, str) and isinstance(rho, dict):
                out[prompt_id] = obj
    return out


def rho_for_case(case: TieNormCase, ref: ReferenceConfig, cache: dict[str, dict]) -> tuple[np.ndarray, dict | None]:
    if ref.rho_cache is None:
        return np.full(len(case.response_indices), 1.0 / len(case.response_indices), dtype=float), None
    record = cache.get(case.prompt_id)
    if record is None:
        raise KeyError(case.prompt_id)
    rho_map = record["rho"]
    rho = np.asarray([float(rho_map[label]) for label in case.response_indices], dtype=float)
    total = float(np.sum(rho))
    if total <= 0:
        raise ValueError(f"Nonpositive rho for {case.prompt_id}")
    return rho / total, record


def case_arrays(case: TieNormCase) -> tuple[np.ndarray, np.ndarray, list[np.ndarray], list[np.ndarray]]:
    total_wins = np.array(case.total_wins, dtype=float)
    total_ties = np.array(case.total_ties, dtype=float)
    wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]
    ties_per = [np.array(t, dtype=float) for t in case.ties_per_ranking]
    return total_wins, total_ties, wins_per, ties_per


def best_monotonicity_witness(case: TieNormCase, tau: float, rho: np.ndarray, ref: ReferenceConfig, rho_record: dict | None) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total_wins, total_ties, wins_per, ties_per = case_arrays(case)
    observed = solve_nlhf_tie_norm(tau, total_wins, total_ties, rho)
    if observed is None:
        return None

    best: dict | None = None
    for ai, ranking in enumerate(case.rankings):
        old_blocks = parse_ranking(ranking)
        present = [cand for block in old_blocks for cand in block]

        for cand in labels:
            idx = index[cand]
            if cand not in present:
                continue

            for new_ranking in improvements(old_blocks, cand):
                new_blocks = parse_ranking(new_ranking)
                if not monotonicity_move_valid(old_blocks, new_blocks, cand, labels):
                    continue
                new_wins, new_ties = ranking_to_wins_and_ties(new_ranking, index)
                after = solve_nlhf_tie_norm(
                    tau,
                    total_wins - wins_per[ai] + new_wins,
                    total_ties - ties_per[ai] + new_ties,
                    rho,
                )
                if after is None:
                    continue
                drop = float(observed[idx] - after[idx])
                if drop > 0 and (best is None or drop > best["effect"]):
                    best = witness_base(
                        case, ref, rho_record, "monotonicity", tau, rho, cand, drop,
                        before=observed, after=after,
                        observed_role="P", assessment_index=ai,
                        old_ranking=ranking, new_ranking=new_ranking,
                    )

            for new_ranking in demotions(old_blocks, cand):
                new_blocks = parse_ranking(new_ranking)
                if not monotonicity_move_valid(new_blocks, old_blocks, cand, labels):
                    continue
                new_wins, new_ties = ranking_to_wins_and_ties(new_ranking, index)
                before = solve_nlhf_tie_norm(
                    tau,
                    total_wins - wins_per[ai] + new_wins,
                    total_ties - ties_per[ai] + new_ties,
                    rho,
                )
                if before is None:
                    continue
                drop = float(before[idx] - observed[idx])
                if drop > 0 and (best is None or drop > best["effect"]):
                    best = witness_base(
                        case, ref, rho_record, "monotonicity", tau, rho, cand, drop,
                        before=before, after=observed,
                        observed_role="Pplus", assessment_index=ai,
                        old_ranking=new_ranking, new_ranking=ranking,
                    )
    return best


def best_positive_involvement_witness(case: TieNormCase, tau: float, rho: np.ndarray, ref: ReferenceConfig, rho_record: dict | None) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total_wins, total_ties, wins_per, ties_per = case_arrays(case)
    observed = solve_nlhf_tie_norm(tau, total_wins, total_ties, rho)
    if observed is None:
        return None

    best: dict | None = None
    for ai, ranking in enumerate(case.rankings):
        blocks = parse_ranking(ranking)
        if not blocks or len(blocks[0]) != 1:
            continue
        cand = blocks[0][0]
        idx = index[cand]
        before = solve_nlhf_tie_norm(
            tau,
            total_wins - wins_per[ai],
            total_ties - ties_per[ai],
            rho,
        )
        if before is None:
            continue
        drop = float(before[idx] - observed[idx])
        if drop > 0 and (best is None or drop > best["effect"]):
            best = witness_base(
                case, ref, rho_record, "positive_involvement", tau, rho, cand, drop,
                before=before, after=observed,
                observed_role="Pplus", assessment_index=ai,
                deleted_ranking=ranking,
            )
    return best


def best_negative_involvement_witness(case: TieNormCase, tau: float, rho: np.ndarray, ref: ReferenceConfig, rho_record: dict | None) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total_wins, total_ties, wins_per, ties_per = case_arrays(case)
    observed = solve_nlhf_tie_norm(tau, total_wins, total_ties, rho)
    if observed is None:
        return None

    best: dict | None = None
    for ai, ranking in enumerate(case.rankings):
        cand = strictly_last_candidate(ranking, labels)
        if cand is None:
            continue
        idx = index[cand]
        before = solve_nlhf_tie_norm(
            tau,
            total_wins - wins_per[ai],
            total_ties - ties_per[ai],
            rho,
        )
        if before is None:
            continue
        gain = float(observed[idx] - before[idx])
        if gain > 0 and (best is None or gain > best["effect"]):
            best = witness_base(
                case, ref, rho_record, "negative_involvement", tau, rho, cand, gain,
                before=before, after=observed,
                observed_role="Pplus", assessment_index=ai,
                deleted_ranking=ranking,
            )
    return best


def balanced_masks(n: int) -> Iterable[int]:
    if n < 2:
        return
    target = (n + 1) // 2

    def rec(start: int, chosen: int, need: int) -> Iterable[int]:
        if need == 0:
            yield chosen
            return
        last = n - need
        for idx in range(start, last + 1):
            yield from rec(idx + 1, chosen | (1 << idx), need - 1)

    yield from rec(1, 1, target - 1)


def sampled_balanced_masks(n: int, count: int, rng: np.random.Generator) -> Iterable[int]:
    if n < 2:
        return
    target = (n + 1) // 2
    max_possible = 1
    for k in range(1, target):
        max_possible *= (n - k)
        max_possible //= k
    target_count = min(count, max_possible)
    seen: set[tuple[int, ...]] = set()
    while len(seen) < target_count:
        tail = rng.choice(np.arange(1, n), size=target - 1, replace=False)
        chosen = tuple(sorted(int(x) for x in tail))
        if chosen in seen:
            continue
        seen.add(chosen)
        mask = 1
        for idx in chosen:
            mask |= 1 << idx
        yield mask


def split_counts(
    wins_per: Sequence[np.ndarray],
    ties_per: Sequence[np.ndarray],
    mask: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    shape = wins_per[0].shape
    left_wins = np.zeros(shape, dtype=float)
    left_ties = np.zeros(shape, dtype=float)
    right_wins = np.zeros(shape, dtype=float)
    right_ties = np.zeros(shape, dtype=float)
    for i, (wins, ties) in enumerate(zip(wins_per, ties_per)):
        if mask & (1 << i):
            left_wins += wins
            left_ties += ties
        else:
            right_wins += wins
            right_ties += ties
    return left_wins, left_ties, right_wins, right_ties


def best_commutativity_witness(
    case: TieNormCase,
    tau: float,
    rho: np.ndarray,
    ref: ReferenceConfig,
    rho_record: dict | None,
    exhaustive_cutoff: int,
    sampled_splits: int,
    rng: np.random.Generator,
) -> dict | None:
    _, _, wins_per, ties_per = case_arrays(case)
    n = len(wins_per)
    if n < 2:
        return None
    if n <= exhaustive_cutoff:
        masks = balanced_masks(n)
    else:
        masks = sampled_balanced_masks(n, sampled_splits, rng)

    best: dict | None = None
    for mask in masks:
        left_wins, left_ties, right_wins, right_ties = split_counts(wins_per, ties_per, mask)
        left_ref = solve_nlhf_tie_norm(tau, left_wins, left_ties, rho)
        if left_ref is None:
            continue
        right_ref = solve_nlhf_tie_norm(tau, right_wins, right_ties, rho)
        if right_ref is None:
            continue
        left_then_right = solve_nlhf_tie_norm(tau, right_wins, right_ties, left_ref)
        right_then_left = solve_nlhf_tie_norm(tau, left_wins, left_ties, right_ref)
        if left_then_right is None or right_then_left is None:
            continue
        diff = left_then_right - right_then_left
        tv = 0.5 * float(np.sum(np.abs(diff)))
        if tv <= 0:
            continue
        if best is None or tv > best["effect"]:
            left_rankings = [case.rankings[i] for i in range(n) if mask & (1 << i)]
            right_rankings = [case.rankings[i] for i in range(n) if not (mask & (1 << i))]
            best = {
                "prompt_id": case.prompt_id,
                "prompt": case.prompt,
                "block_name": case.block_name,
                "response_indices": case.response_indices,
                "reference": ref.name,
                "rho_source": str(ref.rho_cache) if ref.rho_cache is not None else "uniform",
                "rho": rho.tolist(),
                "response_logprobs": rho_record.get("response_logprobs") if rho_record else None,
                "axiom": "commutativity",
                "rule": "nlhf_tie_norm",
                "param": tau,
                "effect": tv,
                "max_abs_diff": float(np.max(np.abs(diff))),
                "argmax_candidate": case.response_indices[int(np.argmax(np.abs(diff)))],
                "left_size": len(left_rankings),
                "right_size": len(right_rankings),
                "n_assessments": n,
                "rankings_left": left_rankings,
                "rankings_right": right_rankings,
                "left_ref": left_ref.tolist(),
                "right_ref": right_ref.tolist(),
                "out_left_then_right": left_then_right.tolist(),
                "out_right_then_left": right_then_left.tolist(),
            }
    return best


def witness_base(
    case: TieNormCase,
    ref: ReferenceConfig,
    rho_record: dict | None,
    axiom: str,
    tau: float,
    rho: np.ndarray,
    candidate: str,
    effect: float,
    *,
    before: np.ndarray,
    after: np.ndarray,
    **extra: object,
) -> dict:
    return {
        "prompt_id": case.prompt_id,
        "prompt": case.prompt,
        "block_name": case.block_name,
        "response_indices": case.response_indices,
        "reference": ref.name,
        "rho_source": str(ref.rho_cache) if ref.rho_cache is not None else "uniform",
        "rho": rho.tolist(),
        "response_logprobs": rho_record.get("response_logprobs") if rho_record else None,
        "axiom": axiom,
        "rule": "nlhf_tie_norm",
        "param": tau,
        "candidate": candidate,
        "effect": effect,
        "before": before.tolist(),
        "after": after.tolist(),
        "n_assessments": len(case.rankings),
        **extra,
    }


_CASES: list[TieNormCase] = []
_REF: ReferenceConfig | None = None
_CACHE: dict[str, dict] = {}
_TAU: float = 0.01
_EXHAUSTIVE_CUTOFF: int = 16
_SAMPLED_SPLITS: int = 1000
_AXIOMS: tuple[str, ...] = ("monotonicity", "positive_involvement", "negative_involvement", "commutativity")


def init_worker(
    cases: list[TieNormCase],
    ref: ReferenceConfig,
    cache: dict[str, dict],
    tau: float,
    exhaustive_cutoff: int,
    sampled_splits: int,
    axioms: tuple[str, ...],
) -> None:
    global _CASES, _REF, _CACHE, _TAU, _EXHAUSTIVE_CUTOFF, _SAMPLED_SPLITS, _AXIOMS
    _CASES = cases
    _REF = ref
    _CACHE = cache
    _TAU = tau
    _EXHAUSTIVE_CUTOFF = exhaustive_cutoff
    _SAMPLED_SPLITS = sampled_splits
    _AXIOMS = axioms


def worker_case(case_index: int) -> dict[str, dict | None]:
    case = _CASES[case_index]
    assert _REF is not None
    try:
        rho, rho_record = rho_for_case(case, _REF, _CACHE)
    except KeyError:
        return {}
    rng = np.random.default_rng(100_000 + case_index)
    out: dict[str, dict | None] = {}
    if "monotonicity" in _AXIOMS:
        out["monotonicity"] = best_monotonicity_witness(case, _TAU, rho, _REF, rho_record)
    if "positive_involvement" in _AXIOMS:
        out["positive_involvement"] = best_positive_involvement_witness(case, _TAU, rho, _REF, rho_record)
    if "negative_involvement" in _AXIOMS:
        out["negative_involvement"] = best_negative_involvement_witness(case, _TAU, rho, _REF, rho_record)
    if "commutativity" in _AXIOMS:
        out["commutativity"] = best_commutativity_witness(
            case,
            _TAU,
            rho,
            _REF,
            rho_record,
            _EXHAUSTIVE_CUTOFF,
            _SAMPLED_SPLITS,
            rng,
        )
    return out


def write_jsonl(path: Path, records: Sequence[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as handle:
        for record in records:
            handle.write(json.dumps(record, sort_keys=True) + "\n")


def summarize(records: Sequence[dict]) -> dict:
    if not records:
        return {"count": 0}
    strongest = max(records, key=lambda r: float(r["effect"]))
    return {
        "count": len(records),
        "strongest_effect": strongest["effect"],
        "strongest_prompt_id": strongest["prompt_id"],
        "strongest_block_name": strongest["block_name"],
        "strongest_candidate": strongest.get("candidate") or strongest.get("argmax_candidate"),
    }


def run_reference(
    cases: list[TieNormCase],
    ref: ReferenceConfig,
    tau: float,
    output_dir: Path,
    workers: int,
    exhaustive_cutoff: int,
    sampled_splits: int,
    axioms: tuple[str, ...],
) -> dict:
    cache = load_rho_cache(ref.rho_cache) if ref.rho_cache is not None else {}
    results: dict[str, list[dict]] = {
        "monotonicity": [],
        "positive_involvement": [],
        "negative_involvement": [],
        "commutativity": [],
    }

    if workers <= 1:
        init_worker(cases, ref, cache, tau, exhaustive_cutoff, sampled_splits, axioms)
        iterator = map(worker_case, range(len(cases)))
    else:
        pool = mp.Pool(
            processes=workers,
            initializer=init_worker,
            initargs=(cases, ref, cache, tau, exhaustive_cutoff, sampled_splits, axioms),
        )
        iterator = pool.imap_unordered(worker_case, range(len(cases)), chunksize=4)

    try:
        for obj in iterator:
            for axiom, record in obj.items():
                if record is not None:
                    results[axiom].append(record)
    finally:
        if workers > 1:
            pool.close()
            pool.join()

    ref_dir = output_dir / ref.name
    ref_dir.mkdir(parents=True, exist_ok=True)
    summary = {"reference": ref.name, "tau": tau, "axioms": {}}
    for axiom, records in results.items():
        records.sort(key=lambda r: float(r["effect"]), reverse=True)
        write_jsonl(ref_dir / f"{axiom}_tau_{tau:g}.jsonl", records)
        summary["axioms"][axiom] = summarize(records)
    with (ref_dir / f"summary_tau_{tau:g}.json").open("w") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--blocks", nargs="+", default=["world", "personal"])
    parser.add_argument("--tau", type=float, default=0.01)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/new_nlhf_tie_normalization_search_results"))
    parser.add_argument("--comm-exhaustive-cutoff", type=int, default=16)
    parser.add_argument("--comm-sampled-splits", type=int, default=1000)
    parser.add_argument(
        "--axioms",
        nargs="+",
        default=["monotonicity", "positive_involvement", "negative_involvement", "commutativity"],
        choices=["monotonicity", "positive_involvement", "negative_involvement", "commutativity"],
    )
    parser.add_argument(
        "--nemo-rho-cache",
        type=Path,
        default=Path("results/reference_distributions/nemo_pytorch_rho_strip_identity.jsonl"),
    )
    parser.add_argument(
        "--qwen25-rho-cache",
        type=Path,
        default=Path("results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl"),
    )
    parser.add_argument(
        "--qwen3-rho-cache",
        type=Path,
        default=Path("results/reference_distributions/qwen3_pytorch_rho_strip_identity.jsonl"),
    )
    parser.add_argument(
        "--references",
        nargs="+",
        default=["uniform", "nemo_base_strip_identity", "qwen25_base_strip_identity"],
    )
    args = parser.parse_args()

    cases = load_cases_tie_norm(args.dataset, args.blocks)
    ref_map = {
        "uniform": ReferenceConfig("uniform", None),
        "nemo_base_strip_identity": ReferenceConfig("nemo_base_strip_identity", args.nemo_rho_cache),
        "qwen25_base_strip_identity": ReferenceConfig("qwen25_base_strip_identity", args.qwen25_rho_cache),
        "qwen3_base_strip_identity": ReferenceConfig("qwen3_base_strip_identity", args.qwen3_rho_cache),
    }

    summaries = []
    for ref_name in args.references:
        ref = ref_map[ref_name]
        print(f"running reference={ref.name} tau={args.tau} cases={len(cases)}", flush=True)
        summary = run_reference(
            cases,
            ref,
            args.tau,
            args.output_dir,
            args.workers,
            args.comm_exhaustive_cutoff,
            args.comm_sampled_splits,
            tuple(args.axioms),
        )
        summaries.append(summary)
        print(json.dumps(summary, sort_keys=True), flush=True)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    with (args.output_dir / f"summary_tau_{args.tau:g}.json").open("w") as handle:
        json.dump(summaries, handle, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
