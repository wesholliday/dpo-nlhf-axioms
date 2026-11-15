#!/usr/bin/env python3
"""Parameter sweeps using the paper's tie-normalized NLHF rule."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import json
import multiprocessing as mp
from pathlib import Path
from typing import Sequence

import matplotlib.pyplot as plt
import numpy as np

from scripts.theory.nlhf_tie_normalization import (
    TieNormCase,
    load_cases_tie_norm,
    parse_ranking,
    ranking_to_string,
    ranking_to_wins_and_ties,
    solve_nlhf_tie_norm,
)
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases as load_rtbt_cases
from scripts.theory.search_model_reference_violation_counts import (
    Scenario,
    load_rho_cache as load_rtbt_rho_cache,
    scenario_summary,
    worker as rtbt_worker,
)
from scripts.theory.search_nlhf_tie_normalization_examples import (
    ReferenceConfig,
    best_monotonicity_witness,
    best_negative_involvement_witness,
    best_positive_involvement_witness,
    load_rho_cache,
    rho_for_case,
)


DEFAULT_NLHF_TAUS = [0.0005, 0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5]
DEFAULT_RTBT_BETAS = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0]


_NLHF_CASES: Sequence[TieNormCase] = ()
_REF: ReferenceConfig | None = None
_RHO_CACHE: dict[str, dict] = {}
_TAU = 0.01
_AXIOM = "monotonicity"
_MIN_EFFECT = 0.0
_COMM_MAX_UNIQUE = 18


def parse_float_list(text: str) -> list[float]:
    return [float(part.strip()) for part in text.split(",") if part.strip()]


def init_nlhf_worker(
    cases: Sequence[TieNormCase],
    ref: ReferenceConfig,
    rho_cache: dict[str, dict],
    tau: float,
    axiom: str,
    min_effect: float,
    comm_max_unique: int,
) -> None:
    global _NLHF_CASES, _REF, _RHO_CACHE, _TAU, _AXIOM, _MIN_EFFECT, _COMM_MAX_UNIQUE
    _NLHF_CASES = cases
    _REF = ref
    _RHO_CACHE = rho_cache
    _TAU = tau
    _AXIOM = axiom
    _MIN_EFFECT = min_effect
    _COMM_MAX_UNIQUE = comm_max_unique


def grouped_masks(n: int):
    if n < 2:
        return
    full = (1 << n) - 1
    for tail in range(1 << (n - 1)):
        mask = 1 | (tail << 1)
        if mask != full:
            yield mask


def compact_unique_ranking_count(case: TieNormCase) -> int:
    return len({ranking_to_string(parse_ranking(ranking)) for ranking in case.rankings})


def grouped_commutativity_witness(
    case: TieNormCase,
    tau: float,
    rho: np.ndarray,
    ref: ReferenceConfig,
    rho_record: dict | None,
    min_effect: float,
    max_unique_rankings: int,
) -> dict | None:
    counts = Counter(ranking_to_string(parse_ranking(ranking)) for ranking in case.rankings)
    unique_rankings = sorted(counts)
    if len(unique_rankings) < 2 or len(unique_rankings) > max_unique_rankings:
        return None

    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    shape = (len(labels), len(labels))
    wins_per: list[np.ndarray] = []
    ties_per: list[np.ndarray] = []
    for ranking in unique_rankings:
        wins, ties = ranking_to_wins_and_ties(ranking, index)
        wins_per.append(counts[ranking] * wins)
        ties_per.append(counts[ranking] * ties)

    best: dict | None = None
    for mask in grouped_masks(len(unique_rankings)):
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

        left_ref = solve_nlhf_tie_norm(tau, left_wins, left_ties, rho)
        right_ref = solve_nlhf_tie_norm(tau, right_wins, right_ties, rho)
        if left_ref is None or right_ref is None:
            continue
        left_then_right = solve_nlhf_tie_norm(tau, right_wins, right_ties, left_ref)
        right_then_left = solve_nlhf_tie_norm(tau, left_wins, left_ties, right_ref)
        if left_then_right is None or right_then_left is None:
            continue

        tv = 0.5 * float(np.sum(np.abs(left_then_right - right_then_left)))
        if tv <= 0:
            continue
        rankings_left = [unique_rankings[i] for i in range(len(unique_rankings)) if mask & (1 << i)]
        rankings_right = [unique_rankings[i] for i in range(len(unique_rankings)) if not (mask & (1 << i))]
        witness = {
            "prompt_id": case.prompt_id,
            "prompt": case.prompt,
            "block_name": case.block_name,
            "response_indices": labels,
            "reference": ref.name,
            "rho_source": str(ref.rho_cache) if ref.rho_cache is not None else "uniform",
            "rho": rho.tolist(),
            "response_logprobs": rho_record.get("response_logprobs") if rho_record else None,
            "axiom": "commutativity",
            "rule": "nlhf_tie_norm",
            "param": tau,
            "effect": tv,
            "tv_distance": tv,
            "n_assessments": len(case.rankings),
            "n_unique_rankings": len(unique_rankings),
            "rankings_left": rankings_left,
            "rankings_right": rankings_right,
            "grouped_left_counts": {ranking: counts[ranking] for ranking in rankings_left},
            "grouped_right_counts": {ranking: counts[ranking] for ranking in rankings_right},
            "left_ref": left_ref.tolist(),
            "right_ref": right_ref.tolist(),
            "out_left_then_right": left_then_right.tolist(),
            "out_right_then_left": right_then_left.tolist(),
        }
        if tv >= min_effect:
            return witness
        if best is None or tv > best["effect"]:
            best = witness

    return best if best is not None and best["effect"] >= min_effect else None


def nlhf_worker_chunk(indices: Sequence[int]) -> list[dict]:
    assert _REF is not None
    out: list[dict] = []
    for index in indices:
        case = _NLHF_CASES[index]
        try:
            rho, rho_record = rho_for_case(case, _REF, _RHO_CACHE)
        except KeyError:
            continue
        if _AXIOM == "monotonicity":
            witness = best_monotonicity_witness(case, _TAU, rho, _REF, rho_record)
        elif _AXIOM == "positive_involvement":
            witness = best_positive_involvement_witness(case, _TAU, rho, _REF, rho_record)
        elif _AXIOM == "negative_involvement":
            witness = best_negative_involvement_witness(case, _TAU, rho, _REF, rho_record)
        elif _AXIOM == "commutativity":
            witness = grouped_commutativity_witness(
                case, _TAU, rho, _REF, rho_record, _MIN_EFFECT, _COMM_MAX_UNIQUE
            )
        else:
            raise ValueError(_AXIOM)
        if witness is not None and witness["effect"] >= _MIN_EFFECT:
            out.append(witness)
    return out


def run_nlhf_axiom(
    cases: Sequence[TieNormCase],
    ref: ReferenceConfig,
    rho_cache: dict[str, dict],
    tau: float,
    axiom: str,
    workers: int,
    min_effect: float,
    comm_max_unique: int,
) -> list[dict]:
    chunks: list[list[int]] = [[] for _ in range(workers)]
    for i in range(len(cases)):
        chunks[i % workers].append(i)
    ctx = mp.get_context("fork")
    with ctx.Pool(
        workers,
        initializer=init_nlhf_worker,
        initargs=(cases, ref, rho_cache, tau, axiom, min_effect, comm_max_unique),
    ) as pool:
        pieces = pool.map(nlhf_worker_chunk, chunks)
    return [witness for piece in pieces for witness in piece]


def run_rtbt_scenario(cases: Sequence, rho_cache: dict[str, dict], scenario: Scenario, workers: int) -> list[dict]:
    chunks: list[list] = [[] for _ in range(workers)]
    for i, case in enumerate(cases):
        chunks[i % workers].append(case)
    ctx = mp.get_context("fork")
    with ctx.Pool(workers) as pool:
        pieces = pool.starmap(
            rtbt_worker,
            [(worker_id, chunks[worker_id], rho_cache, scenario) for worker_id in range(workers)],
        )
    return [witness for piece in pieces for witness in piece]


def uniform_rho_cache(cases: Sequence) -> dict[str, dict]:
    cache: dict[str, dict] = {}
    for case in cases:
        if case.prompt_id not in cache:
            cache[case.prompt_id] = {
                "prompt_id": case.prompt_id,
                "rho": {label: 1.0 / len(case.response_indices) for label in case.response_indices},
                "response_logprobs": None,
            }
    return cache


def make_row(
    model_alias: str,
    rule: str,
    axiom: str,
    param_name: str,
    param_value: float,
    min_effect: float,
    cases: Sequence,
    witnesses: Sequence[dict],
    extra: dict | None = None,
) -> dict:
    summary = scenario_summary(cases, witnesses)
    strongest = max(witnesses, key=lambda w: w["effect"]) if witnesses else None
    row = {
        "model_alias": model_alias,
        "rule": rule,
        "axiom": axiom,
        "param_name": param_name,
        "param_value": param_value,
        "min_effect": min_effect,
        "profiles_total": summary["profiles_total"],
        "profiles_with_witness": summary["profiles_with_witness"],
        "fraction_with_witness": summary["fraction_with_witness"],
        "percent_with_witness": 100.0 * summary["fraction_with_witness"],
        "by_block": summary["by_block"],
        "strongest_witness": strongest,
    }
    if extra:
        row.update(extra)
    return row


def sweep_reference(
    nlhf_cases: Sequence[TieNormCase],
    rtbt_cases: Sequence,
    ref: ReferenceConfig,
    rho_cache: dict[str, dict],
    rtbt_cache: dict[str, dict],
    workers: int,
    nlhf_taus: Sequence[float],
    rtbt_betas: Sequence[float],
    min_effect: float,
    comm_max_unique: int,
) -> list[dict]:
    rows: list[dict] = []
    for tau in nlhf_taus:
        per_axiom: dict[str, list[dict]] = {}
        for axiom in ("monotonicity", "positive_involvement", "negative_involvement"):
            witnesses = run_nlhf_axiom(
                nlhf_cases, ref, rho_cache, tau, axiom, workers, min_effect, comm_max_unique
            )
            per_axiom[axiom] = witnesses
            row = make_row(ref.name, "nlhf_tie_norm", axiom, "tau", tau, min_effect, nlhf_cases, witnesses)
            rows.append(row)
            print(json.dumps({k: row[k] for k in ("model_alias", "rule", "axiom", "param_value", "profiles_with_witness", "profiles_total", "fraction_with_witness")}, sort_keys=True), flush=True)
        involvement = [*per_axiom["positive_involvement"], *per_axiom["negative_involvement"]]
        involvement_row = make_row(ref.name, "nlhf_tie_norm", "involvement", "tau", tau, min_effect, nlhf_cases, involvement)
        rows.append(involvement_row)
        print(json.dumps({k: involvement_row[k] for k in ("model_alias", "rule", "axiom", "param_value", "profiles_with_witness", "profiles_total", "fraction_with_witness")}, sort_keys=True), flush=True)
        comm_witnesses = run_nlhf_axiom(
            nlhf_cases, ref, rho_cache, tau, "commutativity", workers, min_effect, comm_max_unique
        )
        comm_row = make_row(
            ref.name,
            "nlhf_tie_norm",
            "commutativity",
            "tau",
            tau,
            min_effect,
            nlhf_cases,
            comm_witnesses,
            {"comm_max_unique_rankings": comm_max_unique, "comm_profiles_checked": sum(compact_unique_ranking_count(c) <= comm_max_unique for c in nlhf_cases)},
        )
        rows.append(comm_row)
        print(json.dumps({k: comm_row[k] for k in ("model_alias", "rule", "axiom", "param_value", "profiles_with_witness", "profiles_total", "fraction_with_witness", "comm_profiles_checked")}, sort_keys=True), flush=True)

    for beta in rtbt_betas:
        per_axiom = {}
        for axiom in ("positive_involvement", "negative_involvement"):
            scenario = Scenario(
                name=f"{ref.name}_rtbt_{axiom}_beta_{beta}",
                axiom=axiom,
                rule="rtbt",
                param=beta,
                model_alias=ref.name,
                rho_source=str(ref.rho_cache) if ref.rho_cache is not None else "uniform",
                ppi_mode="removal_only",
            )
            witnesses = [w for w in run_rtbt_scenario(rtbt_cases, rtbt_cache, scenario, workers) if w["effect"] >= min_effect]
            per_axiom[axiom] = witnesses
            rows.append(make_row(ref.name, "rtbt", axiom, "beta", beta, min_effect, rtbt_cases, witnesses))
        rows.append(make_row(ref.name, "rtbt", "involvement", "beta", beta, min_effect, rtbt_cases, [*per_axiom["positive_involvement"], *per_axiom["negative_involvement"]]))
    return rows


def write_outputs(rows: Sequence[dict], output_dir: Path) -> tuple[Path, Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "nlhf_tie_normalization_parameter_sweeps.json"
    csv_path = output_dir / "nlhf_tie_normalization_parameter_sweeps.csv"
    with json_path.open("w") as handle:
        json.dump(list(rows), handle, indent=2, sort_keys=True)
        handle.write("\n")
    with csv_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "model_alias",
                "rule",
                "axiom",
                "param_name",
                "param_value",
                "min_effect",
                "profiles_total",
                "profiles_with_witness",
                "fraction_with_witness",
                "percent_with_witness",
            ],
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({name: row[name] for name in writer.fieldnames})
    return json_path, csv_path


def threshold_title_value(threshold: float) -> str:
    return f"{threshold:g}"


def plot_rows(
    rows: Sequence[dict],
    output_dir: Path,
    filename_prefix: str = "model_reference_involvement_parameter_sweeps",
) -> list[Path]:
    styles = {
        "uniform": {"label": "Uniform", "color": "#4d4d4d"},
        "nemo_base_strip_identity": {"label": "Nemo", "color": "#1f77b4"},
        "qwen25_base_strip_identity": {"label": "Qwen2.5", "color": "#d62728"},
        "qwen3_base_strip_identity": {"label": "Qwen3", "color": "#2ca02c"},
    }
    panels = [
        ("nlhf_tie_norm", "monotonicity", "NLHF Monotonicity Violation", "tau"),
        ("nlhf_tie_norm", "involvement", "NLHF Involvement Violation", "tau"),
        ("nlhf_tie_norm", "commutativity", "NLHF Commutativity Violation Lower Bound", "tau"),
        ("rtbt", "involvement", "RTBT Involvement Violation", "beta"),
    ]
    min_effect = float(rows[0]["min_effect"]) if rows else 0.0
    slug = f"{min_effect:g}".replace(".", "p")

    fig, axes = plt.subplots(2, 2, figsize=(12, 8), constrained_layout=True)
    fig.suptitle(rf"Violations with magnitude $\Delta \geq {threshold_title_value(min_effect)}$")
    for ax, (rule, axiom, title, param_name) in zip(axes.flat, panels):
        panel_max = 0.0
        for alias, style in styles.items():
            subset = [
                row
                for row in rows
                if row["model_alias"] == alias and row["rule"] == rule and row["axiom"] == axiom
            ]
            subset.sort(key=lambda row: row["param_value"])
            if not subset:
                continue
            ys = [row["percent_with_witness"] for row in subset]
            panel_max = max(panel_max, max(ys))
            ax.plot(
                [row["param_value"] for row in subset],
                ys,
                marker="o",
                linewidth=2.0,
                markersize=5,
                **style,
            )
        ax.set_xscale("log")
        ax.set_xlabel(param_name)
        ax.set_ylabel("% of CoVal profiles")
        ax.set_ylim(0.0, panel_max + max(0.25, 0.08 * panel_max))
        ax.set_title(title)
        ax.grid(True, alpha=0.3)
    axes.flat[0].legend(frameon=False, loc="best")
    png = output_dir / f"{filename_prefix}_min_effect_{slug}.png"
    svg = output_dir / f"{filename_prefix}_min_effect_{slug}.svg"
    fig.savefig(png, dpi=200, bbox_inches="tight")
    fig.savefig(svg, bbox_inches="tight")
    plt.close(fig)
    return [png, svg]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--blocks", nargs="+", default=["world", "personal"])
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/nlhf_tie_normalization_parameter_sweeps_min_effect_1e-6"))
    parser.add_argument("--nemo-rho-cache", type=Path, default=Path("results/reference_distributions/nemo_pytorch_rho_strip_identity_float32.jsonl"))
    parser.add_argument("--qwen25-rho-cache", type=Path, default=Path("results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl"))
    parser.add_argument("--qwen3-rho-cache", type=Path, default=None)
    parser.add_argument("--model-aliases", nargs="+", default=None)
    parser.add_argument("--nlhf-taus", type=parse_float_list, default=DEFAULT_NLHF_TAUS)
    parser.add_argument("--rtbt-betas", type=parse_float_list, default=DEFAULT_RTBT_BETAS)
    parser.add_argument("--min-effect", type=float, default=1e-6)
    parser.add_argument("--comm-max-unique-rankings", type=int, default=18)
    args = parser.parse_args()

    nlhf_cases = load_cases_tie_norm(args.dataset, args.blocks)
    rtbt_cases = load_rtbt_cases(args.dataset, args.blocks)
    refs = [
        ReferenceConfig("uniform", None),
        ReferenceConfig("nemo_base_strip_identity", args.nemo_rho_cache),
        ReferenceConfig("qwen25_base_strip_identity", args.qwen25_rho_cache),
    ]
    if args.qwen3_rho_cache is not None and args.qwen3_rho_cache.exists():
        refs.append(ReferenceConfig("qwen3_base_strip_identity", args.qwen3_rho_cache))
    if args.model_aliases is not None:
        wanted = set(args.model_aliases)
        refs = [ref for ref in refs if ref.name in wanted]
        missing = wanted.difference(ref.name for ref in refs)
        if missing:
            raise ValueError(f"Requested model aliases are unavailable: {sorted(missing)}")

    rows: list[dict] = []
    for ref in refs:
        rho_cache = {} if ref.rho_cache is None else load_rho_cache(ref.rho_cache)
        rtbt_cache = uniform_rho_cache(rtbt_cases) if ref.rho_cache is None else load_rtbt_rho_cache(ref.rho_cache)
        rows.extend(
            sweep_reference(
                nlhf_cases,
                rtbt_cases,
                ref,
                rho_cache,
                rtbt_cache,
                args.workers,
                args.nlhf_taus,
                args.rtbt_betas,
                args.min_effect,
                args.comm_max_unique_rankings,
            )
        )

    json_path, csv_path = write_outputs(rows, args.output_dir)
    plots = plot_rows(rows, args.output_dir)
    print(json.dumps({"json": str(json_path), "csv": str(csv_path), "plots": [str(path) for path in plots], "rows": len(rows)}, sort_keys=True))


if __name__ == "__main__":
    main()
