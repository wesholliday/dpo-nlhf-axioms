#!/usr/bin/env python3
"""Search CoVal for violations under model-induced reference distributions.

Workflow:
1. For each prompt id, estimate a judge-induced reference distribution rho_model
   using a local LM Studio model and a small number of label permutations.
2. Reuse the existing NLHF / RTBT witness logic with that rho_model on the
   associated world/personal profile blocks.

This script is designed for *finding examples* efficiently. It does not try to
estimate prevalence over the whole dataset with a high-permutation budget.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

from scripts.theory.analyze_coval_lb_vs_pb import solve_nlhf
from scripts.theory.search_coval_nlhf_reverse_monotonicity import load_cases, parse_ranking
from scripts.theory.search_coval_violation_counts import (
    improvements,
    monotonicity_move_valid,
    ranking_to_string,
    ranking_to_wins,
    singleton_top_ballots,
)
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda


LABELS = ("A", "B", "C", "D")


@dataclass(frozen=True)
class ModelConfig:
    alias: str
    model_name: str
    instructions: str
    top_logprobs: int


MODEL_CONFIGS = {
    "maverick": ModelConfig(
        alias="maverick",
        model_name="llama-4-maverick-17b-128e-instruct",
        instructions=(
            "Choose the single best response overall. "
            "Reply with exactly one uppercase letter: A, B, C, or D. "
            "Do not write words, punctuation, explanations, markdown, or reasoning."
        ),
        top_logprobs=20,
    ),
    "nemo_base": ModelConfig(
        alias="nemo_base",
        model_name="mistral-nemo-base-2407",
        instructions=(
            "You are evaluating four candidate assistant responses to the same user prompt. "
            "Choose the response that is best overall for the user, taking into account "
            "helpfulness, correctness, relevance, clarity, and safety. "
            "Output exactly one token: A, B, C, or D."
        ),
        top_logprobs=50,
    ),
}


@dataclass(frozen=True)
class PromptCase:
    prompt_id: str
    user_prompt: str
    responses: dict[str, str]


@dataclass(frozen=True)
class Scenario:
    name: str
    axiom: str
    rule: str
    param: float


SCENARIOS = [
    Scenario("nlhf_monotonicity_tau_0.01", "monotonicity", "nlhf", 0.01),
    Scenario("nlhf_positive_involvement_tau_0.01", "positive_involvement", "nlhf", 0.01),
    Scenario("rtbt_positive_involvement_beta_0.1", "positive_involvement", "rtbt", 0.1),
]


def load_prompt_cases(dataset: Path) -> dict[str, PromptCase]:
    out: dict[str, PromptCase] = {}
    with dataset.open() as handle:
        for line in handle:
            obj = json.loads(line)
            prompt_id = obj["prompt_id"]
            messages = obj["prompt"]["messages"]
            user_prompt = next(
                (msg["content"] for msg in reversed(messages) if msg.get("role") == "user"),
                None,
            )
            if user_prompt is None:
                continue
            responses: dict[str, str] = {}
            for response in obj["responses"]:
                assistant_text = next(
                    (
                        msg["content"]
                        for msg in response.get("messages", [])
                        if msg.get("role") == "assistant"
                    ),
                    None,
                )
                if assistant_text is None:
                    continue
                responses[response["response_index"]] = assistant_text
            if set(responses) == set(LABELS):
                out[prompt_id] = PromptCase(prompt_id, user_prompt, responses)
    return out


def build_input_text(case: PromptCase, label_to_original: dict[str, str]) -> str:
    parts = [
        "USER PROMPT:",
        case.user_prompt,
        "",
        "CANDIDATE RESPONSES:",
    ]
    for label in LABELS:
        original = label_to_original[label]
        parts.append(f"{label}.")
        parts.append(case.responses[original])
        parts.append("")
    parts.append("Best response:")
    return "\n".join(parts)


def iter_label_maps(mode: str, seed: int, max_permutations: int | None) -> Iterable[dict[str, str]]:
    perms = list(itertools.permutations(LABELS))
    if mode == "all":
        selected = perms
    else:
        rng = random.Random(seed)
        if max_permutations is None:
            raise ValueError("max_permutations required in random mode")
        selected = rng.sample(perms, min(max_permutations, len(perms)))
    for perm in selected:
        yield {label: original for label, original in zip(LABELS, perm)}


def normalize_candidate_token(token: str) -> str | None:
    cleaned = token.strip().strip('"').strip("'").upper()
    return cleaned if cleaned in LABELS else None


def query_lmstudio_distribution(
    api_base: str,
    api_key: str,
    model: ModelConfig,
    case: PromptCase,
    label_map: dict[str, str],
    seed: int,
    timeout: float,
) -> dict | None:
    payload = {
        "model": model.model_name,
        "instructions": model.instructions,
        "input": build_input_text(case, label_map),
        "max_output_tokens": 5,
        "temperature": 0,
        "top_logprobs": model.top_logprobs,
        "include": ["message.output_text.logprobs"],
        "seed": seed,
    }
    req = urllib.request.Request(
        api_base.rstrip("/") + "/responses",
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        data = json.loads(resp.read().decode("utf-8"))

    output = data.get("output", [])
    if not output:
        return None
    content = output[0]["content"][0]
    raw_text = content.get("text", "")
    logprobs = content.get("logprobs") or []
    if not logprobs:
        return None
    tops = logprobs[0].get("top_logprobs", [])
    masses = {label: 0.0 for label in LABELS}
    for entry in tops:
        token = normalize_candidate_token(str(entry.get("token", "")))
        if token is None:
            continue
        masses[token] += math.exp(float(entry["logprob"]))
    candidate_mass = sum(masses.values())
    if candidate_mass <= 0:
        return None
    dist_by_label = {label: masses[label] / candidate_mass for label in LABELS}
    dist_by_original = {label_map[label]: prob for label, prob in dist_by_label.items()}
    return {
        "raw_output": raw_text,
        "candidate_mass": candidate_mass,
        "distribution_by_original": dist_by_original,
        "distribution_by_label": dist_by_label,
        "label_map": label_map,
    }


def estimate_reference_distribution(
    api_base: str,
    api_key: str,
    model: ModelConfig,
    case: PromptCase,
    permutation_mode: str,
    max_permutations: int | None,
    seed: int,
    timeout: float,
) -> dict | None:
    runs = []
    for perm_index, label_map in enumerate(iter_label_maps(permutation_mode, seed, max_permutations)):
        run = query_lmstudio_distribution(
            api_base=api_base,
            api_key=api_key,
            model=model,
            case=case,
            label_map=label_map,
            seed=seed + perm_index,
            timeout=timeout,
        )
        if run is not None:
            runs.append(run)

    if not runs:
        return None

    avg = {label: 0.0 for label in LABELS}
    accepted = 0
    raw_prefix_ok = 0
    masses = []
    for run in runs:
        raw = run["raw_output"]
        prefix = raw[:1].upper() if raw else ""
        if prefix in LABELS:
            raw_prefix_ok += 1
        # Accept all runs with a nonempty candidate distribution; record quality separately.
        accepted += 1
        masses.append(run["candidate_mass"])
        for label, prob in run["distribution_by_original"].items():
            avg[label] += prob

    avg = {label: avg[label] / accepted for label in LABELS}
    return {
        "model_alias": model.alias,
        "model_name": model.model_name,
        "prompt_id": case.prompt_id,
        "rho": avg,
        "num_runs": len(runs),
        "raw_prefix_ok_fraction": raw_prefix_ok / len(runs),
        "avg_candidate_mass": float(np.mean(masses)),
        "runs": runs,
    }


def solve_rule(rule: str, param: float, wins: np.ndarray, rho: np.ndarray) -> np.ndarray | None:
    if rule == "nlhf":
        return solve_nlhf(param, wins, rho)
    if rule == "rtbt":
        return solve_weighted_logistic_borda(param, wins, rho)
    raise ValueError(rule)


def best_monotonicity_witness(case, scenario: Scenario, rho: np.ndarray) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total = np.array(case.total_wins, dtype=float)
    wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]
    observed = solve_rule(scenario.rule, scenario.param, total, rho)
    if observed is None:
        return None
    best = None
    for ai, ranking in enumerate(case.rankings):
        blocks = parse_ranking(ranking)
        for cand in labels:
            idx = index[cand]
            for new_ranking in improvements(blocks, cand):
                new_blocks = parse_ranking(new_ranking)
                if not monotonicity_move_valid(blocks, new_blocks, cand, labels):
                    continue
                modified = total - wins_per[ai] + ranking_to_wins(new_ranking, index)
                after = solve_rule(scenario.rule, scenario.param, modified, rho)
                if after is None:
                    continue
                drop = float(observed[idx] - after[idx])
                if drop <= 0:
                    continue
                witness = {
                    "prompt_id": case.prompt_id,
                    "block_name": case.block_name,
                    "prompt": case.prompt,
                    "scenario": scenario.name,
                    "axiom": scenario.axiom,
                    "rule": scenario.rule,
                    "param": scenario.param,
                    "rho": rho.tolist(),
                    "effect": drop,
                    "candidate": cand,
                    "observed_role": "P",
                    "assessment_index": ai,
                    "old_ranking": ranking,
                    "new_ranking": new_ranking,
                    "before": observed.tolist(),
                    "after": after.tolist(),
                    "response_indices": labels,
                    "n_assessments": len(case.rankings),
                }
                if best is None or drop > best["effect"]:
                    best = witness
    return best


def best_positive_involvement_witness(case, scenario: Scenario, rho: np.ndarray) -> dict | None:
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    total = np.array(case.total_wins, dtype=float)
    wins_per = [np.array(w, dtype=float) for w in case.wins_per_ranking]
    top_ballots = singleton_top_ballots(labels)
    observed = solve_rule(scenario.rule, scenario.param, total, rho)
    if observed is None:
        return None
    best = None

    for ai, ranking in enumerate(case.rankings):
        blocks = parse_ranking(ranking)
        if not blocks or len(blocks[0]) != 1:
            continue
        cand = blocks[0][0]
        reduced = total - wins_per[ai]
        before = solve_rule(scenario.rule, scenario.param, reduced, rho)
        if before is None:
            continue
        idx = index[cand]
        drop = float(before[idx] - observed[idx])
        if drop > 0:
            witness = {
                "prompt_id": case.prompt_id,
                "block_name": case.block_name,
                "prompt": case.prompt,
                "scenario": scenario.name,
                "axiom": scenario.axiom,
                "rule": scenario.rule,
                "param": scenario.param,
                "rho": rho.tolist(),
                "effect": drop,
                "candidate": cand,
                "observed_role": "Pplus",
                "assessment_index": ai,
                "added_ballot": ranking,
                "before": before.tolist(),
                "after": observed.tolist(),
                "response_indices": labels,
                "n_assessments": len(case.rankings),
            }
            best = witness if best is None or drop > best["effect"] else best

    for cand in labels:
        idx = index[cand]
        for ballot in top_ballots[cand]:
            added = total + ranking_to_wins(ballot, index)
            after = solve_rule(scenario.rule, scenario.param, added, rho)
            if after is None:
                continue
            drop = float(observed[idx] - after[idx])
            if drop <= 0:
                continue
            witness = {
                "prompt_id": case.prompt_id,
                "block_name": case.block_name,
                "prompt": case.prompt,
                "scenario": scenario.name,
                "axiom": scenario.axiom,
                "rule": scenario.rule,
                "param": scenario.param,
                "rho": rho.tolist(),
                "effect": drop,
                "candidate": cand,
                "observed_role": "P",
                "added_ballot": ballot,
                "before": observed.tolist(),
                "after": after.tolist(),
                "response_indices": labels,
                "n_assessments": len(case.rankings),
            }
            best = witness if best is None or drop > best["effect"] else best
    return best


def search_prompt_cases(cases_for_prompt: Sequence, rho: np.ndarray) -> dict[str, dict]:
    out: dict[str, dict] = {}
    for case in cases_for_prompt:
        for scenario in SCENARIOS:
            if scenario.axiom == "monotonicity":
                witness = best_monotonicity_witness(case, scenario, rho)
            else:
                witness = best_positive_involvement_witness(case, scenario, rho)
            if witness is None:
                continue
            prev = out.get(scenario.name)
            if prev is None or witness["effect"] > prev["effect"]:
                out[scenario.name] = witness
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--api-base", default="http://127.0.0.1:1234/v1")
    parser.add_argument("--api-key", default="lm-studio")
    parser.add_argument("--models", nargs="+", default=["maverick", "nemo_base"])
    parser.add_argument("--permutation-mode", choices=("all", "random"), default="random")
    parser.add_argument("--max-permutations", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-prompts", type=int, default=None)
    parser.add_argument("--output", type=Path, default=Path("results/intermediate/model_reference_search_results.json"))
    args = parser.parse_args()

    cases = load_cases(args.dataset, ["world", "personal"])
    prompt_cases = load_prompt_cases(args.dataset)
    by_prompt: dict[str, list] = {}
    for case in cases:
        by_prompt.setdefault(case.prompt_id, []).append(case)

    seed_order = [
        "05f972bf-9d75-50d6-bdef-d811150636d6",
        "d3bf506b-8f67-58f4-a1db-e947ef14c60f",
        "3e2e5d04-eab7-5bea-bf12-25a78f23bef3",
        "88de6817-0acd-5e0e-9075-0e4af5252518",
        "f7c752f4-bd18-5ec9-8c03-00db4cababc2",
    ]
    prompt_ids = [pid for pid in seed_order if pid in by_prompt]
    prompt_ids += [pid for pid in by_prompt if pid not in set(prompt_ids)]
    if args.max_prompts is not None:
        prompt_ids = prompt_ids[: args.max_prompts]

    results = {"models": {}, "prompt_order": prompt_ids}
    for alias in args.models:
        model = MODEL_CONFIGS[alias]
        best_by_scenario: dict[str, dict] = {}
        rhos: dict[str, dict] = {}
        for i, prompt_id in enumerate(prompt_ids):
            if prompt_id not in prompt_cases:
                continue
            estimate = estimate_reference_distribution(
                api_base=args.api_base,
                api_key=args.api_key,
                model=model,
                case=prompt_cases[prompt_id],
                permutation_mode=args.permutation_mode,
                max_permutations=args.max_permutations,
                seed=args.seed + 1000 * i,
                timeout=args.timeout,
            )
            if estimate is None:
                continue
            rhos[prompt_id] = estimate
            rho = np.array([estimate["rho"][label] for label in LABELS], dtype=float)
            witnesses = search_prompt_cases(by_prompt[prompt_id], rho)
            for scenario_name, witness in witnesses.items():
                enriched = {
                    **witness,
                    "model_alias": model.alias,
                    "model_name": model.model_name,
                    "rho_quality": {
                        "num_runs": estimate["num_runs"],
                        "avg_candidate_mass": estimate["avg_candidate_mass"],
                        "raw_prefix_ok_fraction": estimate["raw_prefix_ok_fraction"],
                    },
                }
                prev = best_by_scenario.get(scenario_name)
                if prev is None or enriched["effect"] > prev["effect"]:
                    best_by_scenario[scenario_name] = enriched
            print(
                json.dumps(
                    {
                        "model": model.alias,
                        "prompt_id": prompt_id,
                        "avg_candidate_mass": estimate["avg_candidate_mass"],
                        "raw_prefix_ok_fraction": estimate["raw_prefix_ok_fraction"],
                        "found_scenarios": sorted(witnesses),
                    },
                    sort_keys=True,
                )
            )

        results["models"][model.alias] = {
            "model_name": model.model_name,
            "best_witnesses": best_by_scenario,
            "rho_estimates": rhos,
        }

    args.output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
