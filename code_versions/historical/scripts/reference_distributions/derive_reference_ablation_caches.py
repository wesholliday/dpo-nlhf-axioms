#!/usr/bin/env python3
"""Derive robustness-check reference caches from existing model reference caches.

The base caches store full-sequence log probabilities and completion token
counts. This script recomputes rho under transformations that test whether
paper results are driven by sequence-length artifacts or extreme concentration.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Mapping


def softmax(scores: Mapping[str, float]) -> dict[str, float]:
    finite_scores = {label: float(score) for label, score in scores.items()}
    max_score = max(finite_scores.values())
    weights = {label: math.exp(score - max_score) for label, score in finite_scores.items()}
    total = sum(weights.values())
    if total <= 0:
        raise ValueError("Softmax weights have nonpositive total")
    return {label: weight / total for label, weight in weights.items()}


def normalize(weights: Mapping[str, float]) -> dict[str, float]:
    values = {label: float(weight) for label, weight in weights.items()}
    total = sum(values.values())
    if total <= 0:
        raise ValueError("Reference weights have nonpositive total")
    return {label: weight / total for label, weight in values.items()}


def transformed_rho(
    record: dict,
    *,
    transform: str,
    temperature: float,
    epsilon: float,
) -> tuple[dict[str, float], dict[str, float]]:
    logps = {label: float(value) for label, value in record["response_logprobs"].items()}
    if transform == "length_normalized":
        tokens = {label: int(value) for label, value in record["completion_tokens"].items()}
        scores = {label: logps[label] / max(tokens[label], 1) for label in logps}
        return softmax(scores), scores
    if transform == "temperature":
        if temperature <= 0:
            raise ValueError("--temperature must be positive")
        scores = {label: logp / temperature for label, logp in logps.items()}
        return softmax(scores), scores
    if transform == "clipped":
        if not 0 <= epsilon < 1:
            raise ValueError("--epsilon must be in [0, 1)")
        raw_rho = {label: float(value) for label, value in record["rho"].items()}
        clipped = {label: max(epsilon, value) for label, value in raw_rho.items()}
        return normalize(clipped), clipped
    raise ValueError(f"Unknown transform: {transform}")


def output_path_for(input_path: Path, output_dir: Path, transform: str, temperature: float, epsilon: float) -> Path:
    stem = input_path.stem
    if transform == "length_normalized":
        suffix = "length_normalized"
    elif transform == "temperature":
        suffix = f"temperature_{temperature:g}".replace(".", "p")
    elif transform == "clipped":
        suffix = f"clipped_eps_{epsilon:g}".replace(".", "p")
    else:
        suffix = transform
    return output_dir / f"{stem}_{suffix}.jsonl"


def derive_cache(input_path: Path, output_path: Path, transform: str, temperature: float, epsilon: float) -> int:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with input_path.open() as source, output_path.open("w") as target:
        for line in source:
            if not line.strip():
                continue
            record = json.loads(line)
            rho, scores = transformed_rho(
                record,
                transform=transform,
                temperature=temperature,
                epsilon=epsilon,
            )
            out = dict(record)
            out["rho"] = rho
            out["reference_ablation"] = transform
            out["source_reference_cache"] = str(input_path)
            out["source_rho"] = record.get("rho")
            out["transformed_scores"] = scores
            if transform == "temperature":
                out["temperature"] = temperature
            if transform == "clipped":
                out["epsilon"] = epsilon
            target.write(json.dumps(out, sort_keys=True) + "\n")
            count += 1
    return count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output-dir", type=Path, default=Path("results/reference_distributions/robustness"))
    parser.add_argument(
        "--transform",
        choices=["length_normalized", "temperature", "clipped"],
        default="length_normalized",
    )
    parser.add_argument("--temperature", type=float, default=2.0)
    parser.add_argument("--epsilon", type=float, default=0.01)
    args = parser.parse_args()

    outputs = []
    for input_path in args.inputs:
        output_path = output_path_for(input_path, args.output_dir, args.transform, args.temperature, args.epsilon)
        count = derive_cache(input_path, output_path, args.transform, args.temperature, args.epsilon)
        outputs.append({"input": str(input_path), "output": str(output_path), "rows": count})
    print(json.dumps({"outputs": outputs}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
