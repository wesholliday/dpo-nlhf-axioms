#!/usr/bin/env python3
"""Derive temperature-smoothed reference caches from model reference caches.

The base caches store full-sequence log probabilities and completion token
counts. This script recomputes rho after dividing sequence log-probabilities by
a temperature before normalization.
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


def transformed_rho(
    record: dict,
    *,
    temperature: float,
) -> tuple[dict[str, float], dict[str, float]]:
    logps = {label: float(value) for label, value in record["response_logprobs"].items()}
    if temperature <= 0:
        raise ValueError("--temperature must be positive")
    scores = {label: logp / temperature for label, logp in logps.items()}
    return softmax(scores), scores


def output_path_for(input_path: Path, output_dir: Path, temperature: float) -> Path:
    stem = input_path.stem
    suffix = f"temperature_{temperature:g}".replace(".", "p")
    return output_dir / f"{stem}_{suffix}.jsonl"


def derive_cache(input_path: Path, output_path: Path, temperature: float) -> int:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with input_path.open() as source, output_path.open("w") as target:
        for line in source:
            if not line.strip():
                continue
            record = json.loads(line)
            rho, scores = transformed_rho(
                record,
                temperature=temperature,
            )
            out = dict(record)
            out["rho"] = rho
            out["reference_ablation"] = "temperature"
            out["source_reference_cache"] = str(input_path)
            out["source_rho"] = record.get("rho")
            out["transformed_scores"] = scores
            out["temperature"] = temperature
            target.write(json.dumps(out, sort_keys=True) + "\n")
            count += 1
    return count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output-dir", type=Path, default=Path("results/reference_distributions/robustness"))
    parser.add_argument("--temperature", type=float, default=2.0)
    args = parser.parse_args()

    outputs = []
    for input_path in args.inputs:
        output_path = output_path_for(input_path, args.output_dir, args.temperature)
        count = derive_cache(input_path, output_path, args.temperature)
        outputs.append({"input": str(input_path), "output": str(output_path), "rows": count})
    print(json.dumps({"outputs": outputs}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
