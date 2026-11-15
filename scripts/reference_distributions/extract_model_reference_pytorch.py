#!/usr/bin/env python3
"""Extract PyTorch-scored CoVal reference distributions over A/B/C/D.

For each prompt in `data/coval_comparisons.jsonl`, it scores the four fixed
CoVal candidate responses as complete assistant replies under a Hugging Face
causal LM, then normalizes those four log-probabilities into a restricted
reference distribution `rho`.

The prompt rendering and full-response scoring intentionally reuse the same
code path used by the empirical DPO/NLHF training scripts, so the saved
reference cache lines up with the training runs.
"""

from __future__ import annotations

import argparse
import gc
import json
import math
import os
import time
from dataclasses import dataclass
from pathlib import Path

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer

from scripts.post_training.train_coval_dpo import (
    LABELS,
    EncodedCompletion,
    choose_device,
    dtype_from_name,
    encode_completion,
    logsumexp,
    normalize_prompt_messages,
    render_full,
    render_prefix,
    safe_tag,
    sequence_logprobs,
)


@dataclass(frozen=True)
class PromptCase:
    prompt_id: str
    prompt_messages: list[dict[str, str]]
    responses: dict[str, str]


def load_prompt_cases(dataset: Path, identity_mode: str) -> list[PromptCase]:
    seen: set[str] = set()
    cases: list[PromptCase] = []
    with dataset.open() as handle:
        for line in handle:
            obj = json.loads(line)
            prompt_id = obj.get("prompt_id")
            if not isinstance(prompt_id, str) or prompt_id in seen:
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
                if assistant_text is not None:
                    responses[response["response_index"]] = assistant_text
            if set(responses) != set(LABELS):
                continue
            seen.add(prompt_id)
            cases.append(
                PromptCase(
                    prompt_id=prompt_id,
                    prompt_messages=normalize_prompt_messages(
                        obj["prompt"]["messages"], identity_mode=identity_mode
                    ),
                    responses=responses,
                )
            )
    return cases


def read_seen_prompt_ids(path: Path) -> set[str]:
    seen: set[str] = set()
    if not path.exists():
        return seen
    with path.open() as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            prompt_id = row.get("prompt_id")
            if isinstance(prompt_id, str):
                seen.add(prompt_id)
    return seen


def append_jsonl(path: Path, row: dict) -> None:
    with path.open("a") as handle:
        handle.write(json.dumps(row, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())


def write_status(path: Path, status: dict) -> None:
    with path.open("w") as handle:
        json.dump(status, handle, indent=2, sort_keys=True)


def maybe_empty_cache(device: torch.device) -> None:
    if device.type == "mps":
        try:
            torch.mps.empty_cache()
        except Exception:
            pass
    elif device.type == "cuda":
        torch.cuda.empty_cache()


def parse_csv(text: str) -> list[str]:
    return [part.strip() for part in text.split(",") if part.strip()]


def select_shard(cases: list[PromptCase], num_shards: int, shard_index: int) -> list[PromptCase]:
    if num_shards < 1:
        raise ValueError("--num-shards must be at least 1")
    if shard_index < 0 or shard_index >= num_shards:
        raise ValueError("--shard-index must satisfy 0 <= shard-index < num-shards")
    if num_shards == 1:
        return cases
    return [case for idx, case in enumerate(cases) if idx % num_shards == shard_index]


def default_output_path(
    output_dir: Path,
    model_alias: str,
    identity_mode: str,
    tag: str | None,
) -> Path:
    suffix = f"_{safe_tag(tag)}" if tag else ""
    return output_dir / f"{safe_tag(model_alias)}_fullprob_rho_{identity_mode}{suffix}.jsonl"


def score_prompt(
    model,
    tokenizer,
    case: PromptCase,
    renderer: str,
    device: torch.device,
    max_length: int,
) -> tuple[dict[str, float], dict[str, float], dict[str, int]]:
    prefix_text = render_prefix(case.prompt_messages, renderer)
    encoded_items: list[EncodedCompletion] = []
    completion_tokens: dict[str, int] = {}
    for label in LABELS:
        full_text = render_full(case.prompt_messages, case.responses[label], renderer)
        encoded = encode_completion(
            tokenizer,
            label,
            prefix_text,
            full_text,
            max_length,
        )
        encoded_items.append(encoded)
        completion_tokens[label] = encoded.completion_tokens
    with torch.inference_mode():
        logps_tensor = sequence_logprobs(
            model, encoded_items, tokenizer.pad_token_id, device
        ).detach()
    response_logprobs = {
        label: float(logps_tensor[idx].cpu()) for idx, label in enumerate(LABELS)
    }
    norm = logsumexp(response_logprobs.values())
    rho = {
        label: math.exp(response_logprobs[label] - norm) for label in LABELS
    }
    return response_logprobs, rho, completion_tokens


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
    parser.add_argument("--model-alias", default=None)
    parser.add_argument("--model-name", default=None)
    parser.add_argument("--renderer", choices=("qwen", "llama2"), default="qwen")
    parser.add_argument(
        "--identity-mode",
        choices=("exact", "strip_identity", "neutralize_identity"),
        default="strip_identity",
    )
    parser.add_argument("--device", choices=("cpu", "mps", "cuda"), default="mps")
    parser.add_argument("--dtype", choices=("float16", "bfloat16", "float32"), default="float16")
    parser.add_argument("--max-length", type=int, default=4096)
    parser.add_argument("--prompt-id", default=None)
    parser.add_argument("--max-prompts", type=int, default=None)
    parser.add_argument("--num-shards", type=int, default=1)
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--output-dir", type=Path, default=Path("results/reference_distributions"))
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--tag", default=None)
    parser.add_argument(
        "--fix-mistral-regex",
        action="store_true",
        help="Pass fix_mistral_regex=True when loading Mistral-family tokenizers.",
    )
    args = parser.parse_args()

    model_alias = args.model_alias or safe_tag(Path(args.model).name)
    model_name = args.model_name or model_alias
    device = choose_device(args.device)
    dtype = dtype_from_name(args.dtype)

    cases = load_prompt_cases(args.dataset, args.identity_mode)
    if args.prompt_id is not None:
        cases = [case for case in cases if case.prompt_id == args.prompt_id]
    cases = select_shard(cases, args.num_shards, args.shard_index)
    if args.max_prompts is not None:
        cases = cases[: args.max_prompts]
    total_prompts = len(cases)
    if total_prompts == 0:
        raise ValueError("No prompts selected")

    args.output_dir.mkdir(parents=True, exist_ok=True)
    output_path = args.output or default_output_path(
        args.output_dir, model_alias, args.identity_mode, args.tag
    )
    status_path = output_path.with_suffix(".status.json")
    meta_path = output_path.with_suffix(".meta.json")
    seen = read_seen_prompt_ids(output_path)

    tokenizer_kwargs = {"trust_remote_code": True}
    if args.fix_mistral_regex:
        tokenizer_kwargs["fix_mistral_regex"] = True
    tokenizer = AutoTokenizer.from_pretrained(args.model, **tokenizer_kwargs)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    if tokenizer.pad_token_id is None:
        raise ValueError("Tokenizer has no pad_token_id")

    model = AutoModelForCausalLM.from_pretrained(
        args.model,
        torch_dtype=dtype,
        trust_remote_code=True,
    )
    model.to(device)
    model.eval()

    metadata = {
        "model_alias": model_alias,
        "model_name": model_name,
        "model_path": args.model,
        "renderer": args.renderer,
        "identity_mode": args.identity_mode,
        "device": str(device),
        "dtype": args.dtype,
        "n_ctx": args.max_length,
        "dataset": str(args.dataset),
        "num_shards": args.num_shards,
        "shard_index": args.shard_index,
        "output_path": str(output_path),
        "total_prompts_selected": total_prompts,
    }
    with meta_path.open("w") as handle:
        json.dump(metadata, handle, indent=2, sort_keys=True)

    started = time.perf_counter()
    completed = 0
    for idx, case in enumerate(cases, start=1):
        if case.prompt_id in seen:
            completed += 1
            continue
        prompt_start = time.perf_counter()
        response_logprobs, rho, completion_tokens = score_prompt(
            model=model,
            tokenizer=tokenizer,
            case=case,
            renderer=args.renderer,
            device=device,
            max_length=args.max_length,
        )
        prompt_seconds = time.perf_counter() - prompt_start
        row = {
            "prompt_id": case.prompt_id,
            "model_alias": model_alias,
            "model_name": model_name,
            "model_path": args.model,
            "renderer": args.renderer,
            "identity_mode": args.identity_mode,
            "n_ctx": args.max_length,
            "response_logprobs": response_logprobs,
            "rho": rho,
            "completion_tokens": completion_tokens,
            "duration_seconds": prompt_seconds,
        }
        append_jsonl(output_path, row)
        seen.add(case.prompt_id)
        completed += 1
        elapsed = time.perf_counter() - started
        avg = elapsed / completed if completed else float("nan")
        remaining = avg * (total_prompts - completed) if completed else float("nan")
        write_status(
            status_path,
            {
                "completed": completed,
                "total_prompts": total_prompts,
                "last_prompt_id": case.prompt_id,
                "elapsed_seconds": elapsed,
                "avg_seconds_per_prompt": avg,
                "estimated_remaining_seconds": remaining,
                "output_path": str(output_path),
            },
        )
        print(
            f"[{completed}/{total_prompts}] {case.prompt_id} "
            f"secs={prompt_seconds:.2f} rho_top={max(LABELS, key=lambda label: rho[label])} "
            f"eta_hours={remaining / 3600:.2f}"
        )
        maybe_empty_cache(device)
        gc.collect()


if __name__ == "__main__":
    main()
