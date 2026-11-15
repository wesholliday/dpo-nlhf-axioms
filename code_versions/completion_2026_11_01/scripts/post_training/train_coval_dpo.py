#!/usr/bin/env python3
"""Train DPO on one CoVal preference profile.

This script builds pairwise chosen/rejected examples from a CoVal ranking
profile, precomputes reference log-probabilities under the base model, then
trains a LoRA adapter and logs the induced distribution over A/B/C/D.

The renderers intentionally match the formatting used by
`scripts/reference_distributions/extract_model_reference_pytorch.py` for the
model-reference caches.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

os.environ.setdefault("TRANSFORMERS_NO_TF", "1")
os.environ.setdefault("TRANSFORMERS_NO_FLAX", "1")
os.environ.setdefault("USE_TF", "0")
os.environ.setdefault("USE_FLAX", "0")

import numpy as np
import torch
import torch.nn.functional as F
from peft import LoraConfig, get_peft_model
from transformers import AutoModelForCausalLM, AutoTokenizer

from scripts.theory.nlhf_tie_normalization import load_cases_tie_norm, parse_ranking


LABELS = ("A", "B", "C", "D")
OPENAI_IDENTITY_LINE = "You are ChatGPT, a large language model trained by OpenAI."


@dataclass(frozen=True)
class PromptCase:
    prompt_id: str
    prompt_messages: list[dict[str, str]]
    responses: dict[str, str]


@dataclass(frozen=True)
class EncodedCompletion:
    label: str
    input_ids: torch.Tensor
    attention_mask: torch.Tensor
    completion_mask: torch.Tensor
    completion_tokens: int


def compact_ranking(ranking: str) -> str:
    return ranking.replace(" ", "")


def safe_tag(text: str) -> str:
    out = text.replace(">", "gt").replace("=", "eq").replace(",", "")
    return "".join(ch if ch.isalnum() or ch in {"-", "_", "."} else "_" for ch in out)


def transform_identity_line(content: str, identity_mode: str) -> str:
    if identity_mode == "exact":
        return content
    if identity_mode == "strip_identity":
        return "\n".join(
            line for line in content.splitlines() if line.strip() != OPENAI_IDENTITY_LINE
        ).strip()
    if identity_mode == "neutralize_identity":
        out: list[str] = []
        replaced = False
        for line in content.splitlines():
            if line.strip() == OPENAI_IDENTITY_LINE:
                if not replaced:
                    out.append("You are a helpful assistant.")
                    replaced = True
            else:
                out.append(line)
        return "\n".join(out).strip()
    raise ValueError(f"Unknown identity mode: {identity_mode}")


def normalize_prompt_messages(
    raw_messages: list[dict], identity_mode: str
) -> list[dict[str, str]]:
    system_chunks: list[str] = []
    chat_messages: list[dict[str, str]] = []
    for message in raw_messages:
        role = message.get("role")
        content = message.get("content")
        if not isinstance(content, str):
            continue
        if role in {"developer", "system"}:
            transformed = transform_identity_line(content, identity_mode)
            if transformed:
                system_chunks.append(transformed)
        elif role in {"user", "assistant"}:
            if not content.strip():
                continue
            chat_messages.append({"role": role, "content": content})
    if system_chunks:
        return [{"role": "system", "content": "\n\n".join(system_chunks)}] + chat_messages
    return chat_messages


def load_prompt_case(dataset: Path, prompt_id: str, identity_mode: str) -> PromptCase:
    with dataset.open() as handle:
        for line in handle:
            obj = json.loads(line)
            if obj.get("prompt_id") != prompt_id:
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
                raise ValueError(f"{prompt_id} does not have exactly A/B/C/D responses")
            return PromptCase(
                prompt_id=prompt_id,
                prompt_messages=normalize_prompt_messages(
                    obj["prompt"]["messages"], identity_mode=identity_mode
                ),
                responses=responses,
            )
    raise KeyError(f"Prompt id not found: {prompt_id}")


def render_qwen_prefix(messages: list[dict[str, str]]) -> str:
    if not messages or messages[0]["role"] != "system":
        messages = [{"role": "system", "content": "You are a helpful assistant."}, *messages]
    pieces: list[str] = []
    for message in messages:
        pieces.append(f"<|im_start|>{message['role']}\n{message['content']}<|im_end|>\n")
    pieces.append("<|im_start|>assistant\n")
    return "".join(pieces)


def render_qwen_full(messages: list[dict[str, str]], response_text: str) -> str:
    return render_qwen_prefix(messages) + response_text + "<|im_end|>\n"


def render_llama2_prefix(messages: list[dict[str, str]]) -> str:
    if not messages:
        raise ValueError("llama2 rendering requires at least one user message")
    if messages[0]["role"] == "system":
        if len(messages) >= 2 and messages[1]["role"] == "user":
            pieces = [
                f"[INST] <<SYS>>\n{messages[0]['content']}\n<</SYS>> {messages[1]['content']} [/INST]"
            ]
            start = 2
        else:
            # Some CoVal prompts contain a developer/system preamble followed by
            # an assistant acknowledgement before the first user message.
            pieces = [f"[INST] <<SYS>>\n{messages[0]['content']}\n<</SYS>> [/INST]"]
            start = 1
    elif messages[0]["role"] == "user":
        pieces = [f" <s>[INST]{messages[0]['content']}  [/INST]"]
        start = 1
    else:
        raise ValueError(f"llama2 rendering cannot start with role {messages[0]['role']}")

    idx = start
    while idx < len(messages):
        current = messages[idx]
        if current["role"] == "user":
            pieces.append(f"<s>[INST]{current['content']}  [/INST]")
            idx += 1
            continue
        if current["role"] != "assistant":
            raise ValueError("Unexpected llama2 message order")
        assistant_chunks: list[str] = []
        while idx < len(messages) and messages[idx]["role"] == "assistant":
            if messages[idx]["content"].strip():
                assistant_chunks.append(messages[idx]["content"])
            idx += 1
        if not assistant_chunks:
            continue
        assistant_text = "\n\n".join(assistant_chunks)
        if idx < len(messages) and messages[idx]["role"] == "user":
            user = messages[idx]
            pieces.append(f"{assistant_text} </s><s>[INST]{user['content']}  [/INST]")
            idx += 1
            continue
        if idx == len(messages):
            # Match the llama.cpp-compatible formatter behavior for prompts
            # that already end with an assistant turn.
            pieces.append(f"{assistant_text} </s>[/INST]")
            continue
        raise ValueError("Unexpected llama2 message order")
    return "".join(pieces)


def render_llama2_full(messages: list[dict[str, str]], response_text: str) -> str:
    prefix = render_llama2_prefix(messages)
    if messages and messages[-1]["role"] == "assistant":
        return prefix + response_text + "  "
    return prefix + response_text + " </s>"


def render_prefix(messages: list[dict[str, str]], renderer: str) -> str:
    if renderer == "qwen":
        return render_qwen_prefix(messages)
    if renderer == "llama2":
        return render_llama2_prefix(messages)
    raise ValueError(f"Unknown renderer: {renderer}")


def render_full(messages: list[dict[str, str]], response_text: str, renderer: str) -> str:
    if renderer == "qwen":
        return render_qwen_full(messages, response_text)
    if renderer == "llama2":
        return render_llama2_full(messages, response_text)
    raise ValueError(f"Unknown renderer: {renderer}")


def first_completion_index(offsets: list[tuple[int, int]], prefix_len: int) -> int:
    for idx, (_start, end) in enumerate(offsets):
        if end > prefix_len:
            return idx
    raise ValueError("Could not find completion token boundary")


def encode_completion(
    tokenizer,
    label: str,
    prefix_text: str,
    full_text: str,
    max_length: int,
) -> EncodedCompletion:
    encoded = tokenizer(
        full_text,
        add_special_tokens=False,
        return_offsets_mapping=True,
        truncation=True,
        max_length=max_length,
        return_tensors="pt",
    )
    input_ids = encoded["input_ids"][0]
    attention_mask = encoded["attention_mask"][0]
    offsets = [tuple(x) for x in encoded["offset_mapping"][0].tolist()]
    first_idx = first_completion_index(offsets, len(prefix_text))
    completion_mask = torch.zeros_like(input_ids, dtype=torch.bool)
    completion_mask[first_idx:] = True
    if not bool(completion_mask.any()):
        raise ValueError(f"Empty completion for {label}")
    if offsets[-1][1] < len(full_text):
        raise ValueError(f"Tokenized transcript for {label} was truncated; raise --max-length")
    return EncodedCompletion(
        label=label,
        input_ids=input_ids,
        attention_mask=attention_mask,
        completion_mask=completion_mask,
        completion_tokens=int(completion_mask.sum().item()),
    )


def collate_encoded(
    items: Sequence[EncodedCompletion],
    pad_token_id: int,
    device: torch.device,
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    max_len = max(int(item.input_ids.shape[0]) for item in items)
    input_ids = torch.full((len(items), max_len), pad_token_id, dtype=torch.long)
    attention_mask = torch.zeros((len(items), max_len), dtype=torch.long)
    completion_mask = torch.zeros((len(items), max_len), dtype=torch.bool)
    for row, item in enumerate(items):
        length = int(item.input_ids.shape[0])
        input_ids[row, :length] = item.input_ids
        attention_mask[row, :length] = item.attention_mask
        completion_mask[row, :length] = item.completion_mask
    return input_ids.to(device), attention_mask.to(device), completion_mask.to(device)


def sequence_logprobs(
    model,
    encoded_items: Sequence[EncodedCompletion],
    pad_token_id: int,
    device: torch.device,
) -> torch.Tensor:
    input_ids, attention_mask, completion_mask = collate_encoded(
        encoded_items, pad_token_id, device
    )
    outputs = model(input_ids=input_ids, attention_mask=attention_mask)
    logits = outputs.logits[:, :-1, :].float()
    targets = input_ids[:, 1:]
    shifted_completion = completion_mask[:, 1:]
    shifted_attention = attention_mask[:, 1:].bool()
    token_logprobs = torch.gather(
        F.log_softmax(logits, dim=-1), dim=-1, index=targets.unsqueeze(-1)
    ).squeeze(-1)
    mask = shifted_completion & shifted_attention
    return (token_logprobs * mask.float()).sum(dim=-1)


@torch.inference_mode()
def score_candidates(
    model,
    encoded_by_label: dict[str, EncodedCompletion],
    pad_token_id: int,
    device: torch.device,
) -> tuple[dict[str, float], dict[str, float]]:
    items = [encoded_by_label[label] for label in LABELS]
    logps_tensor = sequence_logprobs(model, items, pad_token_id, device)
    logps = {label: float(logps_tensor[idx].detach().cpu()) for idx, label in enumerate(LABELS)}
    norm = logsumexp(logps.values())
    probs = {label: math.exp(logps[label] - norm) for label in LABELS}
    return logps, probs


def logsumexp(values: Iterable[float]) -> float:
    values = list(values)
    top = max(values)
    return top + math.log(sum(math.exp(value - top) for value in values))


def load_rankings(
    dataset: Path,
    prompt_id: str,
    block_name: str,
    delete_ranking: str | None,
) -> tuple[tuple[str, ...], list[str], str | None]:
    cases = [
        case
        for case in load_cases_tie_norm(dataset, [block_name])
        if case.prompt_id == prompt_id and case.block_name == block_name
    ]
    if len(cases) != 1:
        raise ValueError(f"Expected one case for {prompt_id}:{block_name}, found {len(cases)}")
    case = cases[0]
    rankings = list(case.rankings)
    deleted: str | None = None
    if delete_ranking is not None:
        want = compact_ranking(delete_ranking)
        for idx, ranking in enumerate(rankings):
            if compact_ranking(ranking) == want:
                deleted = rankings.pop(idx)
                break
        if deleted is None:
            counts: dict[str, int] = {}
            for ranking in rankings:
                key = compact_ranking(ranking)
                counts[key] = counts.get(key, 0) + 1
            available = ", ".join(f"{n}x {r}" for r, n in sorted(counts.items()))
            raise ValueError(f"Ranking to delete not found: {delete_ranking}. Available: {available}")
    return case.response_indices, rankings, deleted


def ranking_pairs(ranking: str, labels: Sequence[str]) -> list[tuple[str, str]]:
    label_set = set(labels)
    blocks = [[label for label in block if label in label_set] for block in parse_ranking(ranking)]
    pairs: list[tuple[str, str]] = []
    for i, winners in enumerate(blocks):
        for losers in blocks[i + 1 :]:
            for winner in winners:
                for loser in losers:
                    pairs.append((winner, loser))
    return pairs


def build_pair_indices(
    rankings: Sequence[str],
    labels: Sequence[str],
) -> tuple[torch.Tensor, torch.Tensor, dict[str, int]]:
    label_to_idx = {label: idx for idx, label in enumerate(labels)}
    chosen: list[int] = []
    rejected: list[int] = []
    pair_counts: dict[str, int] = {}
    for ranking in rankings:
        for winner, loser in ranking_pairs(ranking, labels):
            chosen.append(label_to_idx[winner])
            rejected.append(label_to_idx[loser])
            key = f"{winner}>{loser}"
            pair_counts[key] = pair_counts.get(key, 0) + 1
    if not chosen:
        raise ValueError("Profile produced no strict pairwise comparisons")
    return torch.tensor(chosen, dtype=torch.long), torch.tensor(rejected, dtype=torch.long), pair_counts


def choose_device(name: str) -> torch.device:
    if name == "mps":
        if not torch.backends.mps.is_available():
            raise RuntimeError("MPS requested but unavailable in this process")
        return torch.device("mps")
    if name == "cuda":
        if not torch.cuda.is_available():
            raise RuntimeError("CUDA requested but unavailable")
        return torch.device("cuda")
    return torch.device("cpu")


def dtype_from_name(name: str) -> torch.dtype:
    if name == "float16":
        return torch.float16
    if name == "bfloat16":
        return torch.bfloat16
    if name == "float32":
        return torch.float32
    raise ValueError(f"Unknown dtype: {name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset", type=Path, default=Path("data/coval_comparisons.jsonl"))
    parser.add_argument("--prompt-id", required=True)
    parser.add_argument("--block-name", choices=("world", "personal"), default="world")
    parser.add_argument("--delete-ranking", default=None)
    parser.add_argument("--model", default="/tmp/qwen25_7b_bf16")
    parser.add_argument("--renderer", choices=("qwen", "llama2"), default="qwen")
    parser.add_argument("--identity-mode", choices=("exact", "strip_identity", "neutralize_identity"), default="strip_identity")
    parser.add_argument("--device", choices=("cpu", "mps", "cuda"), default="mps")
    parser.add_argument(
        "--dtype",
        choices=("float16", "bfloat16", "float32"),
        default="float16",
        help="Computation dtype. Paper Mistral-Nemo DPO runs override this to float32.",
    )
    parser.add_argument(
        "--steps",
        type=int,
        default=100,
        help="Number of optimizer steps. The paper's DPO/RTBT runs use 100.",
    )
    parser.add_argument("--batch-size", type=int, default=4)
    parser.add_argument(
        "--full-batch",
        action="store_true",
        help="Use every profile-derived pair on every step instead of random minibatches.",
    )
    parser.add_argument("--beta", type=float, default=0.1)
    parser.add_argument(
        "--lr",
        type=float,
        default=1e-5,
        help="Learning rate. Paper Qwen DPO runs use 5e-5; Mistral-Nemo uses 1e-5.",
    )
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-length", type=int, default=4096)
    parser.add_argument(
        "--fix-mistral-regex",
        action="store_true",
        help="Pass fix_mistral_regex=True when loading Mistral-family tokenizers.",
    )
    parser.add_argument("--log-every", type=int, default=10)
    parser.add_argument("--lora-r", type=int, default=8)
    parser.add_argument("--lora-alpha", type=int, default=32)
    parser.add_argument("--lora-dropout", type=float, default=0.05)
    parser.add_argument("--target-modules", default="q_proj,v_proj")
    parser.add_argument(
        "--grad-clip",
        type=float,
        default=None,
        help="Clip trainable parameter gradient norm before each optimizer step.",
    )
    parser.add_argument("--output-dir", type=Path, default=Path("results/intermediate/dpo_coval_runs"))
    parser.add_argument("--tag", default=None)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--save-policy", action="store_true")
    args = parser.parse_args()

    random.seed(args.seed)
    np.random.seed(args.seed)
    torch.manual_seed(args.seed)

    device = choose_device(args.device)
    dtype = dtype_from_name(args.dtype)
    labels, rankings, deleted = load_rankings(
        args.dataset, args.prompt_id, args.block_name, args.delete_ranking
    )
    if tuple(labels) != LABELS:
        raise ValueError(f"This script expects labels A/B/C/D, found {labels}")

    chosen_idx_cpu, rejected_idx_cpu, pair_counts = build_pair_indices(rankings, labels)
    print(
        f"profile={args.prompt_id}:{args.block_name} voters={len(rankings)} "
        f"pairs={len(chosen_idx_cpu)} deleted={deleted}"
    )
    print("pair_counts=" + json.dumps(pair_counts, sort_keys=True))
    if args.dry_run:
        return

    prompt_case = load_prompt_case(args.dataset, args.prompt_id, args.identity_mode)
    prefix_text = render_prefix(prompt_case.prompt_messages, args.renderer)

    tokenizer_kwargs = {"trust_remote_code": True}
    if args.fix_mistral_regex:
        tokenizer_kwargs["fix_mistral_regex"] = True
    tokenizer = AutoTokenizer.from_pretrained(args.model, **tokenizer_kwargs)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    if tokenizer.pad_token_id is None:
        raise ValueError("Tokenizer has no pad_token_id")

    encoded_by_label: dict[str, EncodedCompletion] = {}
    for label in LABELS:
        full_text = render_full(prompt_case.prompt_messages, prompt_case.responses[label], args.renderer)
        encoded_by_label[label] = encode_completion(
            tokenizer, label, prefix_text, full_text, args.max_length
        )
    encoded_items = [encoded_by_label[label] for label in LABELS]

    print(
        "completion_tokens="
        + json.dumps({label: encoded_by_label[label].completion_tokens for label in LABELS}, sort_keys=True)
    )
    print(f"loading model={args.model} dtype={args.dtype} device={device}")
    model = AutoModelForCausalLM.from_pretrained(
        args.model,
        torch_dtype=dtype,
        trust_remote_code=True,
    )
    model.to(device)
    model.eval()

    with torch.inference_mode():
        ref_logps_tensor = sequence_logprobs(
            model, encoded_items, tokenizer.pad_token_id, device
        ).detach()
    ref_logps = {label: float(ref_logps_tensor[idx].cpu()) for idx, label in enumerate(LABELS)}
    ref_norm = logsumexp(ref_logps.values())
    ref_probs = {label: math.exp(ref_logps[label] - ref_norm) for label in LABELS}
    print("reference_probs=" + json.dumps(ref_probs, sort_keys=True))

    target_modules = [name.strip() for name in args.target_modules.split(",") if name.strip()]
    lora_config = LoraConfig(
        r=args.lora_r,
        lora_alpha=args.lora_alpha,
        lora_dropout=args.lora_dropout,
        target_modules=target_modules,
        bias="none",
        task_type="CAUSAL_LM",
    )
    model = get_peft_model(model, lora_config)
    model.train()
    model.print_trainable_parameters()

    optimizer = torch.optim.AdamW(
        [parameter for parameter in model.parameters() if parameter.requires_grad],
        lr=args.lr,
    )

    chosen_idx = chosen_idx_cpu.to(device)
    rejected_idx = rejected_idx_cpu.to(device)
    ref_logps_tensor = ref_logps_tensor.to(device)
    num_pairs = int(chosen_idx.shape[0])
    log_rows: list[dict] = []

    def log_step(step: int, loss_value: float | None = None) -> None:
        model.eval()
        with torch.inference_mode():
            logps, probs = score_candidates(model, encoded_by_label, tokenizer.pad_token_id, device)
        model.train()
        row = {"step": step, "loss": loss_value, "logprobs": logps, "probs": probs}
        log_rows.append(row)
        prob_text = " ".join(f"{label}={probs[label]:.4g}" for label in LABELS)
        if loss_value is None:
            print(f"step {step}: {prob_text}")
        else:
            print(f"step {step}: loss={loss_value:.6g} {prob_text}")

    log_step(0)
    for step in range(1, args.steps + 1):
        if args.full_batch:
            batch_chosen = chosen_idx
            batch_rejected = rejected_idx
        else:
            batch_indices = torch.randint(0, num_pairs, (args.batch_size,), device=device)
            batch_chosen = chosen_idx[batch_indices]
            batch_rejected = rejected_idx[batch_indices]

        policy_logps = sequence_logprobs(model, encoded_items, tokenizer.pad_token_id, device)
        log_ratio_chosen = policy_logps[batch_chosen] - ref_logps_tensor[batch_chosen]
        log_ratio_rejected = policy_logps[batch_rejected] - ref_logps_tensor[batch_rejected]
        logits = args.beta * (log_ratio_chosen - log_ratio_rejected)
        loss = -F.logsigmoid(logits).mean()
        if not bool(torch.isfinite(loss).detach().cpu()):
            raise FloatingPointError(f"Non-finite loss at step={step}")

        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        if args.grad_clip is not None:
            torch.nn.utils.clip_grad_norm_(
                [parameter for parameter in model.parameters() if parameter.requires_grad],
                max_norm=args.grad_clip,
            )
        optimizer.step()

        if step % args.log_every == 0 or step == args.steps:
            log_step(step, float(loss.detach().cpu()))

    tag_bits = [
        args.prompt_id,
        args.block_name,
        "minus_" + safe_tag(compact_ranking(args.delete_ranking)) if args.delete_ranking else "full",
        f"beta{args.beta}",
        f"seed{args.seed}",
    ]
    if args.tag:
        tag_bits.append(safe_tag(args.tag))
    run_tag = "__".join(tag_bits).replace("/", "_")
    run_dir = args.output_dir / run_tag
    run_dir.mkdir(parents=True, exist_ok=True)
    record = {
        "prompt_id": args.prompt_id,
        "block_name": args.block_name,
        "deleted_ranking": deleted,
        "rankings": rankings,
        "pair_counts": pair_counts,
        "model": args.model,
        "renderer": args.renderer,
        "identity_mode": args.identity_mode,
        "device": str(device),
        "dtype": args.dtype,
        "fix_mistral_regex": args.fix_mistral_regex,
        "beta": args.beta,
        "lr": args.lr,
        "batch_size": args.batch_size,
        "full_batch": args.full_batch,
        "steps": args.steps,
        "grad_clip": args.grad_clip,
        "lora": {
            "r": args.lora_r,
            "alpha": args.lora_alpha,
            "dropout": args.lora_dropout,
            "target_modules": target_modules,
        },
        "completion_tokens": {
            label: encoded_by_label[label].completion_tokens for label in LABELS
        },
        "reference_logprobs": ref_logps,
        "reference_probs": ref_probs,
        "training_log": log_rows,
    }
    with (run_dir / "run.json").open("w") as handle:
        json.dump(record, handle, indent=2, sort_keys=True)
    if args.save_policy:
        model.save_pretrained(run_dir / "policy_lora")
        tokenizer.save_pretrained(run_dir / "policy_lora")
    print(f"wrote {run_dir / 'run.json'}")


if __name__ == "__main__":
    main()
