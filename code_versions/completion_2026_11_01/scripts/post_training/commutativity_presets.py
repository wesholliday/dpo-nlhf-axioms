#!/usr/bin/env python3
"""Shared presets and helpers for sequential commutativity training checks."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

import numpy as np
import torch

from scripts.post_training.train_coval_dpo import LABELS


@dataclass(frozen=True)
class CommutativityPreset:
    prompt_id: str
    block_name: str
    r1: tuple[str, ...]
    r2: tuple[str, ...]


def expand_grouped(groups: Sequence[tuple[int, str]]) -> tuple[str, ...]:
    out: list[str] = []
    for count, ranking in groups:
        out.extend([ranking] * count)
    return tuple(out)


PRESETS: dict[str, CommutativityPreset] = {
    "main_uniform_f450": CommutativityPreset(
        prompt_id="f450f2e2-1d90-577e-a311-c95fb9960433",
        block_name="world",
        r1=expand_grouped(
            [
                (4, "D>A>C>B"),
                (3, "A>D>C>B"),
                (1, "B=C=D>A"),
                (1, "B>C>D>A"),
                (1, "D>A=C>B"),
                (1, "C=D>A>B"),
            ]
        ),
        r2=expand_grouped(
            [
                (1, "A>D>C>B"),
                (1, "A=C>D>B"),
                (1, "A>D>B>C"),
                (3, "C>A>B=D"),
                (1, "D>C>A>B"),
                (1, "B=C>A>D"),
                (1, "A>D>B=C"),
                (1, "A>C>D>B"),
            ]
        ),
    ),
    "qwen_da331": CommutativityPreset(
        prompt_id="da331e43-535b-5dd9-9718-6b048de5e015",
        block_name="world",
        r1=expand_grouped(
            [
                (4, "A>D>B>C"),
                (3, "A>D>B=C"),
                (1, "A=D>B=C"),
                (1, "C>A>B=D"),
                (1, "A>B=C=D"),
                (1, "A>D>C>B"),
            ]
        ),
        r2=expand_grouped(
            [
                (1, "D>A>B>C"),
                (1, "D>A>C=B"),
                (1, "A>D>C>B"),
                (1, "D>B>A>C"),
                (1, "A>B=C>D"),
                (1, "D>A=C>B"),
                (1, "A>D>B=C"),
                (1, "D>A>C>B"),
                (1, "A>D>B>C"),
                (1, "D>A>B=C"),
            ]
        ),
    ),
    "main_nemo_2720": CommutativityPreset(
        prompt_id="2720d0fa-c8f8-598d-a849-e73e3ddccabb",
        block_name="world",
        r1=expand_grouped(
            [
                (2, "B>D>A=C"),
                (1, "B=D>A=C"),
                (2, "D=B>A=C"),
                (1, "B>D>C>A"),
            ]
        ),
        r2=expand_grouped(
            [
                (1, "D>B>A=C"),
                (1, "D>C>B>A"),
                (2, "D>B>A>C"),
                (1, "A=B=C=D"),
            ]
        ),
    ),
    "nemo_9066": CommutativityPreset(
        prompt_id="9066b3b8-4b6f-5676-a873-261341da3c93",
        block_name="world",
        r1=(
            "C>B=A>D",
            "C>B>A>D",
            "B>A=D>C",
            "C>B>D>A",
            "B>A>C>D",
        ),
        r2=(
            "A>B>D>C",
            "C=D>A>B",
            "A>B>C=D",
            "C>A>B=D",
            "B=A>C=D",
        ),
    ),
}


def tensor_by_label(values: torch.Tensor) -> dict[str, float]:
    return {label: float(values[idx].detach().cpu()) for idx, label in enumerate(LABELS)}


def numpy_by_label(values: np.ndarray) -> dict[str, float]:
    return {label: float(values[idx]) for idx, label in enumerate(LABELS)}
