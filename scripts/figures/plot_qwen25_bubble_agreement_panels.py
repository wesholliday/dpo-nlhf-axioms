#!/usr/bin/env python3
"""Matching DPO and NLHF/Nash-MD agreement plots with count bubbles."""

from __future__ import annotations

import argparse
import json
import math
import statistics
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from scripts.figures.plot_filtered_dpo_sweep_agreement import LABELS, PdfCanvas, nice, svg_circle, svg_line, svg_text  # noqa: E402


QWEN25_DPO_INPUT = Path("results/empirical/dpo_rtbt/filtered_profile_sweeps/qwen25.jsonl")
QWEN3_DPO_INPUT = Path("results/empirical/dpo_rtbt/filtered_profile_sweeps/qwen3.jsonl")
NEMO_DPO_INPUT = Path("results/empirical/dpo_rtbt/filtered_profile_sweeps/nemo.jsonl")
NLHF_INPUT = Path("results/empirical/nlhf_nashmd/filtered_profile_sweeps/qwen25.jsonl")
NEMO_NLHF_INPUT = Path("results/empirical/nlhf_nashmd/filtered_profile_sweeps/nemo.jsonl")
QWEN3_NLHF_INPUT = Path("results/empirical/nlhf_nashmd/filtered_profile_sweeps/qwen3.jsonl")
FIGURE_DIR = Path("paper/figures")


@dataclass(frozen=True)
class Row:
    case_key: str
    theory: dict[str, float]
    empirical: dict[str, float]
    reference: dict[str, float]
    tv_theory_reference: float
    tv_empirical_theory: float
    theory_top: str
    empirical_top: str


def tv(left: dict[str, float], right: dict[str, float]) -> float:
    return 0.5 * sum(abs(left[label] - right[label]) for label in LABELS)


def top(probs: dict[str, float]) -> str:
    return max(LABELS, key=lambda label: probs[label])


def correlation(xs: list[float], ys: list[float]) -> float:
    if len(xs) != len(ys) or len(xs) < 2:
        return float("nan")
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    num = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    den_x = math.sqrt(sum((x - mean_x) ** 2 for x in xs))
    den_y = math.sqrt(sum((y - mean_y) ** 2 for y in ys))
    if den_x == 0.0 or den_y == 0.0:
        return float("nan")
    return num / (den_x * den_y)


def mean_absolute_error(xs: list[float], ys: list[float]) -> float:
    if len(xs) != len(ys) or not xs:
        return float("nan")
    return sum(abs(x - y) for x, y in zip(xs, ys)) / len(xs)


def absolute_error_stdev(xs: list[float], ys: list[float]) -> float:
    if len(xs) != len(ys) or not xs:
        return float("nan")
    return statistics.pstdev(abs(x - y) for x, y in zip(xs, ys))


def load_rows(path: Path) -> list[Row]:
    rows: list[Row] = []
    with path.open() as handle:
        for line in handle:
            if not line.strip():
                continue
            raw = json.loads(line)
            if raw.get("error") or not raw.get("theory_available", False):
                continue
            theory = {label: float(raw["theoretical_probs"][label]) for label in LABELS}
            empirical = {label: float(raw["final_probs"][label]) for label in LABELS}
            reference = {label: float(raw["reference_probs"][label]) for label in LABELS}
            rows.append(
                Row(
                    case_key=str(raw["case_key"]),
                    theory=theory,
                    empirical=empirical,
                    reference=reference,
                    tv_theory_reference=tv(theory, reference),
                    tv_empirical_theory=float(raw["tv_to_theory"]),
                    theory_top=top(theory),
                    empirical_top=top(empirical),
                )
            )
    if not rows:
        raise ValueError(f"No usable rows found in {path}")
    return rows


def clamp(value: float) -> float:
    return max(0.0, min(1.0, value))


def xy(left: float, top_y: float, width: float, height: float, x: float, y: float) -> tuple[float, float]:
    return left + clamp(x) * width, top_y + (1.0 - clamp(y)) * height


class SvgTarget:
    def __init__(self, width: int, height: int, title: str) -> None:
        self.parts = [
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img">',
            f"<title>{title}</title>",
            "<desc>Two-panel agreement plot: count-bubble candidate probabilities and profile-level TV discrepancies.</desc>",
            "<style>text{font-family:DejaVu Sans, Helvetica, Arial, sans-serif;}</style>",
            f'<rect width="{width}" height="{height}" fill="#ffffff"/>',
        ]

    def rect(self, x: float, y: float, width: float, height: float, *, fill: str = "none", stroke: str = "none", stroke_width: float = 1.0) -> None:
        self.parts.append(f'<rect x="{x:.2f}" y="{y:.2f}" width="{width:.2f}" height="{height:.2f}" fill="{fill}" stroke="{stroke}" stroke-width="{stroke_width:.2f}"/>')

    def line(self, x1: float, y1: float, x2: float, y2: float, *, stroke: str = "#000000", width: float = 1.0, dash: str | None = None) -> None:
        self.parts.append(svg_line(x1, y1, x2, y2, stroke=stroke, width=width, dash=dash))

    def circle(self, x: float, y: float, radius: float, *, fill: str, stroke: str, opacity: float = 1.0, stroke_width: float = 0.85) -> None:
        self.parts.append(svg_circle(x, y, radius, fill=fill, stroke=stroke, opacity=opacity).replace('stroke-width="0.85"', f'stroke-width="{stroke_width:.2f}"'))

    def text(self, x: float, y: float, content: str, *, size: int = 12, weight: str = "400", fill: str = "#000000", anchor: str = "start") -> None:
        self.parts.append(svg_text(x, y, content, size=size, weight=weight, fill=fill, anchor=anchor))

    def rotated_text(self, x: float, y: float, content: str, *, size: int = 12, fill: str = "#000000", anchor: str = "middle") -> None:
        self.parts.append(
            f'<g transform="translate({x:.2f} {y:.2f}) rotate(-90)">'
            + svg_text(0, 0, content, size=size, fill=fill, anchor=anchor)
            + "</g>"
        )

    def finish(self, output: Path) -> None:
        self.parts.append("</svg>")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("\n".join(self.parts) + "\n")


class PdfTarget:
    def __init__(self, width: int, height: int) -> None:
        self.canvas = PdfCanvas(width, height)
        self.canvas.rect(0, 0, width, height, fill="#ffffff")

    def rect(self, x: float, y: float, width: float, height: float, *, fill: str = "none", stroke: str = "none", stroke_width: float = 1.0) -> None:
        self.canvas.rect(x, y, width, height, fill=None if fill == "none" else fill, stroke=None if stroke == "none" else stroke, width=stroke_width)

    def line(self, x1: float, y1: float, x2: float, y2: float, *, stroke: str = "#000000", width: float = 1.0, dash: str | None = None) -> None:
        self.canvas.line(x1, y1, x2, y2, stroke=stroke, width=width, dash=dash)

    def circle(self, x: float, y: float, radius: float, *, fill: str, stroke: str, opacity: float = 1.0, stroke_width: float = 0.85) -> None:
        self.canvas.circle(x, y, radius, fill=fill, stroke=stroke, width=stroke_width)

    def text(self, x: float, y: float, content: str, *, size: int = 12, weight: str = "400", fill: str = "#000000", anchor: str = "start") -> None:
        self.canvas.text(x, y, content, size=size, fill=fill, anchor=anchor)

    def rotated_text(self, x: float, y: float, content: str, *, size: int = 12, fill: str = "#000000", anchor: str = "middle") -> None:
        self.canvas.rotated_text(x, y, content, size=size, fill=fill, anchor=anchor)

    def finish(self, output: Path) -> None:
        self.canvas.save(output)


def draw_axes(
    target,
    left: float,
    top_y: float,
    width: float,
    height: float,
    *,
    title: str,
    x_label: str,
    y_label: str,
    x_ticks: tuple[float, ...] = (0.0, 0.25, 0.5, 0.75, 1.0),
    y_ticks: tuple[float, ...] = (0.0, 0.25, 0.5, 0.75, 1.0),
    y_max: float = 1.0,
    y_label_offset: float = 0.0,
) -> None:
    bottom = top_y + height
    target.text(left, top_y - 18, title, size=13, weight="700")
    target.rect(left, top_y, width, height, fill="#ffffff", stroke="#000000", stroke_width=0.8)
    for tick in x_ticks:
        x = left + tick * width
        target.line(x, top_y, x, bottom, stroke="#d0d0d0", width=0.6)
        target.line(x, bottom, x, bottom + 4, stroke="#000000", width=0.8)
        target.text(x, bottom + 18, nice(tick), size=9, anchor="middle")
    for tick in y_ticks:
        y = bottom - (tick / y_max) * height
        target.line(left, y, left + width, y, stroke="#d0d0d0", width=0.6)
        target.line(left - 4, y, left, y, stroke="#000000", width=0.8)
        target.text(left - 9, y + 3, nice(tick), size=9, anchor="end")
    target.line(left, bottom, left + width, bottom, stroke="#000000", width=1.0)
    target.line(left, top_y, left, bottom, stroke="#000000", width=1.0)
    target.text(left + width / 2, bottom + 39, x_label, size=10, anchor="middle")
    target.rotated_text(left - 46, top_y + height / 2 + y_label_offset, y_label, size=10, anchor="middle")


def draw_bubble_panel(rows: list[Row], target, left: float, top_y: float, width: float, height: float) -> None:
    draw_axes(
        target,
        left,
        top_y,
        width,
        height,
        title="Candidate probabilities",
        x_label="closed-form probability",
        y_label="empirical probability",
    )
    target.line(left, top_y + height, left + width, top_y, stroke="#777777", width=1.2, dash="5 4")

    bin_width = 0.025
    counts: Counter[tuple[int, int]] = Counter()
    for row in rows:
        for label in LABELS:
            counts[(round(row.theory[label] / bin_width), round(row.empirical[label] / bin_width))] += 1
    max_count = max(counts.values())
    for (bx, by), count in sorted(counts.items(), key=lambda item: item[1]):
        x, y = xy(left, top_y, width, height, bx * bin_width, by * bin_width)
        radius = 1.6 + 15.5 * math.sqrt(count / max_count)
        target.circle(x, y, radius, fill="#f3a0a0", stroke="#7f0000", opacity=0.68, stroke_width=0.7)

    largest = sorted(counts.items(), key=lambda item: item[1], reverse=True)[:2]
    label = ", ".join(f"n={count} at ({nice(bx * bin_width)}, {nice(by * bin_width)})" for (bx, by), count in largest)
    xs = [row.theory[candidate] for row in rows for candidate in LABELS]
    ys = [row.empirical[candidate] for row in rows for candidate in LABELS]
    target.text(
        left,
        top_y + height + 61,
        (
            f"Largest bins: {label}; r={correlation(xs, ys):.3f}; "
            f"MAE={mean_absolute_error(xs, ys):.4f}; SD|err|={absolute_error_stdev(xs, ys):.4f}"
        ),
        size=9,
        fill="#333333",
    )


def draw_profile_panel(rows: list[Row], target, left: float, top_y: float, width: float, height: float, *, y_max: float) -> None:
    draw_axes(
        target,
        left,
        top_y,
        width,
        height,
        title="Profile-level discrepancy",
        x_label="TV(predicted distribution, reference distribution)",
        y_label="TV(post-training distribution, predicted distribution)",
        y_ticks=(0.0, 0.25, 0.5, 0.75, 1.0) if y_max == 1.0 else (0.0, 0.025, 0.05, 0.075, 0.1),
        y_max=y_max,
        y_label_offset=-10.0,
    )
    for row in rows:
        x = left + clamp(row.tv_theory_reference) * width
        y = top_y + (1.0 - clamp(row.tv_empirical_theory / y_max)) * height
        match = row.theory_top == row.empirical_top
        target.circle(
            x,
            y,
            3.1 if match else 4.6,
            fill="#d62728" if match else "#ffffff",
            stroke="#000000",
            opacity=0.70 if match else 1.0,
            stroke_width=0.75,
        )
    target.line(left, top_y + height - min(0.01 / y_max, 1.0) * height, left + width, top_y + height - min(0.01 / y_max, 1.0) * height, stroke="#808080", width=0.9, dash="3 3")
    target.text(left + width - 2, top_y + height - min(0.01 / y_max, 1.0) * height - 4, "TV = 0.01", size=8, anchor="end", fill="#444444")


def render(rows: list[Row], target, *, title: str, subtitle: str, y_max: float) -> None:
    width = 900
    left1 = 75
    left2 = 540
    top_y = 105
    panel_w = 310
    panel_h = 235

    target.text(width / 2, 32, title, size=18, weight="700", anchor="middle")
    target.text(width / 2, 55, subtitle, size=12, anchor="middle")
    draw_bubble_panel(rows, target, left1, top_y, panel_w, panel_h)
    draw_profile_panel(rows, target, left2, top_y, panel_w, panel_h, y_max=y_max)

    tvs = [row.tv_empirical_theory for row in rows]
    top_matches = sum(row.theory_top == row.empirical_top for row in rows)
    target.text(
        left2,
        top_y + panel_h + 61,
        (
            f"median TV={statistics.median(tvs):.5f}; mean TV={statistics.mean(tvs):.5f}; "
            f"SD TV={statistics.pstdev(tvs):.5f}; top match={top_matches}/{len(rows)}"
        ),
        size=9,
        fill="#333333",
    )


def write_one(rows: list[Row], *, title: str, subtitle: str, output_stem: str, y_max: float, write_svg: bool = False) -> None:
    width = 900
    height = 430
    svg_path = FIGURE_DIR / f"{output_stem}.svg"
    pdf_path = FIGURE_DIR / f"{output_stem}.pdf"

    if write_svg:
        svg = SvgTarget(width, height, title)
        render(rows, svg, title=title, subtitle=subtitle, y_max=y_max)
        svg.finish(svg_path)
        print(f"wrote {svg_path}")

    pdf = PdfTarget(width, height)
    render(rows, pdf, title=title, subtitle=subtitle, y_max=y_max)
    pdf.finish(pdf_path)
    print(f"wrote {pdf_path}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--qwen25-dpo-input", type=Path, default=QWEN25_DPO_INPUT)
    parser.add_argument("--qwen3-dpo-input", type=Path, default=QWEN3_DPO_INPUT)
    parser.add_argument("--nemo-dpo-input", type=Path, default=NEMO_DPO_INPUT)
    parser.add_argument("--nlhf-input", type=Path, default=NLHF_INPUT)
    parser.add_argument("--nemo-nlhf-input", type=Path, default=NEMO_NLHF_INPUT)
    parser.add_argument("--qwen3-nlhf-input", type=Path, default=QWEN3_NLHF_INPUT)
    parser.add_argument("--write-svg", action="store_true")
    parser.add_argument("--right-y-max", type=float, default=1.0)
    args = parser.parse_args()

    qwen25_dpo_rows = load_rows(args.qwen25_dpo_input)
    qwen3_dpo_rows = load_rows(args.qwen3_dpo_input)
    nemo_dpo_rows = load_rows(args.nemo_dpo_input)
    nlhf_rows = load_rows(args.nlhf_input)
    nemo_nlhf_rows = load_rows(args.nemo_nlhf_input)
    qwen3_nlhf_rows = load_rows(args.qwen3_nlhf_input)
    write_one(
        qwen25_dpo_rows,
        title="Qwen2.5 RTBT vs. DPO: theory vs. experiment",
        subtitle=f"{len(qwen25_dpo_rows)} profiles selected for DPO training",
        output_stem="filtered_qwen25_dpo_bubble_agreement",
        y_max=args.right_y_max,
        write_svg=args.write_svg,
    )
    write_one(
        qwen3_dpo_rows,
        title="Qwen3 RTBT vs. DPO: theory vs. experiment",
        subtitle=f"{len(qwen3_dpo_rows)} profiles selected for DPO training",
        output_stem="filtered_qwen3_dpo_bubble_agreement",
        y_max=args.right_y_max,
        write_svg=args.write_svg,
    )
    write_one(
        nemo_dpo_rows,
        title="Mistral-Nemo RTBT vs. DPO: theory vs. experiment",
        subtitle=f"{len(nemo_dpo_rows)} profiles selected for DPO training",
        output_stem="filtered_nemo_dpo_bubble_agreement",
        y_max=args.right_y_max,
        write_svg=args.write_svg,
    )
    write_one(
        nlhf_rows,
        title="Qwen2.5 NLHF vs. Nash-MD: theory vs. experiment",
        subtitle=f"{len(nlhf_rows)} profiles with TV(theory, reference) >= 0.01",
        output_stem="filtered_qwen25_nlhf_bubble_agreement",
        y_max=args.right_y_max,
        write_svg=args.write_svg,
    )
    write_one(
        nemo_nlhf_rows,
        title="Mistral-Nemo NLHF vs. Nash-MD: theory vs. experiment",
        subtitle=f"{len(nemo_nlhf_rows)} profiles with TV(theory, reference) >= 0.01",
        output_stem="filtered_nemo_nlhf_bubble_agreement",
        y_max=args.right_y_max,
        write_svg=args.write_svg,
    )
    write_one(
        qwen3_nlhf_rows,
        title="Qwen3 NLHF vs. Nash-MD: theory vs. experiment",
        subtitle=f"{len(qwen3_nlhf_rows)} profiles with TV(theory, reference) >= 0.01",
        output_stem="filtered_qwen3_nlhf_bubble_agreement",
        y_max=args.right_y_max,
        write_svg=args.write_svg,
    )


if __name__ == "__main__":
    main()
