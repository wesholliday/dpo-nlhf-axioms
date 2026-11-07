#!/usr/bin/env python3
"""Plot theory-vs-empirical RTBT involvement effects for DPO witness runs."""

from __future__ import annotations

import argparse
import csv
import html
import math
import os
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

Path("/tmp/matplotlib-codex").mkdir(parents=True, exist_ok=True)
Path("/tmp/codex-xdg-cache").mkdir(parents=True, exist_ok=True)
os.environ.setdefault("MPLCONFIGDIR", "/tmp/matplotlib-codex")
os.environ.setdefault("XDG_CACHE_HOME", "/tmp/codex-xdg-cache")

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

plt.rcParams["figure.constrained_layout.use"] = False
plt.rcParams["figure.autolayout"] = False


DEFAULT_OUTPUT = Path("paper/figures/rtbt_involvement_single_profile_dpo_agreement.svg")
DEFAULT_PDF_OUTPUT = Path("paper/figures/rtbt_involvement_single_profile_dpo_agreement.pdf")
DEFAULT_OVERLAY_OUTPUT = Path(
    "paper/figures/rtbt_involvement_single_profile_dpo_agreement_overlay.svg"
)
DEFAULT_OVERLAY_PDF_OUTPUT = Path(
    "paper/figures/rtbt_involvement_single_profile_dpo_agreement_overlay.pdf"
)
DEFAULT_PLOT_DATA = Path(
    "paper/figures/rtbt_involvement_single_profile_dpo_agreement_plot_data.csv"
)

DEFAULT_INPUTS = [
    (
        "Qwen2.5",
        Path("results/empirical/dpo_rtbt/involvement_witnesses/qwen25/summary.csv"),
    ),
    (
        "Nemo",
        Path("results/empirical/dpo_rtbt/involvement_witnesses/nemo/summary.csv"),
    ),
    (
        "Qwen3",
        Path("results/empirical/dpo_rtbt/involvement_witnesses/qwen3/summary.csv"),
    ),
]

AXIOM_LABELS = {
    "positive_involvement": "Positive involvement",
    "negative_involvement": "Negative involvement",
}
AXIOM_COLORS = {
    "positive_involvement": "#7f7f7f",
    "negative_involvement": "#7f7f7f",
}
AXIOM_MARKERS = {
    "positive_involvement": "circle",
    "negative_involvement": "diamond",
}
MODEL_COLORS = {
    "Nemo": "#1f77b4",
    "Qwen2.5": "#d62728",
    "Qwen3": "#2ca02c",
}
EMPIRICAL_REPRODUCTION_THRESHOLD = 0.01


@dataclass(frozen=True)
class Point:
    model: str
    axiom: str
    witness_id: str
    prompt_id: str
    block_name: str
    candidate: str
    theory_effect: float
    empirical_effect: float
    abs_effect_error: float
    direction_matches: bool


def parse_input_spec(spec: str) -> tuple[str, Path]:
    if "=" not in spec:
        raise ValueError(f"Input spec must be MODEL=PATH, got {spec!r}")
    model, path = spec.split("=", 1)
    model = model.strip()
    if not model:
        raise ValueError(f"Input spec has empty model label: {spec!r}")
    return model, Path(path)


def load_points(inputs: Iterable[tuple[str, Path]]) -> list[Point]:
    points: list[Point] = []
    for model, path in inputs:
        with path.open() as handle:
            for row in csv.DictReader(handle):
                if not row.get("empirical_effect"):
                    continue
                points.append(
                    Point(
                        model=model,
                        axiom=row["axiom"],
                        witness_id=row["witness_id"],
                        prompt_id=row["prompt_id"],
                        block_name=row["block_name"],
                        candidate=row["candidate"],
                        theory_effect=float(row["theory_effect"]),
                        empirical_effect=float(row["empirical_effect"]),
                        abs_effect_error=float(row["abs_effect_error"]),
                        direction_matches=row["direction_matches"] == "True",
                    )
                )
    if not points:
        raise ValueError("No completed rows found in the supplied summaries")
    return points


def empirically_reproduces(point: Point) -> bool:
    return point.empirical_effect >= EMPIRICAL_REPRODUCTION_THRESHOLD


def write_plot_data(points: list[Point], output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "training_scope",
                "model",
                "axiom",
                "witness_id",
                "prompt_id",
                "block_name",
                "candidate",
                "theory_effect",
                "empirical_effect",
                "abs_effect_error",
                "direction_matches",
                "empirical_ge_0p01",
            ],
        )
        writer.writeheader()
        for point in points:
            writer.writerow(
                {
                    "training_scope": "single_profile",
                    "model": point.model,
                    "axiom": point.axiom,
                    "witness_id": point.witness_id,
                    "prompt_id": point.prompt_id,
                    "block_name": point.block_name,
                    "candidate": point.candidate,
                    "theory_effect": point.theory_effect,
                    "empirical_effect": point.empirical_effect,
                    "abs_effect_error": point.abs_effect_error,
                    "direction_matches": point.direction_matches,
                    "empirical_ge_0p01": empirically_reproduces(point),
                }
            )


def correlation(xs: list[float], ys: list[float]) -> float:
    if len(xs) < 2:
        return float("nan")
    mean_x = statistics.mean(xs)
    mean_y = statistics.mean(ys)
    cov = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    var_x = sum((x - mean_x) ** 2 for x in xs)
    var_y = sum((y - mean_y) ** 2 for y in ys)
    if var_x == 0.0 or var_y == 0.0:
        return float("nan")
    return cov / math.sqrt(var_x * var_y)


def nice_tick_label(value: float) -> str:
    if abs(value) < 1e-12:
        return "0"
    return f"{value:.2g}"


def circle(cx: float, cy: float, radius: float, fill: str, stroke: str) -> str:
    return (
        f'<circle cx="{cx:.2f}" cy="{cy:.2f}" r="{radius:.2f}" '
        f'fill="{fill}" stroke="{stroke}" stroke-width="1.2"/>'
    )


def diamond(cx: float, cy: float, radius: float, fill: str, stroke: str) -> str:
    points = [
        (cx, cy - radius),
        (cx + radius, cy),
        (cx, cy + radius),
        (cx - radius, cy),
    ]
    point_text = " ".join(f"{x:.2f},{y:.2f}" for x, y in points)
    return (
        f'<polygon points="{point_text}" fill="{fill}" stroke="{stroke}" '
        'stroke-width="1.2"/>'
    )


def text(
    x: float,
    y: float,
    content: str,
    *,
    size: int = 12,
    weight: str = "400",
    fill: str = "#000000",
    anchor: str = "start",
) -> str:
    return (
        f'<text x="{x:.2f}" y="{y:.2f}" font-size="{size}" '
        f'font-weight="{weight}" fill="{fill}" text-anchor="{anchor}">'
        f"{html.escape(content)}</text>"
    )


def line(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    *,
    stroke: str = "#000000",
    width: float = 1.0,
    dash: str | None = None,
) -> str:
    dash_attr = "" if dash is None else f' stroke-dasharray="{dash}"'
    return (
        f'<line x1="{x1:.2f}" y1="{y1:.2f}" x2="{x2:.2f}" y2="{y2:.2f}" '
        f'stroke="{stroke}" stroke-width="{width:.2f}"{dash_attr}/>'
    )


def hex_to_rgb(color: str) -> tuple[float, float, float]:
    color = color.lstrip("#")
    return (
        int(color[0:2], 16) / 255.0,
        int(color[2:4], 16) / 255.0,
        int(color[4:6], 16) / 255.0,
    )


def pdf_escape(content: str) -> str:
    return content.replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")


def estimated_text_width(content: str, size: int) -> float:
    return len(content) * size * 0.54


class PdfCanvas:
    """Tiny one-page vector PDF writer for this dependency-free figure."""

    def __init__(self, width: int, height: int) -> None:
        self.width = width
        self.height = height
        self.ops: list[str] = []

    def py(self, y: float) -> float:
        return self.height - y

    def fill_color(self, color: str) -> str:
        r, g, b = hex_to_rgb(color)
        return f"{r:.4f} {g:.4f} {b:.4f} rg"

    def stroke_color(self, color: str) -> str:
        r, g, b = hex_to_rgb(color)
        return f"{r:.4f} {g:.4f} {b:.4f} RG"

    def line(
        self,
        x1: float,
        y1: float,
        x2: float,
        y2: float,
        *,
        stroke: str = "#000000",
        width: float = 1.0,
        dash: str | None = None,
    ) -> None:
        dash_cmd = "[] 0 d" if dash is None else "[5 4] 0 d"
        self.ops.append(
            "q "
            f"{self.stroke_color(stroke)} {width:.2f} w {dash_cmd} "
            f"{x1:.2f} {self.py(y1):.2f} m {x2:.2f} {self.py(y2):.2f} l S Q"
        )

    def rect(
        self,
        x: float,
        y: float,
        w: float,
        h: float,
        *,
        fill: str | None = None,
        stroke: str | None = None,
        width: float = 1.0,
    ) -> None:
        y_pdf = self.py(y + h)
        color_ops = []
        if fill is not None:
            color_ops.append(self.fill_color(fill))
        if stroke is not None:
            color_ops.append(self.stroke_color(stroke))
            color_ops.append(f"{width:.2f} w")
        paint = "B" if fill is not None and stroke is not None else "f" if fill is not None else "S"
        self.ops.append(
            "q "
            + " ".join(color_ops)
            + f" {x:.2f} {y_pdf:.2f} {w:.2f} {h:.2f} re {paint} Q"
        )

    def polygon(
        self,
        points: list[tuple[float, float]],
        *,
        fill: str,
        stroke: str,
        width: float = 1.0,
    ) -> None:
        first_x, first_y = points[0]
        path = [f"{first_x:.2f} {self.py(first_y):.2f} m"]
        for x, y in points[1:]:
            path.append(f"{x:.2f} {self.py(y):.2f} l")
        path.append("h")
        self.ops.append(
            "q "
            f"{self.fill_color(fill)} {self.stroke_color(stroke)} {width:.2f} w "
            + " ".join(path)
            + " B Q"
        )

    def circle(
        self,
        cx: float,
        cy: float,
        radius: float,
        *,
        fill: str,
        stroke: str,
        width: float = 1.0,
    ) -> None:
        # A 24-gon is visually sufficient at this scale and keeps the writer simple.
        points = [
            (
                cx + math.cos(2.0 * math.pi * index / 24.0) * radius,
                cy + math.sin(2.0 * math.pi * index / 24.0) * radius,
            )
            for index in range(24)
        ]
        self.polygon(points, fill=fill, stroke=stroke, width=width)

    def text(
        self,
        x: float,
        y: float,
        content: str,
        *,
        size: int = 12,
        fill: str = "#000000",
        anchor: str = "start",
    ) -> None:
        if anchor == "middle":
            x -= estimated_text_width(content, size) / 2.0
        elif anchor == "end":
            x -= estimated_text_width(content, size)
        self.ops.append(
            "q "
            f"BT /F1 {size} Tf {self.fill_color(fill)} "
            f"1 0 0 1 {x:.2f} {self.py(y):.2f} Tm "
            f"({pdf_escape(content)}) Tj ET Q"
        )

    def rotated_text(
        self,
        x: float,
        y: float,
        content: str,
        *,
        size: int = 12,
        fill: str = "#000000",
        anchor: str = "middle",
    ) -> None:
        y_pdf = self.py(y)
        offset = 0.0
        if anchor == "middle":
            offset = -estimated_text_width(content, size) / 2.0
        elif anchor == "end":
            offset = -estimated_text_width(content, size)
        self.ops.append(
            "q "
            f"BT /F1 {size} Tf {self.fill_color(fill)} "
            f"0 1 -1 0 {x:.2f} {y_pdf + offset:.2f} Tm "
            f"({pdf_escape(content)}) Tj ET Q"
        )

    def save(self, output: Path) -> None:
        stream = "\n".join(self.ops).encode("latin-1")
        objects = [
            b"<< /Type /Catalog /Pages 2 0 R >>",
            b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
            (
                f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {self.width} {self.height}] "
                "/Resources << /Font << /F1 5 0 R >> >> /Contents 4 0 R >>"
            ).encode("latin-1"),
            b"<< /Length " + str(len(stream)).encode("ascii") + b" >>\nstream\n" + stream + b"\nendstream",
            b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
        ]
        payload = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
        offsets = [0]
        for index, obj in enumerate(objects, start=1):
            offsets.append(len(payload))
            payload.extend(f"{index} 0 obj\n".encode("ascii"))
            payload.extend(obj)
            payload.extend(b"\nendobj\n")
        xref_offset = len(payload)
        payload.extend(f"xref\n0 {len(objects) + 1}\n".encode("ascii"))
        payload.extend(b"0000000000 65535 f \n")
        for offset in offsets[1:]:
            payload.extend(f"{offset:010d} 00000 n \n".encode("ascii"))
        payload.extend(
            (
                f"trailer\n<< /Size {len(objects) + 1} /Root 1 0 R >>\n"
                f"startxref\n{xref_offset}\n%%EOF\n"
            ).encode("ascii")
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(payload)


def render_pdf(points: list[Point], output: Path) -> None:
    models = [model for model, _ in DEFAULT_INPUTS if any(p.model == model for p in points)]
    for point in points:
        if point.model not in models:
            models.append(point.model)

    min_value = min(0.0, *(p.theory_effect for p in points), *(p.empirical_effect for p in points))
    max_value = max(*(p.theory_effect for p in points), *(p.empirical_effect for p in points))
    axis_min = min(-0.08, math.floor((min_value - 0.03) * 20.0) / 20.0)
    axis_max = max(1.0, math.ceil((max_value + 0.03) * 20.0) / 20.0)
    ticks = [0.0, 0.25, 0.5, 0.75, 1.0]
    ticks = [tick for tick in ticks if axis_min <= tick <= axis_max]
    if axis_min < 0.0:
        ticks = [axis_min] + ticks

    panel_size = 245
    gap = 48
    left = 78
    top = 105
    bottom = 98
    right = 34
    width = left + len(models) * panel_size + (len(models) - 1) * gap + right
    height = top + panel_size + bottom
    panel_bottom = top + panel_size

    def sx(model_index: int, value: float) -> float:
        panel_left = left + model_index * (panel_size + gap)
        return panel_left + (value - axis_min) / (axis_max - axis_min) * panel_size

    def sy(value: float) -> float:
        return panel_bottom - (value - axis_min) / (axis_max - axis_min) * panel_size

    canvas = PdfCanvas(width, height)
    canvas.rect(0, 0, width, height, fill="#ffffff")
    canvas.text(
        width / 2,
        34,
        "RTBT vs. DPO: involvement violations",
        size=20,
        fill="#000000",
        anchor="middle",
    )
    for model_index, model in enumerate(models):
        panel_left = left + model_index * (panel_size + gap)
        model_points = [point for point in points if point.model == model]
        xs = [p.theory_effect for p in model_points]
        ys = [p.empirical_effect for p in model_points]
        matches = sum(empirically_reproduces(p) for p in model_points)
        abs_errors = [p.abs_effect_error for p in model_points]
        mae = statistics.mean(abs_errors)
        sd_abs_error = statistics.pstdev(abs_errors)
        corr = correlation(xs, ys)

        canvas.rect(panel_left, top, panel_size, panel_size, fill="#ffffff", stroke="#000000", width=0.8)
        for tick in ticks:
            x = sx(model_index, tick)
            y = sy(tick)
            canvas.line(x, top, x, panel_bottom, stroke="#b0b0b0", width=0.8)
            canvas.line(panel_left, y, panel_left + panel_size, y, stroke="#b0b0b0", width=0.8)
            canvas.line(x, panel_bottom, x, panel_bottom + 5, stroke="#000000")
            canvas.line(panel_left - 5, y, panel_left, y, stroke="#000000")
            canvas.text(x, panel_bottom + 20, nice_tick_label(tick), size=10, fill="#000000", anchor="middle")
            if model_index == 0:
                canvas.text(panel_left - 10, y + 4, nice_tick_label(tick), size=10, fill="#000000", anchor="end")

        canvas.line(panel_left, panel_bottom, panel_left + panel_size, panel_bottom, stroke="#000000", width=1.2)
        canvas.line(panel_left, top, panel_left, panel_bottom, stroke="#000000", width=1.2)
        canvas.line(
            sx(model_index, axis_min),
            sy(axis_min),
            sx(model_index, axis_max),
            sy(axis_max),
            stroke="#808080",
            width=1.4,
            dash="5 4",
        )
        if axis_min < 0.0:
            canvas.line(sx(model_index, 0.0), top, sx(model_index, 0.0), panel_bottom, stroke="#b0b0b0")
            canvas.line(panel_left, sy(0.0), panel_left + panel_size, sy(0.0), stroke="#b0b0b0")

        canvas.text(panel_left, top - 36, model, size=15, fill="#000000")
        canvas.text(
            panel_left,
            top - 16,
            f"{matches}/{len(model_points)} empirical >= 0.01",
            size=11,
            fill="#000000",
        )
        canvas.text(
            panel_left,
            top - 3,
            f"r={corr:.3f}; MAE={mae:.3f}; SD|err|={sd_abs_error:.3f}",
            size=11,
            fill="#000000",
        )

        for point in model_points:
            x = sx(model_index, point.theory_effect)
            y = sy(point.empirical_effect)
            color = MODEL_COLORS.get(point.model, "#7f7f7f")
            reproduces = empirically_reproduces(point)
            stroke = "#000000" if reproduces else "#d62728"
            fill = color if reproduces else "#ffffff"
            radius = 5.0 if reproduces else 6.4
            if AXIOM_MARKERS.get(point.axiom, "circle") == "diamond":
                canvas.polygon(
                    [(x, y - radius), (x + radius, y), (x, y + radius), (x - radius, y)],
                    fill=fill,
                    stroke=stroke,
                    width=1.2,
                )
            else:
                canvas.circle(x, y, radius, fill=fill, stroke=stroke, width=1.2)
            if not reproduces:
                canvas.line(x - 4.5, y - 4.5, x + 4.5, y + 4.5, stroke="#d62728", width=1.3)
                canvas.line(x - 4.5, y + 4.5, x + 4.5, y - 4.5, stroke="#d62728", width=1.3)

    canvas.text(
        left + (len(models) * panel_size + (len(models) - 1) * gap) / 2,
        height - 42,
        "RTBT-predicted violation magnitude",
        size=13,
        fill="#000000",
        anchor="middle",
    )
    canvas.rotated_text(24, top + panel_size / 2, "DPO-trained violation magnitude", size=13, fill="#000000")

    legend_y = height - 16
    legend_x = left
    canvas.circle(legend_x, legend_y - 4, 5.0, fill=AXIOM_COLORS["positive_involvement"], stroke="#000000")
    canvas.text(legend_x + 13, legend_y, AXIOM_LABELS["positive_involvement"], size=11, fill="#000000")
    legend_x += 180
    canvas.polygon(
        [
            (legend_x, legend_y - 9),
            (legend_x + 5, legend_y - 4),
            (legend_x, legend_y + 1),
            (legend_x - 5, legend_y - 4),
        ],
        fill=AXIOM_COLORS["negative_involvement"],
        stroke="#000000",
    )
    canvas.text(legend_x + 13, legend_y, AXIOM_LABELS["negative_involvement"], size=11, fill="#000000")
    legend_x += 190
    canvas.circle(legend_x, legend_y - 4, 6.2, fill="#ffffff", stroke="#d62728")
    canvas.line(legend_x - 4.5, legend_y - 8.5, legend_x + 4.5, legend_y + 0.5, stroke="#d62728", width=1.3)
    canvas.line(legend_x - 4.5, legend_y + 0.5, legend_x + 4.5, legend_y - 8.5, stroke="#d62728", width=1.3)
    canvas.text(legend_x + 13, legend_y, "Empirical < 0.01", size=11, fill="#000000")

    canvas.save(output)


def render_matplotlib(points: list[Point], svg_output: Path, pdf_output: Path | None) -> None:
    models = [model for model, _ in DEFAULT_INPUTS if any(p.model == model for p in points)]
    for point in points:
        if point.model not in models:
            models.append(point.model)

    # Match the canvas and panel geometry of the Nash-MD commutativity figure.
    canvas_width = 943
    canvas_height = 448
    panel_size = 245
    gap = 48
    left = 78
    right = 34
    top_margin = 105
    bottom_margin = 98
    fig, axes = plt.subplots(
        1,
        len(models),
        figsize=(canvas_width / 72.0, canvas_height / 72.0),
        constrained_layout=False,
    )
    fig.set_layout_engine(None)
    if len(models) == 1:
        axes = [axes]

    # Failed reproduction can have a negative signed effect. Keep the entire
    # range visible instead of clipping substantial effects below -0.1.
    minimum = min(min(p.theory_effect,p.empirical_effect) for p in points)
    axis_min = min(-0.1, math.floor((minimum-0.03)*20)/20)
    axis_max = max(1.05, max(max(p.theory_effect,p.empirical_effect) for p in points)+0.03)
    ticks = [t for t in [-1.,-.75,-.5,-.25,-.1,0.,.25,.5,.75,1.] if axis_min<=t<=axis_max]
    for ax_index, (ax, model) in enumerate(zip(axes, models)):
        model_points = [point for point in points if point.model == model]
        ax.plot([axis_min, axis_max], [axis_min, axis_max], color="#808080", linestyle="--", linewidth=1.1)
        for point in model_points:
            reproduces_violation = empirically_reproduces(point)
            color = MODEL_COLORS.get(point.model, "#7f7f7f")
            marker = "D" if AXIOM_MARKERS.get(point.axiom, "circle") == "diamond" else "o"
            ax.scatter(
                [point.theory_effect],
                [point.empirical_effect],
                marker=marker,
                s=50 if reproduces_violation else 66,
                facecolor=color if reproduces_violation else "#ffffff",
                edgecolor="#000000" if reproduces_violation else "#d62728",
                linewidth=0.65 if reproduces_violation else 1.1,
                alpha=0.82 if reproduces_violation else 1.0,
                zorder=3,
            )
            if not reproduces_violation:
                x = point.theory_effect
                y = point.empirical_effect
                ax.plot([x - 0.018, x + 0.018], [y - 0.018, y + 0.018], color="#d62728", linewidth=1.1, zorder=4)
                ax.plot([x - 0.018, x + 0.018], [y + 0.018, y - 0.018], color="#d62728", linewidth=1.1, zorder=4)

        ax.set_xlim(axis_min, axis_max)
        ax.set_ylim(axis_min, axis_max)
        ax.set_xticks(ticks)
        ax.set_yticks(ticks)
        ax.set_xticklabels([nice_tick_label(tick) for tick in ticks])
        ax.set_yticklabels([nice_tick_label(tick) for tick in ticks])
        ax.set_aspect("equal", adjustable="box")
        ax.grid(True, color="#d9d9d9", linewidth=0.8, alpha=0.65)
        ax.set_title(model, fontsize=15, loc="left", pad=36)
        xs = [point.theory_effect for point in model_points]
        ys = [point.empirical_effect for point in model_points]
        matches = sum(empirically_reproduces(point) for point in model_points)
        abs_errors = [point.abs_effect_error for point in model_points]
        mae = statistics.mean(abs_errors)
        sd_abs_error = statistics.pstdev(abs_errors)
        corr = correlation(xs, ys)
        ax.text(
            0.0,
            1.04,
            (
                f"{matches}/{len(model_points)} empirical >= 0.01\n"
                f"r={corr:.3f}; MAE={mae:.3f}; SD|err|={sd_abs_error:.3f}"
            ),
            transform=ax.transAxes,
            fontsize=11,
            ha="left",
            va="bottom",
        )
        ax.set_xlabel("RTBT-predicted violation magnitude", fontsize=13, labelpad=10)
        if ax_index == 0:
            ax.set_ylabel("DPO-trained violation magnitude", fontsize=13, labelpad=10)
        else:
            ax.set_ylabel("")
        ax.tick_params(labelsize=10)

    legend_handles = [
        Line2D([0], [0], marker="o", color="none", label=AXIOM_LABELS["positive_involvement"], markerfacecolor="#7f7f7f", markeredgecolor="#000000", markersize=7),
        Line2D([0], [0], marker="D", color="none", label=AXIOM_LABELS["negative_involvement"], markerfacecolor="#7f7f7f", markeredgecolor="#000000", markersize=7),
        Line2D([0], [0], marker="o", color="#d62728", label="Empirical < 0.01", markerfacecolor="#ffffff", markeredgecolor="#d62728", markersize=8, linestyle="None"),
    ]
    fig.legend(handles=legend_handles, loc="lower left", bbox_to_anchor=(left / canvas_width, 0.02), ncol=3, frameon=False, fontsize=11)
    fig.suptitle("RTBT vs. DPO: involvement violations", fontsize=20, y=1.0 - 34 / canvas_height)
    fig.subplots_adjust(
        left=left / canvas_width,
        right=(canvas_width - right) / canvas_width,
        top=(canvas_height - top_margin) / canvas_height,
        bottom=bottom_margin / canvas_height,
        wspace=gap / panel_size,
    )

    svg_output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(svg_output)
    if pdf_output is not None:
        pdf_output.parent.mkdir(parents=True, exist_ok=True)
        fig.savefig(pdf_output)
    plt.close(fig)


def render_svg(points: list[Point], output: Path) -> None:
    models = [model for model, _ in DEFAULT_INPUTS if any(p.model == model for p in points)]
    for point in points:
        if point.model not in models:
            models.append(point.model)

    min_value = min(0.0, *(p.theory_effect for p in points), *(p.empirical_effect for p in points))
    max_value = max(*(p.theory_effect for p in points), *(p.empirical_effect for p in points))
    axis_min = min(-0.08, math.floor((min_value - 0.03) * 20.0) / 20.0)
    axis_max = max(1.0, math.ceil((max_value + 0.03) * 20.0) / 20.0)
    ticks = [0.0, 0.25, 0.5, 0.75, 1.0]
    ticks = [tick for tick in ticks if axis_min <= tick <= axis_max]
    if axis_min < 0.0:
        ticks = [axis_min] + ticks

    panel_size = 245
    gap = 48
    left = 78
    top = 105
    bottom = 98
    right = 34
    width = left + len(models) * panel_size + (len(models) - 1) * gap + right
    height = top + panel_size + bottom
    panel_bottom = top + panel_size

    def sx(model_index: int, value: float) -> float:
        panel_left = left + model_index * (panel_size + gap)
        return panel_left + (value - axis_min) / (axis_max - axis_min) * panel_size

    def sy(value: float) -> float:
        return panel_bottom - (value - axis_min) / (axis_max - axis_min) * panel_size

    parts: list[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}" role="img">',
        "<title>Single-profile DPO agreement with RTBT theory</title>",
        "<desc>Theory-predicted versus empirical violation magnitudes for thresholded RTBT involvement witnesses.</desc>",
        f'<rect width="{width}" height="{height}" fill="#ffffff"/>',
        '<style>text{font-family:DejaVu Sans, Helvetica, Arial, sans-serif;} '
        '.axis{stroke:#000000}.grid{stroke:#b0b0b0}.panel{fill:#ffffff;stroke:#000000}</style>',
    ]

    parts.append(
        text(
            width / 2,
            34,
            "RTBT vs. DPO: involvement violations",
            size=20,
            weight="700",
            fill="#000000",
            anchor="middle",
        )
    )
    for model_index, model in enumerate(models):
        panel_left = left + model_index * (panel_size + gap)
        model_points = [point for point in points if point.model == model]
        xs = [p.theory_effect for p in model_points]
        ys = [p.empirical_effect for p in model_points]
        matches = sum(empirically_reproduces(p) for p in model_points)
        abs_errors = [p.abs_effect_error for p in model_points]
        mae = statistics.mean(abs_errors)
        sd_abs_error = statistics.pstdev(abs_errors)
        corr = correlation(xs, ys)

        parts.append(
            f'<rect x="{panel_left:.2f}" y="{top:.2f}" width="{panel_size}" '
            f'height="{panel_size}" class="panel"/>'
        )
        for tick in ticks:
            x = sx(model_index, tick)
            y = sy(tick)
            parts.append(line(x, top, x, panel_bottom, stroke="#b0b0b0", width=0.8))
            parts.append(line(panel_left, y, panel_left + panel_size, y, stroke="#b0b0b0", width=0.8))
            parts.append(line(x, panel_bottom, x, panel_bottom + 5, stroke="#000000", width=1.0))
            parts.append(line(panel_left - 5, y, panel_left, y, stroke="#000000", width=1.0))
            parts.append(text(x, panel_bottom + 20, nice_tick_label(tick), size=10, fill="#000000", anchor="middle"))
            if model_index == 0:
                parts.append(text(panel_left - 10, y + 4, nice_tick_label(tick), size=10, fill="#000000", anchor="end"))

        parts.append(line(panel_left, panel_bottom, panel_left + panel_size, panel_bottom, stroke="#000000", width=1.2))
        parts.append(line(panel_left, top, panel_left, panel_bottom, stroke="#000000", width=1.2))
        parts.append(
            line(
                sx(model_index, axis_min),
                sy(axis_min),
                sx(model_index, axis_max),
                sy(axis_max),
                stroke="#808080",
                width=1.4,
                dash="5 4",
            )
        )
        if axis_min < 0.0:
            parts.append(line(sx(model_index, 0.0), top, sx(model_index, 0.0), panel_bottom, stroke="#b0b0b0", width=1.0))
            parts.append(line(panel_left, sy(0.0), panel_left + panel_size, sy(0.0), stroke="#b0b0b0", width=1.0))

        parts.append(text(panel_left, top - 36, model, size=15, weight="700", fill="#000000"))
        parts.append(
            text(
                panel_left,
                top - 16,
                f"{matches}/{len(model_points)} empirical >= 0.01",
                size=11,
                fill="#000000",
            )
        )
        parts.append(
            text(
                panel_left,
                top - 3,
                f"r={corr:.3f}; MAE={mae:.3f}; SD|err|={sd_abs_error:.3f}",
                size=11,
                fill="#000000",
            )
        )

        for point in model_points:
            x = sx(model_index, point.theory_effect)
            y = sy(point.empirical_effect)
            color = MODEL_COLORS.get(point.model, "#7f7f7f")
            reproduces = empirically_reproduces(point)
            stroke = "#000000" if reproduces else "#d62728"
            fill = color if reproduces else "#ffffff"
            radius = 5.0 if reproduces else 6.4
            marker = AXIOM_MARKERS.get(point.axiom, "circle")
            if marker == "diamond":
                parts.append(diamond(x, y, radius, fill, stroke))
            else:
                parts.append(circle(x, y, radius, fill, stroke))
            if not reproduces:
                parts.append(line(x - 4.5, y - 4.5, x + 4.5, y + 4.5, stroke="#d62728", width=1.3))
                parts.append(line(x - 4.5, y + 4.5, x + 4.5, y - 4.5, stroke="#d62728", width=1.3))

    parts.append(
        text(
            left + (len(models) * panel_size + (len(models) - 1) * gap) / 2,
            height - 42,
            "RTBT-predicted violation magnitude",
            size=13,
            weight="600",
            fill="#000000",
            anchor="middle",
        )
    )
    parts.append(
        f'<g transform="translate(24 {top + panel_size / 2:.2f}) rotate(-90)">'
        + text(0, 0, "DPO-trained violation magnitude", size=13, weight="600", fill="#000000", anchor="middle")
        + "</g>"
    )

    legend_y = height - 16
    legend_x = left
    parts.append(circle(legend_x, legend_y - 4, 5.0, AXIOM_COLORS["positive_involvement"], "#000000"))
    parts.append(text(legend_x + 13, legend_y, AXIOM_LABELS["positive_involvement"], size=11, fill="#000000"))
    legend_x += 180
    parts.append(diamond(legend_x, legend_y - 4, 5.0, AXIOM_COLORS["negative_involvement"], "#000000"))
    parts.append(text(legend_x + 13, legend_y, AXIOM_LABELS["negative_involvement"], size=11, fill="#000000"))
    legend_x += 190
    parts.append(circle(legend_x, legend_y - 4, 6.2, "#ffffff", "#d62728"))
    parts.append(line(legend_x - 4.5, legend_y - 8.5, legend_x + 4.5, legend_y + 0.5, stroke="#d62728", width=1.3))
    parts.append(line(legend_x - 4.5, legend_y + 0.5, legend_x + 4.5, legend_y - 8.5, stroke="#d62728", width=1.3))
    parts.append(text(legend_x + 13, legend_y, "Empirical < 0.01", size=11, fill="#000000"))

    parts.append("</svg>")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(parts) + "\n")


def render_overlay_pdf(points: list[Point], output: Path) -> None:
    models = [model for model, _ in DEFAULT_INPUTS if any(p.model == model for p in points)]
    for point in points:
        if point.model not in models:
            models.append(point.model)

    min_value = min(0.0, *(p.theory_effect for p in points), *(p.empirical_effect for p in points))
    max_value = max(*(p.theory_effect for p in points), *(p.empirical_effect for p in points))
    axis_min = min(-0.08, math.floor((min_value - 0.03) * 20.0) / 20.0)
    axis_max = max(1.0, math.ceil((max_value + 0.03) * 20.0) / 20.0)
    ticks = [axis_min] + [tick for tick in [0.0, 0.25, 0.5, 0.75, 1.0] if axis_min <= tick <= axis_max]

    width = 510
    height = 455
    left = 78
    top = 74
    panel = 285
    bottom = top + panel
    canvas = PdfCanvas(width, height)
    canvas.rect(0, 0, width, height, fill="#ffffff")
    canvas.text(width / 2, 30, "Single-profile DPO agreement by model", size=16, anchor="middle")
    canvas.text(width / 2, 52, "RTBT involvement witnesses", size=11, anchor="middle")
    canvas.rect(left, top, panel, panel, fill="#ffffff", stroke="#000000", width=0.8)

    def sx(value: float) -> float:
        return left + (value - axis_min) / (axis_max - axis_min) * panel

    def sy(value: float) -> float:
        return bottom - (value - axis_min) / (axis_max - axis_min) * panel

    for tick in ticks:
        x = sx(tick)
        y = sy(tick)
        canvas.line(x, top, x, bottom, stroke="#b0b0b0", width=0.8)
        canvas.line(left, y, left + panel, y, stroke="#b0b0b0", width=0.8)
        canvas.line(x, bottom, x, bottom + 5, stroke="#000000")
        canvas.line(left - 5, y, left, y, stroke="#000000")
        canvas.text(x, bottom + 19, nice_tick_label(tick), size=10, anchor="middle")
        canvas.text(left - 10, y + 4, nice_tick_label(tick), size=10, anchor="end")
    canvas.line(left, bottom, left + panel, bottom, stroke="#000000", width=1.2)
    canvas.line(left, top, left, bottom, stroke="#000000", width=1.2)
    canvas.line(sx(axis_min), sy(axis_min), sx(axis_max), sy(axis_max), stroke="#808080", width=1.3, dash="5 4")

    for point in points:
        x = sx(point.theory_effect)
        y = sy(point.empirical_effect)
        reproduces = empirically_reproduces(point)
        fill = MODEL_COLORS.get(point.model, "#7f7f7f") if reproduces else "#ffffff"
        stroke = "#000000" if reproduces else "#d62728"
        radius = 4.5 if reproduces else 5.8
        if AXIOM_MARKERS.get(point.axiom) == "diamond":
            canvas.polygon([(x, y - radius), (x + radius, y), (x, y + radius), (x - radius, y)], fill=fill, stroke=stroke, width=1.0)
        else:
            canvas.circle(x, y, radius, fill=fill, stroke=stroke, width=1.0)
        if not reproduces:
            canvas.line(x - 4.2, y - 4.2, x + 4.2, y + 4.2, stroke="#d62728", width=1.2)
            canvas.line(x - 4.2, y + 4.2, x + 4.2, y - 4.2, stroke="#d62728", width=1.2)

    canvas.text(left + panel / 2, height - 54, "RTBT-predicted violation magnitude", size=12, anchor="middle")
    canvas.rotated_text(24, top + panel / 2, "DPO-trained violation magnitude", size=12, anchor="middle")

    legend_x = left
    legend_y = height - 24
    for model in models:
        canvas.circle(legend_x, legend_y - 4, 4.5, fill=MODEL_COLORS.get(model, "#7f7f7f"), stroke="#000000")
        canvas.text(legend_x + 10, legend_y, model, size=10)
        legend_x += 88
    canvas.polygon([(legend_x, legend_y - 9), (legend_x + 5, legend_y - 4), (legend_x, legend_y + 1), (legend_x - 5, legend_y - 4)], fill="#ffffff", stroke="#000000")
    canvas.text(legend_x + 10, legend_y, "negative involvement", size=10)
    canvas.save(output)


def render_overlay_svg(points: list[Point], output: Path) -> None:
    models = [model for model, _ in DEFAULT_INPUTS if any(p.model == model for p in points)]
    for point in points:
        if point.model not in models:
            models.append(point.model)

    min_value = min(0.0, *(p.theory_effect for p in points), *(p.empirical_effect for p in points))
    max_value = max(*(p.theory_effect for p in points), *(p.empirical_effect for p in points))
    axis_min = min(-0.08, math.floor((min_value - 0.03) * 20.0) / 20.0)
    axis_max = max(1.0, math.ceil((max_value + 0.03) * 20.0) / 20.0)
    ticks = [axis_min] + [tick for tick in [0.0, 0.25, 0.5, 0.75, 1.0] if axis_min <= tick <= axis_max]

    width = 510
    height = 455
    left = 78
    top = 74
    panel = 285
    bottom = top + panel

    def sx(value: float) -> float:
        return left + (value - axis_min) / (axis_max - axis_min) * panel

    def sy(value: float) -> float:
        return bottom - (value - axis_min) / (axis_max - axis_min) * panel

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img">',
        "<title>Single-profile DPO agreement by model</title>",
        "<style>text{font-family:DejaVu Sans, Helvetica, Arial, sans-serif;}</style>",
        f'<rect width="{width}" height="{height}" fill="#ffffff"/>',
        text(width / 2, 30, "Single-profile DPO agreement by model", size=16, weight="700", anchor="middle"),
        text(width / 2, 52, "RTBT involvement witnesses", size=11, anchor="middle"),
        f'<rect x="{left}" y="{top}" width="{panel}" height="{panel}" fill="#ffffff" stroke="#000000" stroke-width="0.8"/>',
    ]
    for tick in ticks:
        x = sx(tick)
        y = sy(tick)
        parts.append(line(x, top, x, bottom, stroke="#b0b0b0", width=0.8))
        parts.append(line(left, y, left + panel, y, stroke="#b0b0b0", width=0.8))
        parts.append(line(x, bottom, x, bottom + 5, stroke="#000000"))
        parts.append(line(left - 5, y, left, y, stroke="#000000"))
        parts.append(text(x, bottom + 19, nice_tick_label(tick), size=10, anchor="middle"))
        parts.append(text(left - 10, y + 4, nice_tick_label(tick), size=10, anchor="end"))
    parts.append(line(left, bottom, left + panel, bottom, stroke="#000000", width=1.2))
    parts.append(line(left, top, left, bottom, stroke="#000000", width=1.2))
    parts.append(line(sx(axis_min), sy(axis_min), sx(axis_max), sy(axis_max), stroke="#808080", width=1.3, dash="5 4"))

    for point in points:
        x = sx(point.theory_effect)
        y = sy(point.empirical_effect)
        reproduces = empirically_reproduces(point)
        fill = MODEL_COLORS.get(point.model, "#7f7f7f") if reproduces else "#ffffff"
        stroke = "#000000" if reproduces else "#d62728"
        radius = 4.5 if reproduces else 5.8
        if AXIOM_MARKERS.get(point.axiom) == "diamond":
            parts.append(diamond(x, y, radius, fill, stroke))
        else:
            parts.append(circle(x, y, radius, fill, stroke))
        if not reproduces:
            parts.append(line(x - 4.2, y - 4.2, x + 4.2, y + 4.2, stroke="#d62728", width=1.2))
            parts.append(line(x - 4.2, y + 4.2, x + 4.2, y - 4.2, stroke="#d62728", width=1.2))

    parts.append(text(left + panel / 2, height - 54, "RTBT-predicted violation magnitude", size=12, anchor="middle"))
    parts.append(f'<g transform="translate(24 {top + panel / 2:.2f}) rotate(-90)">' + text(0, 0, "DPO-trained violation magnitude", size=12, anchor="middle") + "</g>")

    legend_x = left
    legend_y = height - 24
    for model in models:
        parts.append(circle(legend_x, legend_y - 4, 4.5, MODEL_COLORS.get(model, "#7f7f7f"), "#000000"))
        parts.append(text(legend_x + 10, legend_y, model, size=10))
        legend_x += 88
    parts.append(diamond(legend_x, legend_y - 4, 5.0, "#ffffff", "#000000"))
    parts.append(text(legend_x + 10, legend_y, "negative involvement", size=10))
    parts.append("</svg>")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(parts) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--input",
        action="append",
        default=[],
        help="Summary CSV input as MODEL=PATH. Can be repeated.",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--pdf-output", type=Path, default=DEFAULT_PDF_OUTPUT)
    parser.add_argument("--overlay-output", type=Path, default=DEFAULT_OVERLAY_OUTPUT)
    parser.add_argument("--overlay-pdf-output", type=Path, default=DEFAULT_OVERLAY_PDF_OUTPUT)
    parser.add_argument("--no-pdf", action="store_true")
    parser.add_argument("--no-overlay", action="store_true")
    parser.add_argument("--plot-data-output", type=Path, default=DEFAULT_PLOT_DATA)
    args = parser.parse_args()

    inputs = [parse_input_spec(spec) for spec in args.input] if args.input else DEFAULT_INPUTS
    points = load_points(inputs)
    write_plot_data(points, args.plot_data_output)
    render_matplotlib(points, args.output, None if args.no_pdf else args.pdf_output)
    if not args.no_overlay:
        render_overlay_svg(points, args.overlay_output)
        if not args.no_pdf:
            render_overlay_pdf(points, args.overlay_pdf_output)
    print(f"wrote {args.output}")
    if not args.no_pdf:
        print(f"wrote {args.pdf_output}")
    if not args.no_overlay:
        print(f"wrote {args.overlay_output}")
        if not args.no_pdf:
            print(f"wrote {args.overlay_pdf_output}")
    print(f"wrote {args.plot_data_output}")


if __name__ == "__main__":
    main()
