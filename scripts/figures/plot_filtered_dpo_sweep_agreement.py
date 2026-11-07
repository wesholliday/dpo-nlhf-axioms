#!/usr/bin/env python3
"""Plot empirical-vs-theory agreement for the filtered Qwen DPO sweep.

The figure summarizes the 154 single-profile trainings whose theoretical RTBT
updates move the Qwen2.5 reference distribution by at least 0.01 in TV.
It writes dependency-free PDF/SVG output so it can run in the MPS environment.
"""

from __future__ import annotations

import argparse
import csv
import html
import json
import math
import statistics
from dataclasses import dataclass
from pathlib import Path


DEFAULT_INPUT = Path("results/empirical/dpo_rtbt/filtered_profile_sweeps/qwen25.jsonl")
DEFAULT_OUTPUT = Path("paper/figures/filtered_qwen_dpo_sweep_agreement.svg")
DEFAULT_PDF_OUTPUT = Path("paper/figures/filtered_qwen_dpo_sweep_agreement.pdf")
DEFAULT_PLOT_DATA = Path("paper/figures/filtered_qwen_dpo_sweep_agreement_plot_data.csv")

LABELS = ("A", "B", "C", "D")
QWEN25_COLOR = "#d62728"
LABEL_COLORS = {
    "A": "#1f77b4",
    "B": "#ff7f0e",
    "C": "#2ca02c",
    "D": "#d62728",
}


@dataclass(frozen=True)
class ProfileRow:
    case_key: str
    prompt_id: str
    block_name: str
    tv_theory_to_reference: float
    tv_empirical_to_theory: float
    tv_empirical_to_reference: float
    max_abs_error: float
    reference_top: str
    theory_top: str
    final_top: str
    reference_probs: dict[str, float]
    theoretical_probs: dict[str, float]
    final_probs: dict[str, float]


def tv_distance(left: dict[str, float], right: dict[str, float]) -> float:
    return 0.5 * sum(abs(float(left[label]) - float(right[label])) for label in LABELS)


def top_label(probs: dict[str, float]) -> str:
    return max(LABELS, key=lambda label: float(probs[label]))


def load_rows(path: Path) -> list[ProfileRow]:
    rows: list[ProfileRow] = []
    with path.open() as handle:
        for line in handle:
            if not line.strip():
                continue
            row = json.loads(line)
            if not row.get("theory_available", False):
                continue
            reference = {label: float(row["reference_probs"][label]) for label in LABELS}
            theory = {label: float(row["theoretical_probs"][label]) for label in LABELS}
            final = {label: float(row["final_probs"][label]) for label in LABELS}
            rows.append(
                ProfileRow(
                    case_key=row["case_key"],
                    prompt_id=row["prompt_id"],
                    block_name=row["block_name"],
                    tv_theory_to_reference=tv_distance(theory, reference),
                    tv_empirical_to_theory=float(row["tv_to_theory"]),
                    tv_empirical_to_reference=tv_distance(final, reference),
                    max_abs_error=float(row["max_abs_error"]),
                    reference_top=top_label(reference),
                    theory_top=top_label(theory),
                    final_top=top_label(final),
                    reference_probs=reference,
                    theoretical_probs=theory,
                    final_probs=final,
                )
            )
    if not rows:
        raise ValueError(f"No usable rows found in {path}")
    return rows


def write_plot_data(rows: list[ProfileRow], output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "training_scope",
                "model",
                "case_key",
                "prompt_id",
                "block_name",
                "candidate",
                "reference_prob",
                "theory_prob",
                "empirical_prob",
                "tv_theory_to_reference",
                "tv_empirical_to_reference",
                "tv_empirical_to_theory",
                "max_abs_error",
                "reference_top",
                "theory_top",
                "final_top",
                "top_theory_matches_final",
            ],
        )
        writer.writeheader()
        for row in rows:
            for label in LABELS:
                writer.writerow(
                    {
                        "training_scope": "single_profile",
                        "model": "Qwen2.5",
                        "case_key": row.case_key,
                        "prompt_id": row.prompt_id,
                        "block_name": row.block_name,
                        "candidate": label,
                        "reference_prob": row.reference_probs[label],
                        "theory_prob": row.theoretical_probs[label],
                        "empirical_prob": row.final_probs[label],
                        "tv_theory_to_reference": row.tv_theory_to_reference,
                        "tv_empirical_to_reference": row.tv_empirical_to_reference,
                        "tv_empirical_to_theory": row.tv_empirical_to_theory,
                        "max_abs_error": row.max_abs_error,
                        "reference_top": row.reference_top,
                        "theory_top": row.theory_top,
                        "final_top": row.final_top,
                        "top_theory_matches_final": row.theory_top == row.final_top,
                    }
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


def estimated_text_width(content: str, size: float) -> float:
    return len(content) * size * 0.54


def formula_tokens(kind: str, size: int = 12) -> list[dict[str, str | float]]:
    rho = {"kind": "rho", "size": float(size)}
    prime = {"kind": "prime", "size": float(size)}
    sub_size = float(size) * 0.70

    def text_token(value: str) -> dict[str, str | float]:
        return {"kind": "text", "text": value, "size": float(size)}

    def sub_token(value: str) -> dict[str, str | float]:
        return {"kind": "sub", "text": value, "size": sub_size}

    if kind == "subtitle":
        return [
            text_token("154 single-profile trainings with TV("),
            rho,
            prime,
            sub_token("theory"),
            text_token(", "),
            rho,
            sub_token("model"),
            text_token(") >= 0.01"),
        ]
    if kind == "theory_prob":
        return [
            text_token("p"),
            sub_token("theory"),
            text_token("(c; "),
            rho,
            prime,
            text_token(")"),
        ]
    if kind == "empirical_prob":
        return [
            text_token("p"),
            sub_token("emp"),
            text_token("(c; "),
            rho,
            prime,
            text_token(")"),
        ]
    if kind == "tv_theory_reference":
        return [
            text_token("TV("),
            rho,
            prime,
            sub_token("theory"),
            text_token(", "),
            rho,
            sub_token("model"),
            text_token(")"),
        ]
    if kind == "tv_empirical_theory":
        return [
            text_token("TV("),
            rho,
            prime,
            sub_token("emp"),
            text_token(", "),
            rho,
            prime,
            sub_token("theory"),
            text_token(")"),
        ]
    raise ValueError(f"Unknown formula kind: {kind}")


def token_width(token: dict[str, str | float]) -> float:
    size = float(token["size"])
    kind = str(token["kind"])
    if kind == "rho":
        return size * 0.55
    if kind == "prime":
        return size * 0.24
    return estimated_text_width(str(token["text"]), size)


def formula_width(tokens: list[dict[str, str | float]]) -> float:
    return sum(token_width(token) for token in tokens)


def draw_svg_formula(
    kind: str,
    x: float,
    y: float,
    *,
    size: int = 12,
    anchor: str = "middle",
    rotate: bool = False,
) -> str:
    tokens = formula_tokens(kind, size)
    width = formula_width(tokens)
    start = 0.0
    if anchor == "middle":
        start = -width / 2.0
    elif anchor == "end":
        start = -width

    parts = [
        f'<g transform="translate({x:.2f} {y:.2f})' + (" rotate(-90)" if rotate else "") + '">'
    ]
    cursor = start
    for token in tokens:
        token_kind = str(token["kind"])
        token_size = float(token["size"])
        if token_kind == "rho":
            parts.append(
                f'<text x="{cursor:.2f}" y="0" font-size="{token_size:.2f}" '
                'font-style="italic" fill="#000000">ρ</text>'
            )
        elif token_kind == "prime":
            parts.append(
                f'<line x1="{cursor + 1.0:.2f}" y1="{-0.78 * size:.2f}" '
                f'x2="{cursor + 3.0:.2f}" y2="{-0.42 * size:.2f}" '
                'stroke="#000000" stroke-width="1.1"/>'
            )
        elif token_kind == "sub":
            parts.append(
                f'<text x="{cursor:.2f}" y="{0.32 * size:.2f}" '
                f'font-size="{token_size:.2f}" fill="#000000">{html.escape(str(token["text"]))}</text>'
            )
        else:
            parts.append(
                f'<text x="{cursor:.2f}" y="0" font-size="{token_size:.2f}" '
                f'fill="#000000">{html.escape(str(token["text"]))}</text>'
            )
        cursor += token_width(token)
    parts.append("</g>")
    return "".join(parts)


class PdfCanvas:
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

    def rect(self, x: float, y: float, w: float, h: float, *, fill: str | None = None, stroke: str | None = None, width: float = 1.0) -> None:
        y_pdf = self.py(y + h)
        color_ops = []
        if fill is not None:
            color_ops.append(self.fill_color(fill))
        if stroke is not None:
            color_ops.append(self.stroke_color(stroke))
            color_ops.append(f"{width:.2f} w")
        paint = "B" if fill is not None and stroke is not None else "f" if fill is not None else "S"
        self.ops.append("q " + " ".join(color_ops) + f" {x:.2f} {y_pdf:.2f} {w:.2f} {h:.2f} re {paint} Q")

    def line(self, x1: float, y1: float, x2: float, y2: float, *, stroke: str = "#000000", width: float = 1.0, dash: str | None = None) -> None:
        dash_cmd = "[] 0 d" if dash is None else f"[{dash}] 0 d"
        self.ops.append(
            "q "
            f"{self.stroke_color(stroke)} {width:.2f} w {dash_cmd} "
            f"{x1:.2f} {self.py(y1):.2f} m {x2:.2f} {self.py(y2):.2f} l S Q"
        )

    def polygon(self, points: list[tuple[float, float]], *, fill: str, stroke: str, width: float = 1.0) -> None:
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

    def circle(self, cx: float, cy: float, radius: float, *, fill: str, stroke: str, width: float = 1.0) -> None:
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
        font: str = "F1",
    ) -> None:
        if anchor == "middle":
            x -= estimated_text_width(content, size) / 2.0
        elif anchor == "end":
            x -= estimated_text_width(content, size)
        self.ops.append(
            "q "
            f"BT /{font} {size} Tf {self.fill_color(fill)} "
            f"1 0 0 1 {x:.2f} {self.py(y):.2f} Tm "
            f"({pdf_escape(content)}) Tj ET Q"
        )

    def rich_text(
        self,
        x: float,
        y: float,
        parts: list[dict[str, str | float]],
        *,
        anchor: str = "start",
        fill: str = "#000000",
    ) -> None:
        width = sum(estimated_text_width(str(part["text"]), float(part["size"])) for part in parts)
        if anchor == "middle":
            x -= width / 2.0
        elif anchor == "end":
            x -= width
        cursor = x
        for part in parts:
            text_value = str(part["text"])
            size = float(part["size"])
            self.text(
                cursor,
                y + float(part.get("dy", 0.0)),
                text_value,
                size=int(round(size)),
                fill=fill,
                font=str(part.get("font", "F1")),
            )
            cursor += estimated_text_width(text_value, size)

    def rotated_text(
        self,
        x: float,
        y: float,
        content: str,
        *,
        size: int = 12,
        fill: str = "#000000",
        anchor: str = "middle",
        font: str = "F1",
    ) -> None:
        y_pdf = self.py(y)
        offset = 0.0
        if anchor == "middle":
            offset = -estimated_text_width(content, size) / 2.0
        elif anchor == "end":
            offset = -estimated_text_width(content, size)
        self.ops.append(
            "q "
            f"BT /{font} {size} Tf {self.fill_color(fill)} "
            f"0 1 -1 0 {x:.2f} {y_pdf + offset:.2f} Tm "
            f"({pdf_escape(content)}) Tj ET Q"
        )

    def rotated_rich_text(
        self,
        x: float,
        y: float,
        parts: list[dict[str, str | float]],
        *,
        anchor: str = "middle",
        fill: str = "#000000",
    ) -> None:
        width = sum(estimated_text_width(str(part["text"]), float(part["size"])) for part in parts)
        offset = 0.0
        if anchor == "middle":
            offset = -width / 2.0
        elif anchor == "end":
            offset = -width
        cursor = offset
        y_pdf = self.py(y)
        for part in parts:
            text_value = str(part["text"])
            size = float(part["size"])
            dy = float(part.get("dy", 0.0))
            self.ops.append(
                "q "
                f"BT /{part.get('font', 'F1')} {int(round(size))} Tf {self.fill_color(fill)} "
                f"0 1 -1 0 {x - dy:.2f} {y_pdf + cursor:.2f} Tm "
                f"({pdf_escape(text_value)}) Tj ET Q"
            )
            cursor += estimated_text_width(text_value, size)

    def save(self, output: Path) -> None:
        stream = "\n".join(self.ops).encode("latin-1")
        objects = [
            b"<< /Type /Catalog /Pages 2 0 R >>",
            b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
            (
                f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {self.width} {self.height}] "
                "/Resources << /Font << /F1 5 0 R /F2 6 0 R >> >> /Contents 4 0 R >>"
            ).encode("latin-1"),
            b"<< /Length " + str(len(stream)).encode("ascii") + b" >>\nstream\n" + stream + b"\nendstream",
            b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>",
            b"<< /Type /Font /Subtype /Type1 /BaseFont /Symbol >>",
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


def draw_pdf_formula(
    canvas: PdfCanvas,
    kind: str,
    x: float,
    y: float,
    *,
    size: int = 12,
    anchor: str = "middle",
    rotate: bool = False,
) -> None:
    tokens = formula_tokens(kind, size)
    width = formula_width(tokens)
    start = 0.0
    if anchor == "middle":
        start = -width / 2.0
    elif anchor == "end":
        start = -width

    def rotated_text(local_x: float, local_y: float, content: str, token_size: int, font: str) -> None:
        canvas.ops.append(
            "q "
            f"BT /{font} {token_size} Tf {canvas.fill_color('#000000')} "
            f"0 1 -1 0 {x - local_y:.2f} {canvas.py(y) + local_x:.2f} Tm "
            f"({pdf_escape(content)}) Tj ET Q"
        )

    def rotated_line(x1: float, y1: float, x2: float, y2: float) -> None:
        canvas.line(x + y1, y - x1, x + y2, y - x2, stroke="#000000", width=1.1)

    cursor = start
    for token in tokens:
        token_kind = str(token["kind"])
        token_size = float(token["size"])
        if token_kind == "rho":
            if rotate:
                rotated_text(cursor, 0.0, "r", int(round(token_size)), "F2")
            else:
                canvas.text(cursor + x, y, "r", size=int(round(token_size)), font="F2")
        elif token_kind == "prime":
            if rotate:
                rotated_line(cursor + 1.0, -0.78 * size, cursor + 3.0, -0.42 * size)
            else:
                canvas.line(
                    x + cursor + 1.0,
                    y - 0.78 * size,
                    x + cursor + 3.0,
                    y - 0.42 * size,
                    stroke="#000000",
                    width=1.1,
                )
        elif token_kind == "sub":
            content = str(token["text"])
            if rotate:
                rotated_text(cursor, 0.32 * size, content, int(round(token_size)), "F1")
            else:
                canvas.text(x + cursor, y + 0.32 * size, content, size=int(round(token_size)))
        else:
            content = str(token["text"])
            if rotate:
                rotated_text(cursor, 0.0, content, int(round(token_size)), "F1")
            else:
                canvas.text(x + cursor, y, content, size=int(round(token_size)))
        cursor += token_width(token)


def svg_text(x: float, y: float, content: str, *, size: int = 12, weight: str = "400", fill: str = "#000000", anchor: str = "start") -> str:
    return (
        f'<text x="{x:.2f}" y="{y:.2f}" font-size="{size}" font-weight="{weight}" '
        f'fill="{fill}" text-anchor="{anchor}">{html.escape(content)}</text>'
    )


def svg_line(x1: float, y1: float, x2: float, y2: float, *, stroke: str = "#000000", width: float = 1.0, dash: str | None = None) -> str:
    dash_attr = "" if dash is None else f' stroke-dasharray="{dash}"'
    return (
        f'<line x1="{x1:.2f}" y1="{y1:.2f}" x2="{x2:.2f}" y2="{y2:.2f}" '
        f'stroke="{stroke}" stroke-width="{width:.2f}"{dash_attr}/>'
    )


def svg_circle(cx: float, cy: float, radius: float, *, fill: str, stroke: str, opacity: float = 1.0) -> str:
    return (
        f'<circle cx="{cx:.2f}" cy="{cy:.2f}" r="{radius:.2f}" fill="{fill}" '
        f'stroke="{stroke}" stroke-width="0.85" opacity="{opacity:.2f}"/>'
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


def nice(value: float) -> str:
    if abs(value) < 1e-12:
        return "0"
    if value < 0.01:
        return f"{value:.3f}"
    return f"{value:.2g}"


def compute_layout() -> dict[str, int]:
    return {
        "width": 860,
        "height": 480,
        "top": 104,
        "panel_h": 240,
        "left1": 72,
        "left2": 506,
        "panel_w": 285,
    }


def render_common(rows: list[ProfileRow], target) -> None:
    layout = compute_layout()
    top = layout["top"]
    panel_h = layout["panel_h"]
    left1 = layout["left1"]
    left2 = layout["left2"]
    panel_w = layout["panel_w"]
    bottom = top + panel_h

    prob_ticks = [0.0, 0.25, 0.5, 0.75, 1.0]
    err_ticks = [0.0, 0.02, 0.05, 0.10]
    update_ticks = [0.0, 0.25, 0.5, 0.75, 1.0]

    def p_x(value: float) -> float:
        return left1 + value * panel_w

    def p_y(value: float) -> float:
        return bottom - value * panel_h

    def e_x(value: float) -> float:
        return left2 + value * panel_w

    def e_y(value: float) -> float:
        return bottom - value / 0.12 * panel_h

    if isinstance(target, PdfCanvas):
        target.rect(0, 0, layout["width"], layout["height"], fill="#ffffff")
        target.text(layout["width"] / 2, 32, "Filtered Qwen2.5 DPO sweep: theory vs. experiment", size=18, fill="#000000", anchor="middle")
        target.text(
            layout["width"] / 2,
            55,
            "154 single-profile trainings with TV(theoretical update, model reference) >= 0.01",
            size=12,
            fill="#000000",
            anchor="middle",
        )
        rect = target.rect
        line = target.line
        text = target.text
        circle = lambda x, y, r, **kw: target.circle(
            x,
            y,
            r,
            fill=kw.get("fill", "#000000"),
            stroke=kw.get("stroke", "#000000"),
            width=kw.get("width", 1.0),
        )
        axis_text = target.text
        rotated_axis_text = target.rotated_text
    else:
        target.append(f'<rect width="{layout["width"]}" height="{layout["height"]}" fill="#ffffff"/>')
        target.append(svg_text(layout["width"] / 2, 32, "Filtered Qwen2.5 DPO sweep: theory vs. experiment", size=18, weight="700", fill="#000000", anchor="middle"))
        target.append(
            svg_text(
                layout["width"] / 2,
                55,
                "154 single-profile trainings with TV(theoretical update, model reference) >= 0.01",
                size=12,
                fill="#000000",
                anchor="middle",
            )
        )
        rect = lambda x, y, w, h, **kw: target.append(f'<rect x="{x:.2f}" y="{y:.2f}" width="{w:.2f}" height="{h:.2f}" fill="{kw.get("fill", "none")}" stroke="{kw.get("stroke", "none")}" stroke-width="{kw.get("width", 1.0):.2f}"/>')
        line = lambda x1, y1, x2, y2, **kw: target.append(svg_line(x1, y1, x2, y2, stroke=kw.get("stroke", "#000000"), width=kw.get("width", 1.0), dash=kw.get("dash")))
        text = lambda x, y, content, **kw: target.append(svg_text(x, y, content, size=kw.get("size", 12), weight=kw.get("weight", "400"), fill=kw.get("fill", "#000000"), anchor=kw.get("anchor", "start")))
        circle = lambda x, y, r, **kw: target.append(svg_circle(x, y, r, fill=kw.get("fill", "#000000"), stroke=kw.get("stroke", "#000000"), opacity=kw.get("opacity", 1.0)))
        axis_text = lambda x, y, content, **kw: target.append(
            svg_text(
                x,
                y,
                content,
                size=kw.get("size", 12),
                fill=kw.get("fill", "#000000"),
                anchor=kw.get("anchor", "middle"),
            )
        )
        rotated_axis_text = lambda x, y, content, **kw: target.append(
            f'<g transform="translate({x:.2f} {y:.2f}) rotate(-90)">'
            + svg_text(
                0,
                0,
                content,
                size=kw.get("size", 12),
                fill=kw.get("fill", "#000000"),
                anchor=kw.get("anchor", "middle"),
            )
            + "</g>"
        )

    for left, title in [(left1, "Candidate probabilities"), (left2, "Profile-level discrepancy")]:
        rect(left, top, panel_w, panel_h, fill="#ffffff", stroke="#000000", width=0.8)
        text(left, top - 18, title, size=13, fill="#000000", anchor="start")

    legend_x = left1 + 176
    legend_y = top - 21
    for label in LABELS:
        circle(legend_x, legend_y, 3.0, fill=LABEL_COLORS[label], stroke="#000000", opacity=0.75)
        text(legend_x + 7, legend_y + 4, label, size=10, fill="#000000")
        legend_x += 28

    for tick in prob_ticks:
        x = p_x(tick)
        y = p_y(tick)
        line(x, top, x, bottom, stroke="#b0b0b0", width=0.8)
        line(left1, y, left1 + panel_w, y, stroke="#b0b0b0", width=0.8)
        line(x, bottom, x, bottom + 5, stroke="#000000")
        line(left1 - 5, y, left1, y, stroke="#000000")
        text(x, bottom + 19, nice(tick), size=10, fill="#000000", anchor="middle")
        text(left1 - 10, y + 4, nice(tick), size=10, fill="#000000", anchor="end")
    line(left1, bottom, left1 + panel_w, bottom, stroke="#000000", width=1.2)
    line(left1, top, left1, bottom, stroke="#000000", width=1.2)
    line(left1, bottom, left1 + panel_w, top, stroke="#808080", width=1.3, dash="5 4")

    candidate_xs: list[float] = []
    candidate_ys: list[float] = []
    for row in rows:
        for label in LABELS:
            theory = row.theoretical_probs[label]
            empirical = row.final_probs[label]
            candidate_xs.append(theory)
            candidate_ys.append(empirical)
            circle(p_x(theory), p_y(empirical), 2.5, fill=LABEL_COLORS[label], stroke="#000000", opacity=0.62)

    for tick in update_ticks:
        x = e_x(tick)
        line(x, top, x, bottom, stroke="#b0b0b0", width=0.8)
        line(x, bottom, x, bottom + 5, stroke="#000000")
        text(x, bottom + 19, nice(tick), size=10, fill="#000000", anchor="middle")
    for tick in err_ticks:
        y = e_y(tick)
        line(left2, y, left2 + panel_w, y, stroke="#b0b0b0", width=0.8)
        line(left2 - 5, y, left2, y, stroke="#000000")
        text(left2 - 10, y + 4, nice(tick), size=10, fill="#000000", anchor="end")
    line(left2, bottom, left2 + panel_w, bottom, stroke="#000000", width=1.2)
    line(left2, top, left2, bottom, stroke="#000000", width=1.2)
    line(left2, e_y(0.02), left2 + panel_w, e_y(0.02), stroke="#808080", width=1.1, dash="4 4")
    text(left2 + panel_w - 2, e_y(0.02) - 5, "0.02", size=9, fill="#000000", anchor="end")

    for row in rows:
        top_match = row.theory_top == row.final_top
        circle(
            e_x(row.tv_theory_to_reference),
            e_y(min(row.tv_empirical_to_theory, 0.12)),
            3.0 if top_match else 4.5,
            fill=QWEN25_COLOR if top_match else "#ffffff",
            stroke="#000000" if top_match else "#000000",
            opacity=0.68 if top_match else 1.0,
        )

    prob_corr = correlation(candidate_xs, candidate_ys)
    tvs = [row.tv_empirical_to_theory for row in rows]
    within_001 = sum(value <= 0.01 for value in tvs)
    within_002 = sum(value <= 0.02 for value in tvs)
    top_matches = sum(row.theory_top == row.final_top for row in rows)
    text(left1, bottom + 48, f"Candidate-probability r = {prob_corr:.4f}", size=11, fill="#000000")
    text(left2, bottom + 48, f"TV error <= 0.02: {within_002}/{len(rows)}; top match: {top_matches}/{len(rows)}", size=11, fill="#000000")
    text(left2, bottom + 64, f"median TV error = {statistics.median(tvs):.5f}; <= 0.01: {within_001}/{len(rows)}", size=11, fill="#000000")

    axis_text(left1 + panel_w / 2, layout["height"] - 28, "Theoretical candidate probability", size=12, anchor="middle")
    rotated_axis_text(24, top + panel_h / 2, "Post-training candidate probability", size=12, anchor="middle")
    axis_text(left2 + panel_w / 2, layout["height"] - 28, "TV(theoretical update, model reference)", size=12, anchor="middle")
    rotated_axis_text(left2 - 52, top + panel_h / 2, "TV(post-training update, theoretical update)", size=12, anchor="middle")


def render_svg(rows: list[ProfileRow], output: Path) -> None:
    layout = compute_layout()
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{layout["width"]}" height="{layout["height"]}" '
        f'viewBox="0 0 {layout["width"]} {layout["height"]}" role="img">',
        "<title>Filtered Qwen2.5 DPO sweep agreement</title>",
        "<desc>Agreement between closed-form RTBT theory and empirical single-profile DPO training.</desc>",
        "<style>text{font-family:DejaVu Sans, Helvetica, Arial, sans-serif;}</style>",
    ]
    render_common(rows, parts)
    parts.append("</svg>")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(parts) + "\n")


def render_pdf(rows: list[ProfileRow], output: Path) -> None:
    layout = compute_layout()
    canvas = PdfCanvas(layout["width"], layout["height"])
    render_common(rows, canvas)
    canvas.save(output)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--pdf-output", type=Path, default=DEFAULT_PDF_OUTPUT)
    parser.add_argument("--plot-data-output", type=Path, default=DEFAULT_PLOT_DATA)
    parser.add_argument("--no-pdf", action="store_true")
    args = parser.parse_args()

    rows = load_rows(args.input)
    write_plot_data(rows, args.plot_data_output)
    render_svg(rows, args.output)
    print(f"wrote {args.output}")
    if not args.no_pdf:
        render_pdf(rows, args.pdf_output)
        print(f"wrote {args.pdf_output}")
    print(f"wrote {args.plot_data_output}")


if __name__ == "__main__":
    main()
