#!/usr/bin/env python3

import argparse
import csv
import html
import math
import sys
from collections import defaultdict
from pathlib import Path
from typing import Iterable, Optional


csv.field_size_limit(sys.maxsize)


LANE_LABELS = {
    "auto": "Auto",
    "auto-duper": "Auto + Duper",
    "duper": "Duper",
    "duper-only": "Duper",
    "grind": "grind",
    "grind-only": "grind",
    "crush-only": "Crush (Z3)",
    "crush-verify": "Crush (trusted SMT)",
    "crush-core": "Core",
    "crush-alethe": "Alethe",
    "crush-portfolio": "Portfolio",
}

BACKEND_LABELS = {
    "auto": "Auto",
    "duper": "Duper",
    "crush": "Crush",
    "grind": "grind",
}

SUITE_LABELS = {
    "leanhammer": "LeanHammer",
    "loom": "Loom",
    "cashmere": "Cashmere",
    "velvet": "Velvet",
    "plean": "PLean",
}

SUITE_ORDER = ("leanhammer", "loom", "cashmere", "velvet", "plean")

BACKEND_COLORS = {
    "auto": "#597A91",
    "duper": "#B55B45",
    "crush": "#178078",
    "grind": "#77834D",
}

OUTCOME_FIELDS = (
    ("success", "Success", "#178078"),
    ("translation_error", "Translation error", "#D69A3A"),
    ("timeout", "Timeout", "#A4433E"),
    ("failed_to_prove", "Failed to prove", "#597A91"),
)

LANE_ORDER = (
    "auto",
    "auto-duper",
    "duper",
    "duper-only",
    "crush-only",
    "crush-verify",
    "crush-core",
    "crush-alethe",
    "crush-portfolio",
    "grind-only",
    "grind",
)

LANE_COLORS = {
    "auto": "#597A91",
    "auto-duper": "#597A91",
    "duper": "#B55B45",
    "duper-only": "#B55B45",
    "crush-only": "#0B504A",
    "crush-verify": "#178078",
    "crush-core": "#DD7A45",
    "crush-alethe": "#D3A22E",
    "crush-portfolio": "#254A62",
    "grind-only": "#77834D",
    "grind": "#77834D",
}

PHASE_COLORS = {
    "collect": "#4F6D7A",
    "pre-reconstruct": "#739E82",
    "normalize": "#DAB785",
    "instantiate": "#D5896F",
    "monomorphize": "#B35C5D",
    "translate": "#6E7FA3",
    "solve": "#234E52",
    "replay": "#E09F3E",
    "reconstruct": "#9E2A2B",
}

FAILURE_COLORS = (
    "#A4433E",
    "#D27645",
    "#D6A73A",
    "#557A75",
    "#476A8A",
    "#7B7653",
)

FAILURE_MODE_ORDER = (
    "certificate-error",
    "certificate-error+core-failed",
    "core-failed",
    "not-attempted",
    "rule-gap",
    "solver-sat",
    "solver-unknown",
    "tactic",
    "term-gap",
)

FAILURE_MODE_COLORS = {
    "certificate-error": "#A4433E",
    "certificate-error+core-failed": "#D27645",
    "core-failed": "#D6A73A",
    "not-attempted": "#557A75",
    "rule-gap": "#476A8A",
    "solver-sat": "#7B7653",
    "solver-unknown": "#80546B",
    "tactic": "#B7684B",
    "term-gap": "#3D7C83",
}

INK = "#1B2927"
MUTED = "#64716E"
GRID = "#D9D5CB"
PAPER = "#FBF8F1"

OUTPUTS = (
    "tables",
    "coverage",
    "outcomes",
    "reconstruction",
    "reconstruction-failures",
    "phase-breakdown",
    "alethe-replay-scaling",
)


def read_tsv(result_dirs: list[Path], filename: str) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    seen: set[tuple[tuple[str, str], ...]] = set()
    for result_dir in result_dirs:
        path = result_dir / filename
        if not path.exists():
            continue
        with path.open(newline="", encoding="utf-8") as stream:
            for row in csv.DictReader(stream, delimiter="\t"):
                signature = tuple(sorted(row.items()))
                if signature in seen:
                    continue
                seen.add(signature)
                row["_source"] = str(result_dir)
                rows.append(row)
    return rows


def rows_with_columns(
    rows: list[dict[str, str]], columns: tuple[str, ...]
) -> list[dict[str, str]]:
    return [row for row in rows if all(column in row for column in columns)]


def unique_rows(
    rows: list[dict[str, str]], keys: tuple[str, ...], filename: str
) -> list[dict[str, str]]:
    indexed: dict[tuple[str, ...], dict[str, str]] = {}
    for row in rows:
        key = tuple(row[name] for name in keys)
        previous = indexed.get(key)
        if previous is None:
            indexed[key] = row
            continue
        current_data = {name: value for name, value in row.items() if name != "_source"}
        previous_data = {
            name: value for name, value in previous.items() if name != "_source"
        }
        if current_data != previous_data:
            rendered = ", ".join(f"{name}={value}" for name, value in zip(keys, key))
            raise SystemExit(
                f"{filename} has conflicting rows for {rendered}; "
                "pass only one result directory for that suite and lane"
            )
    return list(indexed.values())


def lane_sort_key(lane: str) -> tuple[int, str]:
    try:
        return (LANE_ORDER.index(lane), lane)
    except ValueError:
        return (len(LANE_ORDER), lane)


def label_lane(lane: str) -> str:
    return LANE_LABELS.get(lane, lane)


def label_backend(backend: str) -> str:
    return BACKEND_LABELS.get(backend, backend)


def label_suite(suite: str) -> str:
    return SUITE_LABELS.get(suite, suite)


def suite_sort_key(suite: str) -> tuple[int, str]:
    try:
        return (SUITE_ORDER.index(suite), suite)
    except ValueError:
        return (len(SUITE_ORDER), suite)


def xml(value: object) -> str:
    return html.escape(str(value), quote=True)


def markdown(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def svg_open(width: int, height: int, title: str, description: str) -> list[str]:
    return [
        (
            f'<svg xmlns="http://www.w3.org/2000/svg" '
            f'viewBox="0 0 {width} {height}" role="img" '
            f'aria-labelledby="title description">'
        ),
        f"<title id=\"title\">{xml(title)}</title>",
        f"<desc id=\"description\">{xml(description)}</desc>",
        "<style>",
        (
            "text { fill: #1B2927; font-family: 'Avenir Next', "
            "'IBM Plex Sans', sans-serif; }"
        ),
        ".title { font-size: 25px; font-weight: 700; letter-spacing: .2px; }",
        ".subtitle { fill: #64716E; font-size: 13px; }",
        ".axis { fill: #64716E; font-size: 12px; }",
        ".label { font-size: 13px; font-weight: 600; }",
        ".value { font-size: 11px; font-weight: 600; }",
        ".legend { font-size: 12px; }",
        ".grid { stroke: #D9D5CB; stroke-width: 1; }",
        ".axis-line { stroke: #64716E; stroke-width: 1.2; }",
        "</style>",
        f'<rect width="{width}" height="{height}" fill="{PAPER}"/>',
    ]


def text(
    x: float,
    y: float,
    value: object,
    css_class: str = "",
    anchor: str = "start",
    transform: str = "",
) -> str:
    class_attr = f' class="{css_class}"' if css_class else ""
    transform_attr = f' transform="{transform}"' if transform else ""
    return (
        f'<text x="{x:.2f}" y="{y:.2f}" text-anchor="{anchor}"'
        f"{class_attr}{transform_attr}>{xml(value)}</text>"
    )


def rect(
    x: float,
    y: float,
    width: float,
    height: float,
    fill: str,
    radius: float = 0,
    opacity: float = 1.0,
) -> str:
    return (
        f'<rect x="{x:.2f}" y="{y:.2f}" width="{max(width, 0):.2f}" '
        f'height="{max(height, 0):.2f}" rx="{radius:.2f}" '
        f'fill="{fill}" opacity="{opacity:.3f}"/>'
    )


def line(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    css_class: str = "",
    stroke: str = "",
    dash: str = "",
) -> str:
    attrs = []
    if css_class:
        attrs.append(f'class="{css_class}"')
    if stroke:
        attrs.append(f'stroke="{stroke}"')
    if dash:
        attrs.append(f'stroke-dasharray="{dash}"')
    return (
        f'<line x1="{x1:.2f}" y1="{y1:.2f}" x2="{x2:.2f}" '
        f'y2="{y2:.2f}" {" ".join(attrs)}/>'
    )


def circle(x: float, y: float, radius: float, fill: str, tooltip: str) -> str:
    return (
        f'<circle cx="{x:.2f}" cy="{y:.2f}" r="{radius:.2f}" '
        f'fill="{fill}" stroke="{PAPER}" stroke-width="1.5">'
        f"<title>{xml(tooltip)}</title></circle>"
    )


def pie_sector(
    x: float,
    y: float,
    radius: float,
    start_angle: float,
    end_angle: float,
    fill: str,
    tooltip: str,
) -> str:
    angle = end_angle - start_angle
    if angle >= 2 * math.pi - 1e-9:
        return circle(x, y, radius, fill, tooltip)
    start_x = x + radius * math.cos(start_angle)
    start_y = y + radius * math.sin(start_angle)
    end_x = x + radius * math.cos(end_angle)
    end_y = y + radius * math.sin(end_angle)
    large_arc = 1 if angle > math.pi else 0
    path = (
        f"M {x:.2f} {y:.2f} L {start_x:.2f} {start_y:.2f} "
        f"A {radius:.2f} {radius:.2f} 0 {large_arc} 1 "
        f"{end_x:.2f} {end_y:.2f} Z"
    )
    return (
        f'<path d="{path}" fill="{fill}" stroke="{PAPER}" stroke-width="1.5">'
        f"<title>{xml(tooltip)}</title></path>"
    )


def write_svg(path: Path, elements: list[str]) -> None:
    path.write_text("\n".join([*elements, "</svg>", ""]), encoding="utf-8")


def write_markdown_table(
    stream, headers: list[str], rows: Iterable[Iterable[object]]
) -> None:
    stream.write("| " + " | ".join(headers) + " |\n")
    stream.write("|" + "|".join("---" for _ in headers) + "|\n")
    for row in rows:
        stream.write("| " + " | ".join(markdown(value) for value in row) + " |\n")
    stream.write("\n")


def draw_legend(
    elements: list[str],
    entries: list[tuple[str, str]],
    x: float,
    y: float,
    max_width: float,
) -> float:
    cursor_x = x
    cursor_y = y
    for label, color in entries:
        entry_width = 32 + max(55, len(label) * 7)
        if cursor_x + entry_width > x + max_width:
            cursor_x = x
            cursor_y += 24
        elements.append(rect(cursor_x, cursor_y - 11, 15, 10, color, 2))
        elements.append(text(cursor_x + 21, cursor_y - 2, label, "legend"))
        cursor_x += entry_width
    return cursor_y + 8


def plot_coverage(rows: list[dict[str, str]], path: Path) -> None:
    suites = sorted({row["suite"] for row in rows})
    is_headline = all(row.get("backend") for row in rows)
    if is_headline:
        order = ("auto", "duper", "crush", "grind")
        series = sorted(
            {row["backend"] for row in rows},
            key=lambda backend: (
                order.index(backend) if backend in order else len(order),
                backend,
            ),
        )
        indexed = {(row["suite"], row["backend"]): row for row in rows}
        labels = {backend: label_backend(backend) for backend in series}
        colors = {
            backend: BACKEND_COLORS.get(backend, "#66736F")
            for backend in series
        }
    else:
        series = sorted({row["lane"] for row in rows}, key=lane_sort_key)
        indexed = {(row["suite"], row["lane"]): row for row in rows}
        labels = {lane: label_lane(lane) for lane in series}
        colors = {
            lane: LANE_COLORS.get(lane, "#66736F") for lane in series
        }
    width = max(1040, 260 + len(suites) * max(130, len(series) * 32))
    height = 610
    left, right, top, bottom = 80.0, 32.0, 142.0, 105.0
    chart_width = width - left - right
    chart_height = height - top - bottom
    elements = svg_open(
        width,
        height,
        "Verification coverage",
        "Solved verification conditions as a percentage of the fixed corpus workload.",
    )
    elements.append(text(42, 42, "Verification coverage", "title"))
    elements.append(
        text(
            42,
            66,
            "Solved / all corpus VCs; Crush trusts SMT; failed and missing count unsolved",
            "subtitle",
        )
    )
    legend_entries = list(
        dict.fromkeys(
            (labels[entry], colors[entry])
            for entry in series
        )
    )
    draw_legend(elements, legend_entries, 42, 98, width - 84)

    for value in (0, 25, 50, 75, 100):
        y = top + chart_height * (1.0 - value / 100.0)
        elements.append(line(left, y, width - right, y, "grid"))
        elements.append(text(left - 12, y + 4, f"{value}%", "axis", "end"))

    group_width = chart_width / max(len(suites), 1)
    for suite_index, suite in enumerate(suites):
        available = [
            entry for entry in series if (suite, entry) in indexed
        ]
        usable = group_width * 0.78
        bar_width = min(31.0, max(10.0, usable / max(len(available), 1) - 5))
        bars_width = len(available) * bar_width + max(0, len(available) - 1) * 5
        group_start = left + suite_index * group_width + (group_width - bars_width) / 2
        for entry_index, entry in enumerate(available):
            row = indexed[(suite, entry)]
            percentage = float(row["pass_pct"])
            total_vcs = row.get("total_vcs", row["attempted_vcs"])
            x = group_start + entry_index * (bar_width + 5)
            y = top + chart_height * (1.0 - percentage / 100.0)
            elements.append(
                rect(
                    x,
                    y,
                    bar_width,
                    top + chart_height - y,
                    colors[entry],
                    2,
                )
            )
            elements.append(
                text(
                    x + bar_width / 2,
                    max(top - 5, y - 7),
                    f'{row["solved_vcs"]}/{total_vcs}',
                    "value",
                    "middle",
                )
            )
        center = left + (suite_index + 0.5) * group_width
        elements.append(text(center, top + chart_height + 27, suite, "label", "middle"))
    elements.append(
        text(
            width / 2,
            height - 25,
            "Corpus",
            "axis",
            "middle",
        )
    )
    write_svg(path, elements)


def plot_outcomes(rows: list[dict[str, str]], path: Path) -> None:
    suites = sorted({row["suite"] for row in rows}, key=suite_sort_key)
    backend_order = ("auto", "duper", "crush", "grind")
    indexed = {(row["suite"], row["backend"]): row for row in rows}
    totals_by_suite: dict[str, set[int]] = defaultdict(set)
    for row in rows:
        total = int(row["total_vcs"])
        totals_by_suite[row["suite"]].add(total)
        partition = sum(int(row[field]) for field, _, _ in OUTCOME_FIELDS)
        if total <= 0 or partition != total:
            raise SystemExit(
                "headline-outcomes.tsv does not partition the fixed workload "
                f"for {row['suite']} / {row['backend']}: "
                f"{partition} outcomes for {total} VCs"
            )
    for suite, totals in totals_by_suite.items():
        if len(totals) != 1:
            raise SystemExit(
                "headline-outcomes.tsv uses different workloads for "
                f"{suite}: {sorted(totals)}"
            )

    width = max(1180, 220 + len(suites) * 220)
    height = 650
    left, right, top, bottom = 82.0, 36.0, 142.0, 120.0
    chart_width = width - left - right
    chart_height = height - top - bottom
    chart_bottom = top + chart_height
    elements = svg_open(
        width,
        height,
        "Verification outcomes by corpus and backend",
        (
            "Within each corpus, every stacked bar partitions the same VCs into "
            "success, translation error, timeout, and failed to prove."
        ),
    )
    elements.append(text(42, 42, "Verification outcomes", "title"))
    elements.append(
        text(
            42,
            66,
            "Within each corpus, every bar uses the same VCs; Crush trusts SMT verdicts",
            "subtitle",
        )
    )
    draw_legend(
        elements,
        [(label, color) for _, label, color in OUTCOME_FIELDS],
        42,
        98,
        width - 84,
    )

    for value in (0, 25, 50, 75, 100):
        y = chart_bottom - chart_height * value / 100.0
        elements.append(line(left, y, width - right, y, "grid"))
        elements.append(text(left - 12, y + 4, f"{value}%", "axis", "end"))

    group_width = chart_width / max(len(suites), 1)
    for suite_index, suite in enumerate(suites):
        available = [
            backend
            for backend in backend_order
            if (suite, backend) in indexed
        ]
        bar_width = min(42.0, group_width * 0.16)
        gap = min(14.0, bar_width * 0.35)
        bars_width = len(available) * bar_width + max(0, len(available) - 1) * gap
        group_start = (
            left
            + suite_index * group_width
            + (group_width - bars_width) / 2
        )
        for backend_index, backend in enumerate(available):
            row = indexed[(suite, backend)]
            total = int(row["total_vcs"])
            x = group_start + backend_index * (bar_width + gap)
            cursor_y = chart_bottom
            for field, label, color in OUTCOME_FIELDS:
                count = int(row[field])
                if count == 0:
                    continue
                segment_height = chart_height * count / total
                y = cursor_y - segment_height
                tooltip = (
                    f"{label_suite(suite)} / {label_backend(backend)} / {label}: "
                    f"{count} of {total} ({100.0 * count / total:.1f}%)"
                )
                elements.append(
                    f"<g><title>{xml(tooltip)}</title>"
                    f"{rect(x, y, bar_width, segment_height, color)}</g>"
                )
                if segment_height >= 18:
                    elements.append(
                        text(
                            x + bar_width / 2,
                            y + segment_height / 2 + 4,
                            count,
                            "value",
                            "middle",
                        )
                    )
                cursor_y = y
            elements.append(
                text(
                    x + bar_width / 2,
                    chart_bottom + 22,
                    label_backend(backend),
                    "axis",
                    "middle",
                )
            )
        center = left + (suite_index + 0.5) * group_width
        total = int(indexed[(suite, available[0])]["total_vcs"])
        elements.append(
            text(center, chart_bottom + 50, label_suite(suite), "label", "middle")
        )
        elements.append(
            text(center, chart_bottom + 69, f"{total} VCs", "axis", "middle")
        )
        if suite_index > 0:
            separator = left + suite_index * group_width
            elements.append(
                line(separator, top, separator, chart_bottom + 74, stroke=GRID)
            )
    write_svg(path, elements)


def plot_reconstruction(rows: list[dict[str, str]], path: Path) -> None:
    suites = sorted(row["suite"] for row in rows)
    fields = (
        ("core_reconstructed", "Core", LANE_COLORS["crush-core"]),
        ("alethe_reconstructed", "Alethe", LANE_COLORS["crush-alethe"]),
        ("portfolio_reconstructed", "Portfolio", LANE_COLORS["crush-portfolio"]),
    )
    width = max(1000, 260 + len(suites) * 175)
    height = 600
    left, right, top, bottom = 80.0, 34.0, 140.0, 108.0
    chart_width = width - left - right
    chart_height = height - top - bottom
    elements = svg_open(
        width,
        height,
        "Proof reconstruction coverage",
        "Kernel-checked reconstruction success among SMT-verified conditions.",
    )
    elements.append(text(42, 42, "Proof reconstruction coverage", "title"))
    elements.append(
        text(
            42,
            66,
            "Successfully reconstructed VCs / SMT-verified VCs; higher is better",
            "subtitle",
        )
    )
    draw_legend(
        elements,
        [(label, color) for _, label, color in fields],
        42,
        98,
        width - 84,
    )
    for value in (0, 25, 50, 75, 100):
        y = top + chart_height * (1.0 - value / 100.0)
        elements.append(line(left, y, width - right, y, "grid"))
        elements.append(text(left - 12, y + 4, f"{value}%", "axis", "end"))

    group_width = chart_width / max(len(rows), 1)
    for suite_index, row in enumerate(sorted(rows, key=lambda item: item["suite"])):
        verified = int(row["verified_vcs"])
        bar_width = min(42.0, group_width * 0.19)
        bars_width = len(fields) * bar_width + (len(fields) - 1) * 8
        group_start = left + suite_index * group_width + (group_width - bars_width) / 2
        for field_index, (field, _, color) in enumerate(fields):
            count = int(row[field])
            percentage = 100.0 * count / verified if verified else 0.0
            x = group_start + field_index * (bar_width + 8)
            y = top + chart_height * (1.0 - percentage / 100.0)
            elements.append(
                rect(x, y, bar_width, top + chart_height - y, color, 2)
            )
            elements.append(
                text(
                    x + bar_width / 2,
                    max(top - 5, y - 7),
                    f"{count}/{verified}",
                    "value",
                    "middle",
                )
            )
        center = left + (suite_index + 0.5) * group_width
        elements.append(
            text(center, top + chart_height + 27, row["suite"], "label", "middle")
        )
        elements.append(
            text(
                center,
                top + chart_height + 47,
                f'{verified}/{row["total_vcs"]} SMT-verified',
                "axis",
                "middle",
            )
        )
    write_svg(path, elements)


def plot_failures(
    rows: list[dict[str, str]],
    reconstruction: list[dict[str, str]],
    path: Path,
) -> None:
    suites = sorted(row["suite"] for row in reconstruction)
    failure_modes = sorted(
        {row["failure_mode"] for row in rows},
        key=lambda mode: (
            FAILURE_MODE_ORDER.index(mode)
            if mode in FAILURE_MODE_ORDER
            else len(FAILURE_MODE_ORDER),
            mode,
        ),
    )
    colors = {
        mode: FAILURE_MODE_COLORS.get(
            mode, FAILURE_COLORS[index % len(FAILURE_COLORS)]
        )
        for index, mode in enumerate(failure_modes)
    }
    counts: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    for row in rows:
        counts[row["suite"]][row["failure_mode"]] += int(row["vcs"])

    width = 1260
    columns = 3
    panel_rows = max(1, math.ceil(len(suites) / columns))
    legend_entries = [
        (mode.replace("+", " + ").replace("-", " "), colors[mode])
        for mode in failure_modes
    ]
    legend_lines = max(
        1,
        math.ceil(
            sum(45 + len(label) * 7 for label, _ in legend_entries) / 1120
        ),
    )
    top = 112.0 + legend_lines * 24
    panel_height = 270.0
    height = int(top + panel_rows * panel_height + 68)
    elements = svg_open(
        width,
        height,
        "Proof reconstruction failure modes",
        "One pie per corpus showing strict-lane failure records by reported cause.",
    )
    elements.append(text(42, 42, "Proof reconstruction failure modes", "title"))
    elements.append(
        text(
            42,
            66,
            "One pie per corpus; slices aggregate Core, Alethe, and Portfolio records",
            "subtitle",
        )
    )
    if legend_entries:
        draw_legend(elements, legend_entries, 42, 98, width - 84)

    panel_width = (width - 80.0) / columns
    radius = 88.0
    for index, suite in enumerate(suites):
        row = index // columns
        column = index % columns
        center_x = 40.0 + (column + 0.5) * panel_width
        panel_top = top + row * panel_height
        center_y = panel_top + 126.0
        suite_counts = counts[suite]
        total = sum(suite_counts.values())
        elements.append(text(center_x, panel_top + 18, suite, "label", "middle"))

        if total == 0:
            elements.append(
                circle(
                    center_x,
                    center_y,
                    radius,
                    "#E6E1D7",
                    f"{suite}: no reconstruction failure records",
                )
            )
            elements.append(text(center_x, center_y + 5, "0", "label", "middle"))
            summary = "no failure records"
        else:
            start_angle = -math.pi / 2
            for mode in failure_modes:
                count = suite_counts.get(mode, 0)
                if count == 0:
                    continue
                share = count / total
                end_angle = start_angle + 2 * math.pi * share
                label = mode.replace("+", " + ").replace("-", " ")
                elements.append(
                    pie_sector(
                        center_x,
                        center_y,
                        radius,
                        start_angle,
                        end_angle,
                        colors[mode],
                        f"{suite}: {label}: {count} ({share:.1%})",
                    )
                )
                if share >= 0.06:
                    middle = (start_angle + end_angle) / 2
                    elements.append(
                        text(
                            center_x + radius * 0.62 * math.cos(middle),
                            center_y + radius * 0.62 * math.sin(middle) + 4,
                            count,
                            "value",
                            "middle",
                        )
                    )
                start_angle = end_angle
            summary = f"{total} failure records"
        elements.append(
            text(center_x, center_y + radius + 26, summary, "axis", "middle")
        )

    elements.append(
        text(
            width / 2,
            height - 24,
            (
                "A verified VC may contribute one record per strict lane; "
                "not attempted remains a separate outcome."
            ),
            "subtitle",
            "middle",
        )
    )
    write_svg(path, elements)


def plot_phases(rows: list[dict[str, str]], path: Path) -> None:
    grouped: dict[tuple[str, str], list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        grouped[(row["suite"], row["lane"])].append(row)
    keys = sorted(grouped, key=lambda key: (key[0], lane_sort_key(key[1])))
    phases = sorted(
        {row["phase"] for row in rows},
        key=lambda phase: (
            list(PHASE_COLORS).index(phase)
            if phase in PHASE_COLORS
            else len(PHASE_COLORS),
            phase,
        ),
    )
    phase_colors = {
        phase: PHASE_COLORS.get(
            phase, FAILURE_COLORS[index % len(FAILURE_COLORS)]
        )
        for index, phase in enumerate(phases)
    }
    width = 1260
    legend_lines = max(1, math.ceil(sum(45 + len(phase) * 7 for phase in phases) / 1120))
    top = 102.0 + legend_lines * 24
    row_height = 31.0
    height = int(top + len(keys) * row_height + 72)
    left, right = 300.0, 42.0
    chart_width = width - left - right
    elements = svg_open(
        width,
        height,
        "Crush phase-time breakdown",
        "Share of measured Crush phase time by corpus and execution lane.",
    )
    elements.append(text(42, 42, "Crush phase-time breakdown", "title"))
    elements.append(
        text(
            42,
            66,
            "Share of profiler-accounted time; each bar totals 100%",
            "subtitle",
        )
    )
    draw_legend(
        elements,
        [(phase, phase_colors[phase]) for phase in phases],
        42,
        98,
        width - 84,
    )

    for value in (0, 25, 50, 75, 100):
        x = left + chart_width * value / 100.0
        elements.append(line(x, top - 8, x, top + len(keys) * row_height, "grid"))
        elements.append(text(x, top - 14, f"{value}%", "axis", "middle"))

    for index, key in enumerate(keys):
        y = top + index * row_height
        suite, lane = key
        phase_rows = grouped[key]
        total = sum(float(row["total_ms"]) for row in phase_rows)
        cursor = left
        by_phase = {row["phase"]: row for row in phase_rows}
        for phase in phases:
            row = by_phase.get(phase)
            if row is None or total == 0:
                continue
            percentage = 100.0 * float(row["total_ms"]) / total
            segment_width = chart_width * percentage / 100.0
            elements.append(rect(cursor, y + 4, segment_width, 20, phase_colors[phase]))
            if segment_width >= 42:
                elements.append(
                    text(
                        cursor + segment_width / 2,
                        y + 18,
                        f"{percentage:.0f}%",
                        "value",
                        "middle",
                    )
                )
            cursor += segment_width
        elements.append(
            text(left - 14, y + 19, f"{suite} / {label_lane(lane)}", "label", "end")
        )
    write_svg(path, elements)


def linear_fit(
    xs: list[float], ys: list[float]
) -> Optional[tuple[float, float, float]]:
    if len(xs) < 2 or len(xs) != len(ys):
        return None
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    variance_x = sum((value - mean_x) ** 2 for value in xs)
    variance_y = sum((value - mean_y) ** 2 for value in ys)
    if variance_x == 0 or variance_y == 0:
        return None
    covariance = sum(
        (x_value - mean_x) * (y_value - mean_y)
        for x_value, y_value in zip(xs, ys)
    )
    slope = covariance / variance_x
    correlation = covariance / math.sqrt(variance_x * variance_y)
    return correlation, slope, mean_y - slope * mean_x


def averaged_scaling(
    rows: list[dict[str, str]],
) -> dict[str, list[tuple[str, float, float, float]]]:
    samples: dict[tuple[str, str], list[tuple[float, float, float]]] = defaultdict(list)
    for row in rows:
        if row["lane"] != "crush-alethe":
            continue
        samples[(row["suite"], row["vc_key"])].append(
            (
                float(row["commands"]),
                float(row["certificate_bytes"]),
                float(row["replay_ms"]),
            )
        )
    grouped: dict[str, list[tuple[str, float, float, float]]] = defaultdict(list)
    for (suite, vc_key), values in samples.items():
        count = len(values)
        grouped[suite].append(
            (
                vc_key,
                sum(value[0] for value in values) / count,
                sum(value[1] for value in values) / count,
                sum(value[2] for value in values) / count,
            )
        )
    for values in grouped.values():
        values.sort(key=lambda value: (value[1], value[0]))
    return grouped


def plot_scaling(
    rows: list[dict[str, str]], path: Path, replay_axis: str
) -> None:
    grouped = averaged_scaling(rows)
    suites = sorted(grouped)
    width = 1120
    panel_height = 330
    height = 94 + len(suites) * panel_height + 28
    elements = svg_open(
        width,
        height,
        "Alethe replay scaling",
        "Replay time compared with parsed Alethe command count for successful replays.",
    )
    elements.append(text(42, 42, "Alethe replay scaling", "title"))
    axis_note = "logarithmic replay-time axis" if replay_axis == "log" else "linear axes"
    elements.append(
        text(
            42,
            66,
            f"Successful strict Alethe replays, averaged per VC; {axis_note}",
            "subtitle",
        )
    )
    left, right = 100.0, 52.0
    chart_width = width - left - right

    for panel_index, suite in enumerate(suites):
        values = grouped[suite]
        panel_top = 94.0 + panel_index * panel_height
        chart_top = panel_top + 38
        chart_height = 225.0
        chart_bottom = chart_top + chart_height
        xs = [value[1] for value in values]
        ys = [value[3] for value in values]
        x_max = max(xs) if xs else 1.0
        x_max = max(1.0, math.ceil(x_max / 50.0) * 50.0)
        positive_ys = [value for value in ys if value > 0]
        if replay_axis == "log":
            min_power = math.floor(math.log10(min(positive_ys))) if positive_ys else 0
            max_power = math.ceil(math.log10(max(positive_ys))) if positive_ys else 1
            if min_power == max_power:
                max_power += 1

            def map_y(value: float) -> float:
                safe_value = max(value, 10.0**min_power)
                ratio = (math.log10(safe_value) - min_power) / (max_power - min_power)
                return chart_bottom - chart_height * ratio

            y_ticks = [(10.0**power, f"10^{power}") for power in range(min_power, max_power + 1)]
        else:
            y_max = max(ys) if ys else 1.0
            y_max = max(1.0, y_max * 1.08)

            def map_y(value: float) -> float:
                return chart_bottom - chart_height * value / y_max

            y_ticks = [(y_max * index / 4, f"{y_max * index / 4:.0f}") for index in range(5)]

        def map_x(value: float) -> float:
            return left + chart_width * value / x_max

        fit = linear_fit(xs, ys)
        fit_label = "fit unavailable"
        if fit is not None:
            correlation, slope, intercept = fit
            fit_label = (
                f"n={len(values)}, r={correlation:.3f}, "
                f"R2={correlation * correlation:.3f}, "
                f"slope={slope * 100:.1f} ms / 100 commands"
            )
            start_x = max(0.0, -intercept / slope) if slope > 0 else 0.0
            start_x = min(start_x, x_max)
            end_x = x_max
            start_y = max(10.0**min_power if replay_axis == "log" else 0.0, intercept + slope * start_x)
            end_y = max(10.0**min_power if replay_axis == "log" else 0.0, intercept + slope * end_x)
            elements.append(
                line(
                    map_x(start_x),
                    map_y(start_y),
                    map_x(end_x),
                    map_y(end_y),
                    stroke=LANE_COLORS["crush-alethe"],
                    dash="7 5",
                )
            )
        elements.append(text(left, panel_top + 18, suite, "label"))
        elements.append(text(left + 90, panel_top + 18, fit_label, "subtitle"))

        for tick_index in range(6):
            value = x_max * tick_index / 5
            x = map_x(value)
            elements.append(line(x, chart_top, x, chart_bottom, "grid"))
            elements.append(text(x, chart_bottom + 20, f"{value:.0f}", "axis", "middle"))
        for value, label in y_ticks:
            y = map_y(value)
            elements.append(line(left, y, width - right, y, "grid"))
            elements.append(text(left - 12, y + 4, label, "axis", "end"))
        elements.append(line(left, chart_bottom, width - right, chart_bottom, "axis-line"))
        elements.append(line(left, chart_top, left, chart_bottom, "axis-line"))
        elements.append(
            text(width / 2, chart_bottom + 43, "Parsed Alethe commands", "axis", "middle")
        )
        y_label = "Replay time (ms, log10)" if replay_axis == "log" else "Replay time (ms)"
        elements.append(
            text(
                31,
                chart_top + chart_height / 2,
                y_label,
                "axis",
                "middle",
                f"rotate(-90 31 {chart_top + chart_height / 2:.2f})",
            )
        )
        for vc_key, commands, certificate_bytes, replay_ms in values:
            tooltip = (
                f"{vc_key}: {commands:.0f} commands, "
                f"{certificate_bytes:.0f} bytes, {replay_ms:.3f} ms"
            )
            elements.append(
                circle(
                    map_x(commands),
                    map_y(replay_ms),
                    5.2,
                    LANE_COLORS["crush-alethe"],
                    tooltip,
                )
            )
    write_svg(path, elements)


def scaling_summary_rows(
    scaling_rows: list[dict[str, str]],
) -> list[list[object]]:
    grouped = averaged_scaling(scaling_rows)
    output: list[list[object]] = []
    for suite, values in sorted(grouped.items()):
        xs = [value[1] for value in values]
        ys = [value[3] for value in values]
        fit = linear_fit(xs, ys)
        if fit is None:
            correlation = r_squared = slope = "-"
        else:
            raw_correlation, raw_slope, _ = fit
            correlation = f"{raw_correlation:.4f}"
            r_squared = f"{raw_correlation * raw_correlation:.4f}"
            slope = f"{raw_slope * 100:.3f}"
        output.append(
            [
                suite,
                len(values),
                f"{min(xs):.0f}-{max(xs):.0f}",
                f"{min(ys):.3f}-{max(ys):.3f}",
                correlation,
                r_squared,
                slope,
            ]
        )
    return output


def write_tables(
    path: Path,
    result_dirs: list[Path],
    headline: list[dict[str, str]],
    outcomes: list[dict[str, str]],
    comparisons: list[dict[str, str]],
    coverage: list[dict[str, str]],
    reconstruction: list[dict[str, str]],
    failures: list[dict[str, str]],
    phases: list[dict[str, str]],
    scaling: list[dict[str, str]],
) -> None:
    with path.open("w", encoding="utf-8") as stream:
        stream.write("# Benchmark Tables\n\n")
        stream.write("Generated from:\n\n")
        for result_dir in result_dirs:
            stream.write(f"- `{result_dir}`\n")
        if headline:
            stream.write("\n## Backend Comparison\n\n")
            stream.write(
                "Each corpus has one fixed total for every backend. "
                "`Crush` is the `crush-verify` lane, which trusts the SMT "
                "verdict and does not reconstruct a Lean proof. `Attempted` "
                "counts VCs with a complete backend record; `Failed` counts "
                "attempted but unsolved VCs; and `Missing` counts corpus VCs "
                "without a complete attempt record. Missing VCs count as "
                "unsolved for coverage and are excluded from timing "
                "statistics.\n\n"
            )
            write_markdown_table(
                stream,
                [
                    "Corpus",
                    "Backend",
                    "Lane",
                    "Solved / total",
                    "Attempted",
                    "Failed",
                    "Missing",
                    "Coverage",
                    "Total (ms)",
                    "Mean (ms)",
                    "Min (ms)",
                    "Max (ms)",
                ],
                (
                    [
                        row["suite"],
                        label_backend(row["backend"]),
                        label_lane(row["lane"]),
                        f'{row["solved_vcs"]} / {row["total_vcs"]}',
                        row["attempted_vcs"],
                        row["failed_vcs"],
                        row["missing_vcs"],
                        f'{row["pass_pct"]}%',
                        row["total_ms"],
                        row["mean_ms"],
                        row["min_ms"],
                        row["max_ms"],
                    ]
                    for row in sorted(
                        headline,
                        key=lambda item: (
                            item["suite"],
                            ("auto", "duper", "crush", "grind").index(
                                item["backend"]
                            ),
                        ),
                    )
                ),
            )
        if outcomes:
            stream.write("## Verification Outcomes\n\n")
            stream.write(
                "The four outcome columns partition each backend's fixed "
                "corpus workload. `Translation error` means the backend "
                "explicitly rejected an unsupported translation or encoding. "
                "`Timeout` requires an explicit wall-clock, heartbeat, or "
                "saturation-limit diagnostic. `Failed to prove` contains all "
                "other unsuccessful attempts, including solver `sat` or "
                "`unknown`, exhausted proof search, and ordinary tactic "
                "errors.\n\n"
            )
            write_markdown_table(
                stream,
                [
                    "Corpus",
                    "Backend",
                    "Total",
                    "Success",
                    "Translation error",
                    "Timeout",
                    "Failed to prove",
                ],
                (
                    [
                        row["suite"],
                        label_backend(row["backend"]),
                        row["total_vcs"],
                        row["success"],
                        row["translation_error"],
                        row["timeout"],
                        row["failed_to_prove"],
                    ]
                    for row in sorted(
                        outcomes,
                        key=lambda item: (
                            item["suite"],
                            ("auto", "duper", "crush", "grind").index(
                                item["backend"]
                            ),
                        ),
                    )
                ),
            )
        if comparisons:
            stream.write("## Pairwise Matched VCs\n\n")
            stream.write(
                "`Matched` counts exact VC identities attempted by both the "
                "named baseline and Crush. The four outcome columns partition "
                "that matched set. Timing means include only VCs solved by "
                "both lanes, so failures do not create artificial speedups. "
                "Rows compare Crush with one baseline; baselines are not "
                "compared with each other.\n\n"
            )
            write_markdown_table(
                stream,
                [
                    "Corpus",
                    "Baseline",
                    "Baseline lane",
                    "Crush lane",
                    "Matched",
                    "Baseline only",
                    "Crush only",
                    "Both",
                    "Neither",
                    "Baseline mean (ms)",
                    "Crush mean (ms)",
                ],
                (
                    [
                        row["suite"],
                        label_backend(row["baseline"]),
                        label_lane(row["baseline_lane"]),
                        label_lane(row["crush_lane"]),
                        row["matched_vcs"],
                        row["baseline_only_solved"],
                        row["crush_only_solved"],
                        row["both_solved"],
                        row["neither_solved"],
                        row["baseline_mean_ms"],
                        row["crush_mean_ms"],
                    ]
                    for row in sorted(
                        comparisons,
                        key=lambda item: (item["suite"], item["baseline"]),
                    )
                ),
            )
        if coverage and not headline:
            stream.write("\n## Verification Coverage\n\n")
            stream.write(
                "`Total` is the fixed number of VC occurrences in the corpus. "
                "`Attempted` counts VCs with a complete backend record; `Failed` "
                "counts attempted but unsolved VCs; and `Missing` counts corpus "
                "VCs without a complete attempt record. Missing VCs count as "
                "unsolved for coverage and are excluded from timing "
                "statistics.\n\n"
            )
            write_markdown_table(
                stream,
                [
                    "Corpus",
                    "Lane",
                    "Solved / total",
                    "Attempted",
                    "Failed",
                    "Missing",
                    "Coverage",
                    "Total (ms)",
                    "Mean (ms)",
                ],
                (
                    [
                        row["suite"],
                        label_lane(row["lane"]),
                        (
                            f'{row["solved_vcs"]} / '
                            f'{row.get("total_vcs", row["attempted_vcs"])}'
                        ),
                        row["attempted_vcs"],
                        row["failed_vcs"],
                        row.get("missing_vcs", "0"),
                        f'{row["pass_pct"]}%',
                        row["total_ms"],
                        row["mean_ms"],
                    ]
                    for row in sorted(
                        coverage,
                        key=lambda item: (
                            item["suite"],
                            lane_sort_key(item["lane"]),
                        ),
                    )
                ),
            )
        if reconstruction:
            stream.write("## Proof Reconstruction\n\n")
            write_markdown_table(
                stream,
                [
                    "Corpus",
                    "SMT verified / total",
                    "Core / verified",
                    "Alethe / verified",
                    "Portfolio / verified",
                ],
                (
                    [
                        row["suite"],
                        f'{row["verified_vcs"]} / {row["total_vcs"]}',
                        f'{row["core_reconstructed"]} / {row["verified_vcs"]}',
                        f'{row["alethe_reconstructed"]} / {row["verified_vcs"]}',
                        f'{row["portfolio_reconstructed"]} / {row["verified_vcs"]}',
                    ]
                    for row in sorted(
                        reconstruction, key=lambda item: item["suite"]
                    )
                ),
            )
        if failures:
            stream.write("## Reconstruction Failures\n\n")
            write_markdown_table(
                stream,
                ["Corpus", "Lane", "Failure mode", "VCs"],
                (
                    [
                        row["suite"],
                        label_lane(row["lane"]),
                        row["failure_mode"],
                        row["vcs"],
                    ]
                    for row in sorted(
                        failures,
                        key=lambda item: (
                            item["suite"],
                            lane_sort_key(item["lane"]),
                            item["failure_mode"],
                        ),
                    )
                ),
            )
        if phases:
            stream.write("## Crush Phase Breakdown\n\n")
            write_markdown_table(
                stream,
                ["Corpus", "Lane", "Phase", "Events", "Total (ms)", "Share"],
                (
                    [
                        row["suite"],
                        label_lane(row["lane"]),
                        row["phase"],
                        row["events"],
                        row["total_ms"],
                        f'{row["phase_pct"]}%',
                    ]
                    for row in sorted(
                        phases,
                        key=lambda item: (
                            item["suite"],
                            lane_sort_key(item["lane"]),
                            item["phase"],
                        ),
                    )
                ),
            )
        scaling_rows = scaling_summary_rows(scaling)
        if scaling_rows:
            stream.write("## Alethe Replay Scaling\n\n")
            write_markdown_table(
                stream,
                [
                    "Corpus",
                    "VCs",
                    "Command range",
                    "Replay range (ms)",
                    "Pearson r",
                    "R2",
                    "ms / 100 commands",
                ],
                scaling_rows,
            )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Render normalized lean-crush benchmark reports as tables and SVG figures."
    )
    parser.add_argument(
        "result_dirs",
        nargs="+",
        type=Path,
        help="benchmark result directories containing normalized TSV reports",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("BenchmarkResults/figures"),
        help="destination directory (default: BenchmarkResults/figures)",
    )
    parser.add_argument(
        "--replay-axis",
        choices=("log", "linear"),
        default="log",
        help="Alethe replay-time axis (default: log)",
    )
    parser.add_argument(
        "--skip-tables",
        action="store_true",
        help="write SVG figures without tables.md",
    )
    parser.add_argument(
        "--only",
        action="append",
        choices=OUTPUTS,
        help="generate only this output; repeat to select multiple outputs",
    )
    args = parser.parse_args()

    missing = [path for path in args.result_dirs if not path.is_dir()]
    if missing:
        raise SystemExit(f"result directory does not exist: {missing[0]}")

    selected = set(args.only or OUTPUTS)
    if args.skip_tables:
        selected.discard("tables")

    need_tables = "tables" in selected
    need_coverage = need_tables or "coverage" in selected
    need_outcomes = need_tables or "outcomes" in selected
    need_reconstruction = (
        need_tables
        or "reconstruction" in selected
        or "reconstruction-failures" in selected
    )
    need_failures = need_tables or "reconstruction-failures" in selected
    need_phases = need_tables or "phase-breakdown" in selected
    need_scaling = need_tables or "alethe-replay-scaling" in selected

    headline = (
        unique_rows(
            read_tsv(args.result_dirs, "headline-summary.tsv"),
            ("suite", "backend"),
            "headline-summary.tsv",
        )
        if need_coverage
        else []
    )
    coverage = (
        unique_rows(
            read_tsv(args.result_dirs, "coverage-summary.tsv"),
            ("suite", "lane"),
            "coverage-summary.tsv",
        )
        if need_tables or (need_coverage and not headline)
        else []
    )
    outcomes = (
        unique_rows(
            read_tsv(args.result_dirs, "headline-outcomes.tsv"),
            ("suite", "backend"),
            "headline-outcomes.tsv",
        )
        if need_outcomes
        else []
    )
    comparisons = (
        unique_rows(
            rows_with_columns(
                read_tsv(args.result_dirs, "comparison.tsv"),
                ("suite", "baseline", "baseline_lane", "crush_lane"),
            ),
            ("suite", "baseline"),
            "comparison.tsv",
        )
        if need_tables
        else []
    )
    reconstruction = (
        unique_rows(
            read_tsv(args.result_dirs, "reconstruction-summary.tsv"),
            ("suite",),
            "reconstruction-summary.tsv",
        )
        if need_reconstruction
        else []
    )
    failures = (
        unique_rows(
            read_tsv(args.result_dirs, "reconstruction-failures.tsv"),
            ("suite", "lane", "failure_mode"),
            "reconstruction-failures.tsv",
        )
        if need_failures
        else []
    )
    phases = (
        unique_rows(
            read_tsv(args.result_dirs, "phase-summary.tsv"),
            ("suite", "lane", "phase"),
            "phase-summary.tsv",
        )
        if need_phases
        else []
    )
    scaling = (
        read_tsv(args.result_dirs, "alethe-replay-scaling.tsv")
        if need_scaling
        else []
    )

    if not any(
        (
            headline,
            outcomes,
            comparisons,
            coverage,
            reconstruction,
            failures,
            phases,
            scaling,
        )
    ):
        raise SystemExit("no normalized benchmark reports found")

    args.out_dir.mkdir(parents=True, exist_ok=True)
    generated: list[Path] = []
    if "tables" in selected:
        write_tables(
            args.out_dir / "tables.md",
            args.result_dirs,
            headline,
            outcomes,
            comparisons,
            coverage,
            reconstruction,
            failures,
            phases,
            scaling,
        )
        generated.append(args.out_dir / "tables.md")
    coverage_plot_rows = headline or coverage
    if "coverage" in selected and coverage_plot_rows:
        path = args.out_dir / "coverage.svg"
        plot_coverage(coverage_plot_rows, path)
        generated.append(path)
    if "outcomes" in selected and outcomes:
        path = args.out_dir / "outcomes.svg"
        plot_outcomes(outcomes, path)
        generated.append(path)
    if "reconstruction" in selected and reconstruction:
        path = args.out_dir / "reconstruction.svg"
        plot_reconstruction(reconstruction, path)
        generated.append(path)
    if "reconstruction-failures" in selected and reconstruction:
        path = args.out_dir / "reconstruction-failures.svg"
        plot_failures(failures, reconstruction, path)
        generated.append(path)
    if "phase-breakdown" in selected and phases:
        path = args.out_dir / "phase-breakdown.svg"
        plot_phases(phases, path)
        generated.append(path)
    if (
        "alethe-replay-scaling" in selected
        and scaling
        and averaged_scaling(scaling)
    ):
        path = args.out_dir / "alethe-replay-scaling.svg"
        plot_scaling(scaling, path, args.replay_axis)
        generated.append(path)
    for path in generated:
        print(path)


if __name__ == "__main__":
    main()
