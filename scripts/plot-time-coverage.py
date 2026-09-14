#!/usr/bin/env python3

"""Draw time-versus-coverage curves for the benchmark comparisons.

Two figures, both with tactic-local time on the x axis in seconds:

* `coverage-over-time` plots closed VCs for the main comparison's headline
  backends, including lean-smt where its lane ran.
* `reconstruction-over-time` plots VCs closed with a kernel-checked Lean proof
  for the reconstruction comparison's lanes.

Unlike `plot-benchmarks.py`, which hand-writes SVG with only the standard
library, this script needs matplotlib. It reuses the other scripts' cohort
predicates and palette so a curve's final height equals the corresponding
count in `headline-summary.tsv` or `reconstruction-comparison.tsv`; both are
checked before anything is written.
"""

import argparse
import csv
import importlib.util
import sys
from collections import defaultdict
from pathlib import Path
from types import ModuleType


csv.field_size_limit(sys.maxsize)

# The sibling scripts are loaded by path below. Keep that from leaving a
# __pycache__ directory in the source tree.
sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent

# Times are recorded in whole milliseconds, so a sub-millisecond attempt is
# stored as 0 and has no position on a logarithmic axis. Draw those at the
# measurement resolution instead of dropping them.
RESOLUTION_SECONDS = 1e-3

# Crush and its reconstruction portfolio are the subject of every comparison,
# so they are drawn wider, last, and with a white halo that keeps them legible
# where several curves plateau on top of one another. The other series are
# slightly thinner and marginally translucent so the emphasis reads without
# resorting to dash patterns, which proved hard to tell apart.
EMPHASIS = frozenset({"crush", "crush-portfolio"})


def legend_order(keys: list[str]) -> list[int]:
    """Indices that put the emphasised curves last in the legend.

    Crush is the subject of every comparison, so it reads at the bottom of the
    legend even though it is drawn on top of the baselines. Sorting is stable,
    so the baselines keep their existing order among themselves.
    """
    return sorted(range(len(keys)), key=lambda index: keys[index] in EMPHASIS)
OUTPUTS = (
    "main",
    "reconstruction",
    "scaling",
    "coverage-table",
    "reconstruction-table",
)


def load_script(name: str, filename: str) -> ModuleType:
    """Import a sibling script whose filename is not a valid module name."""
    path = HERE / filename
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


report = load_script("benchmark_report", "benchmark-report.py")
style = load_script("plot_benchmarks", "plot-benchmarks.py")


def require_matplotlib():
    try:
        import matplotlib
    except ModuleNotFoundError:
        raise SystemExit(
            "this figure needs matplotlib: pip install matplotlib\n"
            "plot-benchmarks.py renders the other figures with only the "
            "standard library"
        )
    matplotlib.use("Agg")
    import matplotlib.pyplot as pyplot

    return pyplot


EXCLUDED_SUITES: set[str] = set()


def read_tsv(result_dirs: list[Path], filename: str) -> list[dict[str, str]]:
    """Read one report across the result directories, minus omitted suites."""
    return style.drop_suites(
        style.read_tsv(result_dirs, filename), EXCLUDED_SUITES
    )


def solved_times(
    rows_by_vc: dict[str, list[dict[str, str]]], solved: set[str]
) -> list[float]:
    """Per-VC seconds for the solved VCs, ascending.

    Repeats of one VC are averaged before sorting, so a repeated run does not
    weight one obligation more than the others.
    """
    return sorted(
        report.mean_milliseconds(rows_by_vc[vc]) / 1000.0 for vc in solved
    )


def curve(times: list[float], mode: str) -> tuple[list[float], list[int]]:
    """Turn per-VC times into the step positions for one series.

    `per-vc` reads as "given this much time for each VC, how many close",
    which matches the harness giving every VC its own independent budget.
    `cumulative` reads as "how much total time to close this many", so its x
    axis is the running sum instead.
    """
    xs: list[float] = []
    running = 0.0
    for seconds in times:
        if mode == "cumulative":
            running += seconds
            xs.append(running)
        else:
            xs.append(seconds)
    return xs, list(range(1, len(xs) + 1))


def main_series(
    result_dirs: list[Path],
) -> tuple[dict[str, list[dict[str, object]]], dict[str, int]]:
    """One series per headline backend, grouped by suite.

    The headline report already decided which lane represents each backend,
    so read that rather than re-deriving it here.
    """
    headline = read_tsv(result_dirs, "headline-summary.tsv")
    measurements = read_tsv(result_dirs, "measurements.tsv")
    attempts = report.grouped_attempts(measurements)

    rows_by_lane: dict[tuple[str, str], dict[str, list[dict[str, str]]]]
    rows_by_lane = defaultdict(dict)
    for (suite, lane, vc), rows in attempts.items():
        rows_by_lane[(suite, lane)][vc] = rows

    series: dict[str, list[dict[str, object]]] = defaultdict(list)
    totals: dict[str, int] = {}
    for row in sorted(
        headline,
        key=lambda item: (
            style.suite_sort_key(item["suite"]),
            style.backend_sort_key(item["backend"]),
        ),
    ):
        suite = row["suite"]
        lane = row["lane"]
        rows_by_vc = rows_by_lane.get((suite, lane))
        if not rows_by_vc:
            continue
        solved = {vc for vc, rows in rows_by_vc.items() if report.all_pass(rows)}
        expected = int(row["solved_vcs"])
        if len(solved) != expected:
            raise SystemExit(
                f"{suite} / {row['backend']}: measurements.tsv has "
                f"{len(solved)} solved VCs but headline-summary.tsv reports "
                f"{expected}; pass matching result directories"
            )
        totals[suite] = int(row["total_vcs"])
        series[suite].append(
            {
                "key": row["backend"],
                "label": style.label_backend(row["backend"]),
                "color": style.BACKEND_COLORS.get(row["backend"], "#66736F"),
                "times": solved_times(rows_by_vc, solved),
            }
        )
    return series, totals


def reconstruction_series(
    result_dirs: list[Path],
) -> tuple[dict[str, list[dict[str, object]]], dict[str, int]]:
    """One series per compared reconstruction lane, grouped by suite.

    Success is `checked_proof_succeeded`, the same predicate behind the
    comparison table, so a goal closed by checked pre-SMT reconstruction
    counts and a trusted verdict does not.
    """
    comparison = read_tsv(result_dirs, "reconstruction-comparison.tsv")
    if not comparison:
        return {}, {}
    measurements = read_tsv(result_dirs, "measurements.tsv")
    profiles = read_tsv(result_dirs, "profile-events.tsv")
    attempts = report.grouped_attempts(measurements)
    profile_groups = report.profiles_by_vc(profiles)
    cohorts = {
        suite: cohort
        for suite, cohort in report.reconstruction_comparison_cohort(
            attempts
        ).items()
        if suite not in EXCLUDED_SUITES
    }

    expected = {
        (row["suite"], row["lane"]): int(row["checked_proof_vcs"])
        for row in comparison
    }
    series: dict[str, list[dict[str, object]]] = defaultdict(list)
    totals: dict[str, int] = {}
    for suite in sorted(cohorts, key=style.suite_sort_key):
        lanes, by_lane, matched = cohorts[suite]
        totals[suite] = len(matched)
        for lane in sorted(lanes, key=style.lane_sort_key):
            solved = {
                vc
                for vc in matched
                if report.checked_proof_succeeded(
                    by_lane[lane][vc],
                    profile_groups.get((suite, lane, vc), []),
                )
            }
            recorded = expected.get((suite, lane))
            if recorded is not None and len(solved) != recorded:
                raise SystemExit(
                    f"{suite} / {lane}: recomputed {len(solved)} checked "
                    f"proofs but reconstruction-comparison.tsv reports "
                    f"{recorded}; pass matching result directories"
                )
            series[suite].append(
                {
                    "key": lane,
                    "label": style.label_lane(lane),
                    "color": style.LANE_COLORS.get(lane, "#66736F"),
                    "times": solved_times(by_lane[lane], solved),
                }
            )
    return series, totals


def scaling_series(
    result_dirs: list[Path],
) -> dict[str, list[tuple[float, float]]]:
    """Per-suite (parsed Alethe commands, replay ms) samples.

    Averaged per VC by the same helper the table uses, so the figure and the
    Alethe Replay Scaling table describe the same samples.
    """
    rows = read_tsv(result_dirs, "alethe-replay-scaling.tsv")
    grouped = style.averaged_scaling(rows)
    return {
        suite: [(commands, replay_ms) for _, commands, _, replay_ms in values]
        for suite, values in grouped.items()
        if suite not in EXCLUDED_SUITES
    }


def draw_scaling_suite(
    pyplot,
    path: Path,
    suite: str,
    samples: list[tuple[float, float]],
    time_axis: str,
) -> None:
    from matplotlib.ticker import LogFormatterSciNotation

    figure, axis = pyplot.subplots(figsize=SQUARE_SIZE)
    figure.patch.set_facecolor(style.PAPER)
    axis.set_facecolor(style.PAPER)
    for spine in ("top", "right"):
        axis.spines[spine].set_visible(False)
    for spine in ("left", "bottom"):
        axis.spines[spine].set_color(style.GRID)
    axis.tick_params(colors=style.MUTED, labelsize=10)
    axis.grid(True, color=style.GRID, linewidth=0.7, alpha=0.9)
    axis.set_axisbelow(True)

    axis.scatter(
        [x for x, _ in samples],
        [y for _, y in samples],
        s=34,
        color=style.LANE_COLORS["crush-alethe"],
        edgecolor=style.PAPER,
        linewidth=0.8,
        zorder=3,
    )
    if time_axis == "log":
        axis.set_yscale("log")
        # Mathtext powers of ten rather than 10^4 spelled out.
        axis.yaxis.set_major_formatter(LogFormatterSciNotation())
    # Say what the count is: these are the VCs whose Alethe certificate was
    # actually parsed and replayed, not the VCs the lane closed. The lane also
    # closes goals by pre-reconstruction or a selected fact, which parse no
    # certificate and so have no command count to plot.
    axis.set_title(
        f"{style.label_suite(suite)} — {len(samples)} replayed certificates",
        color=style.INK,
        fontsize=12,
        pad=8,
    )
    axis.set_xlabel("Parsed Alethe commands", color=style.MUTED, fontsize=10)
    axis.set_ylabel("Replay time (ms)", color=style.MUTED, fontsize=10)
    figure.tight_layout()
    figure.savefig(path, facecolor=figure.get_facecolor())
    pyplot.close(figure)


def median_of(values: list[float]) -> float:
    ordered = sorted(values)
    count = len(ordered)
    if not count:
        return 0.0
    middle = count // 2
    if count % 2:
        return ordered[middle]
    return (ordered[middle - 1] + ordered[middle]) / 2


def coverage_table_rows(
    result_dirs: list[Path],
) -> list[tuple[str, int, list[tuple[str, int, float, float]]]]:
    """Per-suite coverage grouped for a multirow table.

    Returns (suite, total VCs, [(tool, proved, coverage pct, median ms)]).
    The median comes from measurements.tsv rather than the mean in
    headline-summary.tsv: one pathological VC moves a mean by orders of
    magnitude and the median states what a typical VC costs.
    """
    headline = read_tsv(result_dirs, "headline-summary.tsv")
    measurements = read_tsv(result_dirs, "measurements.tsv")
    attempts = report.grouped_attempts(measurements)

    solved_ms: dict[tuple[str, str], list[float]] = defaultdict(list)
    for (suite, lane, _vc), rows in attempts.items():
        if not report.all_pass(rows):
            continue
        solved_ms[(suite, lane)].append(
            report.mean_milliseconds(rows)
        )

    grouped: dict[str, list[tuple[str, int, float, float]]] = defaultdict(list)
    totals: dict[str, int] = {}
    for row in sorted(
        headline,
        key=lambda item: (
            style.suite_sort_key(item["suite"]),
            style.backend_sort_key(item["backend"]),
        ),
    ):
        suite = row["suite"]
        if suite in EXCLUDED_SUITES:
            continue
        totals[suite] = int(row["total_vcs"])
        grouped[suite].append(
            (
                style.label_backend(row["backend"]),
                int(row["solved_vcs"]),
                float(row["pass_pct"]),
                median_of(solved_ms.get((suite, row["lane"]), [])),
            )
        )
    return [
        (suite, totals[suite], grouped[suite])
        for suite in sorted(grouped, key=style.suite_sort_key)
    ]


def draw_table(
    pyplot,
    path: Path,
    header: tuple[str, ...],
    columns: tuple[float, ...],
    aligns: tuple[str, ...],
    groups: list[tuple[str, str, list[tuple[tuple[str, ...], tuple[str, ...]]]]],
    width: float = 6.4,
) -> None:
    """A multirow table: the first column spans each group's rows.

    `groups` is (label, sublabel, rows) and each row is (cells, weights) with
    one entry per column after the spanning one. Drawn with matplotlib rather
    than emitted as markdown so it shares the figures' typeface.
    """
    body_rows = sum(len(rows) for _, _, rows in groups)
    row_height = 0.30
    height = 0.62 + body_rows * row_height
    figure = pyplot.figure(figsize=(width, height))
    figure.patch.set_facecolor(style.PAPER)
    axis = figure.add_axes((0, 0, 1, 1))
    axis.set_facecolor(style.PAPER)
    axis.set_xlim(0, 1)
    axis.set_ylim(0, 1)
    axis.axis("off")

    top = 1 - 0.34 / height
    step = row_height / height
    for x, label, align in zip(columns, header, aligns):
        axis.text(
            x, top, label, ha=align, va="center",
            fontsize=10, fontweight="bold", color=style.INK,
        )
    rule = top - step * 0.55
    axis.plot([0, 1], [rule, rule], color=style.INK, linewidth=1.1)

    row = 0
    for index, (label, sublabel, rows) in enumerate(groups):
        first = top - step * (row + 1.15)
        for offset, (cells, weights) in enumerate(rows):
            y = top - step * (row + 1.15 + offset)
            for x, value, align, weight in zip(
                columns[1:], cells, aligns[1:], weights
            ):
                axis.text(
                    x, y, value, ha=align, va="center",
                    fontsize=9.5, fontweight=weight, color=style.INK,
                )
        last = top - step * (row + 1.15 + len(rows) - 1)
        centre = (first + last) / 2
        axis.text(
            columns[0], centre, label, ha=aligns[0], va="center",
            fontsize=10, fontweight="bold", color=style.INK,
        )
        if sublabel:
            axis.text(
                columns[0], centre - step * 0.52, sublabel,
                ha=aligns[0], va="center", fontsize=8.5, color=style.MUTED,
            )
        row += len(rows)
        if index < len(groups) - 1:
            separator = top - step * (row + 0.65)
            axis.plot(
                [0, 1], [separator, separator],
                color=style.GRID, linewidth=0.8,
            )
    bottom = top - step * (row + 0.65)
    axis.plot([0, 1], [bottom, bottom], color=style.INK, linewidth=1.1)
    figure.savefig(path, facecolor=figure.get_facecolor())
    pyplot.close(figure)


def draw_coverage_table(
    pyplot,
    path: Path,
    groups: list[tuple[str, int, list[tuple[str, int, float, float]]]],
) -> None:
    rendered: list[tuple[str, str, list[tuple[tuple[str, ...], tuple[str, ...]]]]]
    rendered = []
    for suite, total, tools in groups:
        best = max(proved for _, proved, _, _ in tools)
        rows = []
        for tool, proved, pct, median_ms in tools:
            # Bold marks the most VCs proved, so it stops at the coverage
            # column: median time is a different question and grind, not
            # Crush, is usually fastest.
            weight = "bold" if proved == best else "normal"
            rows.append(
                (
                    (tool, f"{proved}", f"{pct:.1f}%", f"{median_ms:,.1f}"),
                    (weight, weight, weight, "normal"),
                )
            )
        rendered.append((style.label_suite(suite), f"{total} VCs", rows))
    draw_table(
        pyplot,
        path,
        ("Benchmark", "Tool", "#VC proved", "Coverage", "Median (ms)"),
        (0.015, 0.30, 0.62, 0.79, 0.985),
        ("left", "left", "right", "right", "right"),
        rendered,
    )


def reconstruction_table_rows(
    result_dirs: list[Path],
) -> list[tuple[str, int, int, list[tuple[str, int, float, int, int, float]]]]:
    """Per-suite reconstruction comparison grouped for a multirow table."""
    rows = read_tsv(result_dirs, "reconstruction-comparison.tsv")
    grouped: dict[str, list[tuple[str, int, float, int, int, float]]]
    grouped = defaultdict(list)
    matched: dict[str, int] = {}
    common: dict[str, int] = {}
    for row in sorted(
        rows,
        key=lambda item: (
            style.suite_sort_key(item["suite"]),
            style.lane_sort_key(item["lane"]),
        ),
    ):
        suite = row["suite"]
        if suite in EXCLUDED_SUITES:
            continue
        matched[suite] = int(row["matched_vcs"])
        common[suite] = int(row["common_checked_proof_vcs"])
        grouped[suite].append(
            (
                style.label_lane(row["lane"]),
                int(row["checked_proof_vcs"]),
                float(row["pass_pct"]),
                int(row["cohort_reconstructed_vcs"]),
                int(row["verify_smt_cohort_vcs"]),
                float(row["common_mean_ms"]),
            )
        )
    return [
        (suite, matched[suite], common[suite], grouped[suite])
        for suite in sorted(grouped, key=style.suite_sort_key)
    ]


def draw_reconstruction_table(
    pyplot,
    path: Path,
    groups: list[tuple[str, int, int, list[tuple[str, int, float, int, int, float]]]],
) -> None:
    rendered: list[tuple[str, str, list[tuple[tuple[str, ...], tuple[str, ...]]]]]
    rendered = []
    for suite, total, common, lanes in groups:
        best = max(proved for _, proved, _, _, _, _ in lanes)
        rows = []
        for lane, proved, pct, replayed, cohort, common_ms in lanes:
            weight = "bold" if proved == best else "normal"
            rows.append(
                (
                    (
                        lane,
                        f"{proved}",
                        f"{pct:.1f}%",
                        f"{replayed} / {cohort}",
                        f"{common_ms:,.1f}",
                    ),
                    (weight, weight, weight, "normal", "normal"),
                )
            )
        rendered.append(
            (
                style.label_suite(suite),
                f"{total} VCs \u00b7 {common} common",
                rows,
            )
        )
    draw_table(
        pyplot,
        path,
        (
            "Benchmark",
            "Tool",
            "Checked proof",
            "Coverage",
            "Replayed/Total",
            "Common (ms)",
        ),
        (0.012, 0.20, 0.50, 0.645, 0.83, 0.988),
        ("left", "left", "right", "right", "right", "right"),
        rendered,
        width=7.8,
    )


def write_points(
    path: Path,
    series: dict[str, list[dict[str, object]]],
    mode: str,
) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(["suite", "series", "rank", "seconds", "vcs"])
        for suite in series:
            for entry in series[suite]:
                xs, ys = curve(entry["times"], mode)
                for rank, (seconds, count) in enumerate(zip(xs, ys), start=1):
                    writer.writerow(
                        [suite, entry["key"], rank, f"{seconds:.6f}", count]
                    )


# One figure per corpus, all at the same size so they can be placed side by
# side in the paper without rescaling. Every figure carries its own legend,
# placed inside the axes rather than in the figure margin, which would
# otherwise make the geometry depend on the legend.
PANEL_SIZE = (6.4, 4.4)
EMPHASIS_WIDTH = 3.4
# The scaling figure is a scatter of two commensurate quantities, so it is
# drawn square rather than in the wide aspect the coverage curves use.
SQUARE_SIZE = (4.8, 4.8)
LINE_WIDTH = 2.2


def draw_suite(
    pyplot,
    path: Path,
    suite: str,
    entries: list[dict[str, object]],
    total: int | None,
    y_label: str,
    mode: str,
    time_axis: str,
) -> None:
    from matplotlib.patheffects import Stroke, Normal
    from matplotlib.ticker import MaxNLocator

    figure, axis = pyplot.subplots(figsize=PANEL_SIZE)
    figure.patch.set_facecolor(style.PAPER)
    axis.set_facecolor(style.PAPER)
    for spine in ("top", "right"):
        axis.spines[spine].set_visible(False)
    for spine in ("left", "bottom"):
        axis.spines[spine].set_color(style.GRID)
    axis.tick_params(colors=style.MUTED, labelsize=10)
    axis.grid(True, color=style.GRID, linewidth=0.7, alpha=0.9)
    axis.set_axisbelow(True)

    floor = RESOLUTION_SECONDS if time_axis == "log" else 0.0
    limit = max(
        (max(curve(entry["times"], mode)[0], default=floor) for entry in entries),
        default=floor,
    )
    limit = max(limit, floor) * (1.6 if time_axis == "log" else 1.05)

    handles: list[object] = []
    labels: list[str] = []
    keys: list[str] = []
    for entry in entries:
        xs, ys = curve(entry["times"], mode)
        if not xs:
            continue
        xs = [max(value, floor) for value in xs]
        emphasised = entry["key"] in EMPHASIS
        # Hold the final plateau to the panel edge, and start the step at the
        # left edge so the run-up from zero is visible.
        line = axis.step(
            [floor] + xs + [limit],
            [0] + ys + [ys[-1]],
            where="post",
            color=entry["color"],
            linewidth=EMPHASIS_WIDTH if emphasised else LINE_WIDTH,
            alpha=1.0 if emphasised else 0.85,
            zorder=5 if emphasised else 3,
            solid_joinstyle="round",
            solid_capstyle="round",
        )[0]
        if emphasised:
            line.set_path_effects(
                [Stroke(linewidth=EMPHASIS_WIDTH + 2.2, foreground=style.PAPER),
                 Normal()]
            )
        handles.append(line)
        labels.append(str(entry["label"]))
        keys.append(str(entry["key"]))

    # VC counts are whole numbers, so suppress fractional y ticks.
    axis.yaxis.set_major_locator(MaxNLocator(integer=True, nbins=6))
    if total:
        axis.axhline(total, color=style.MUTED, linewidth=1.0, linestyle=(0, (4, 3)))
        axis.set_ylim(0, total * 1.08)
    if time_axis == "log":
        axis.set_xscale("log")
    axis.set_xlim(floor, limit)
    axis.set_title(
        f"{style.label_suite(suite)}" + (f" — {total} VCs" if total else ""),
        color=style.INK,
        fontsize=12,
        pad=8,
    )
    axis.set_xlabel(
        "Time (s)"
        if mode == "cumulative"
        else "Time per VC (s)",
        color=style.MUTED,
        fontsize=10,
    )
    axis.set_ylabel(y_label, color=style.MUTED, fontsize=10)
    if handles:
        order = legend_order(keys)
        # The curves rise left to right, so the upper left is the free region.
        axis.legend(
            [handles[index] for index in order],
            [labels[index] for index in order],
            loc="upper left",
            frameon=False,
            fontsize=9.5,
            labelcolor=style.INK,
            handlelength=2.8,
            borderaxespad=0.4,
        )
    figure.tight_layout()
    figure.savefig(path, facecolor=figure.get_facecolor())
    pyplot.close(figure)


def draw(
    pyplot,
    out_dir: Path,
    stem: str,
    suffix: str,
    fmt: str,
    series: dict[str, list[dict[str, object]]],
    totals: dict[str, int],
    y_label: str,
    mode: str,
    time_axis: str,
) -> list[Path]:
    """Draw one figure per corpus and return the paths written."""
    written: list[Path] = []
    suites = sorted(series, key=style.suite_sort_key)
    for suite in suites:
        path = out_dir / f"{stem}-{suite}{suffix}.{fmt}"
        draw_suite(
            pyplot,
            path,
            suite,
            series[suite],
            totals.get(suite),
            y_label,
            mode,
            time_axis,
        )
        written.append(path)
    return written


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Draw closed and reconstructed VCs against tactic-local time for "
            "completed benchmark result directories."
        )
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
        "--only",
        action="append",
        choices=OUTPUTS,
        help="generate only this figure; repeat to select multiple figures",
    )
    parser.add_argument(
        "--mode",
        choices=("per-vc", "cumulative"),
        default="per-vc",
        help=(
            "per-vc: x is the time budget each VC is given (default). "
            "cumulative: x is the running total across VCs"
        ),
    )
    parser.add_argument(
        "--time-axis",
        choices=("log", "linear"),
        default="log",
        help="time axis scale (default: log)",
    )
    parser.add_argument(
        "--format",
        choices=("pdf", "svg", "png"),
        default="pdf",
        help="figure format (default: pdf)",
    )
    parser.add_argument(
        "--exclude-suite",
        action="append",
        default=[],
        metavar="SUITE",
        help=(
            "omit this corpus from the figures; repeat to omit several. The "
            "published figures omit "
            f"{', '.join(style.PAPER_EXCLUDED_SUITES)}."
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    missing = [path for path in args.result_dirs if not path.is_dir()]
    if missing:
        raise SystemExit(f"result directory does not exist: {missing[0]}")
    selected = set(args.only or OUTPUTS)
    EXCLUDED_SUITES.update(args.exclude_suite)
    pyplot = require_matplotlib()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    suffix = "" if args.mode == "per-vc" else "-cumulative"
    generated: list[Path] = []

    if "main" in selected:
        series, totals = main_series(args.result_dirs)
        if series:
            paths = draw(
                pyplot,
                args.out_dir,
                "coverage-over-time",
                suffix,
                args.format,
                series,
                totals,
                "VCs proved",
                args.mode,
                args.time_axis,
            )
            points = args.out_dir / f"coverage-over-time{suffix}.tsv"
            write_points(points, series, args.mode)
            generated.extend([*paths, points])

    if "reconstruction" in selected:
        series, totals = reconstruction_series(args.result_dirs)
        if series:
            paths = draw(
                pyplot,
                args.out_dir,
                "reconstruction-over-time",
                suffix,
                args.format,
                series,
                totals,
                "VCs reconstructed",
                args.mode,
                args.time_axis,
            )
            points = args.out_dir / f"reconstruction-over-time{suffix}.tsv"
            write_points(points, series, args.mode)
            generated.extend([*paths, points])

    if "scaling" in selected:
        samples = scaling_series(args.result_dirs)
        for suite in sorted(samples, key=style.suite_sort_key):
            if not samples[suite]:
                continue
            path = args.out_dir / f"alethe-replay-scaling-{suite}.{args.format}"
            draw_scaling_suite(
                pyplot, path, suite, samples[suite], args.time_axis
            )
            generated.append(path)

    if "coverage-table" in selected:
        groups = coverage_table_rows(args.result_dirs)
        if groups:
            path = args.out_dir / f"coverage-table.{args.format}"
            draw_coverage_table(pyplot, path, groups)
            generated.append(path)

    if "reconstruction-table" in selected:
        groups = reconstruction_table_rows(args.result_dirs)
        if groups:
            path = args.out_dir / f"reconstruction-table.{args.format}"
            draw_reconstruction_table(pyplot, path, groups)
            generated.append(path)

    if not generated:
        raise SystemExit(
            "no usable reports found; the main figure needs "
            "headline-summary.tsv, the reconstruction figure needs "
            "reconstruction-comparison.tsv, both alongside measurements.tsv, "
            "and the scaling figure needs alethe-replay-scaling.tsv"
            + (
                f" (omitting {', '.join(sorted(EXCLUDED_SUITES))})"
                if EXCLUDED_SUITES
                else ""
            )
        )
    for path in generated:
        print(path)


if __name__ == "__main__":
    main()
