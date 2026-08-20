#!/usr/bin/env python3

import argparse
import csv
import math
from collections import Counter, defaultdict
from pathlib import Path
from typing import Optional


RECONSTRUCTION_LANES = (
    "crush-core",
    "crush-alethe",
    "crush-portfolio",
)


def read_tsv(path: Path) -> list[dict[str, str]]:
    if not path.exists():
        return []
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def write_tsv(path: Path, columns: list[str], rows: list[list[object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(columns)
        writer.writerows(rows)


def grouped_attempts(
    measurements: list[dict[str, str]],
) -> dict[tuple[str, str, str], list[dict[str, str]]]:
    grouped: dict[tuple[str, str, str], list[dict[str, str]]] = defaultdict(list)
    for row in measurements:
        grouped[(row["suite"], row["lane"], row["vc_key"])].append(row)
    return grouped


def all_pass(rows: list[dict[str, str]]) -> bool:
    return bool(rows) and all(row["status"] == "pass" for row in rows)


def parse_numeric_map(value: str) -> dict[str, int]:
    parsed: dict[str, int] = {}
    for item in filter(None, value.split(",")):
        name, separator, raw_value = item.rpartition("=")
        if separator and raw_value.isdigit():
            parsed[name] = int(raw_value)
    return parsed


def profiles_by_vc(
    profiles: list[dict[str, str]],
) -> dict[tuple[str, str, str], list[dict[str, str]]]:
    grouped: dict[tuple[str, str, str], list[dict[str, str]]] = defaultdict(list)
    for profile in profiles:
        grouped[(profile["suite"], profile["lane"], profile["vc_key"])].append(
            profile
        )
    return grouped


def reconstruction_succeeded(
    rows: list[dict[str, str]],
    profiles: list[dict[str, str]],
    lane: str,
) -> bool:
    if not all_pass(rows):
        return False
    if not profiles:
        return all(
            row["message"] == "closed before backend timing" for row in rows
        )
    accepted = {
        "crush-core": {
            "selected-fact",
            "pre-reconstructed",
            "core-reconstructed",
        },
        "crush-alethe": {"alethe-reconstructed"},
        "crush-portfolio": {
            "selected-fact",
            "pre-reconstructed",
            "alethe-reconstructed",
            "core-reconstructed",
        },
    }[lane]
    return all(profile["outcome"] in accepted for profile in profiles)


def failure_mode(
    rows: list[dict[str, str]], profiles: list[dict[str, str]], lane: str
) -> str:
    candidates: list[str] = []
    for profile in profiles:
        outcome = profile["outcome"]
        replay = profile["replay"]
        if outcome == "reconstruction-failed":
            if lane == "crush-core" or replay == "not-attempted":
                candidates.append("core-failed")
            elif lane == "crush-alethe":
                candidates.append(replay)
            else:
                candidates.append(f"{replay}+core-failed")
        elif outcome == "unknown":
            candidates.append("solver-unknown")
        elif outcome == "sat":
            candidates.append("solver-sat")
        elif outcome not in {
            "alethe-reconstructed",
            "core-reconstructed",
            "pre-reconstructed",
            "selected-fact",
            "verified",
        }:
            candidates.append(outcome)
    if candidates:
        return Counter(candidates).most_common(1)[0][0]
    categories = [row["category"] for row in rows if row["category"] != "-"]
    return Counter(categories).most_common(1)[0][0] if categories else "unclassified"


def coverage_rows(
    attempts: dict[tuple[str, str, str], list[dict[str, str]]]
) -> list[list[object]]:
    by_lane: dict[tuple[str, str], list[list[dict[str, str]]]] = defaultdict(list)
    for (suite, lane, _), rows in attempts.items():
        by_lane[(suite, lane)].append(rows)
    output: list[list[object]] = []
    for (suite, lane), vcs in sorted(by_lane.items()):
        solved = sum(all_pass(rows) for rows in vcs)
        attempted = len(vcs)
        elapsed = [
            float(row["milliseconds"])
            for rows in vcs
            for row in rows
            if row["milliseconds"]
        ]
        output.append(
            [
                suite,
                lane,
                attempted,
                solved,
                attempted - solved,
                f"{100.0 * solved / attempted:.1f}" if attempted else "0.0",
                f"{sum(elapsed):.3f}",
                f"{sum(elapsed) / len(elapsed):.3f}" if elapsed else "0.000",
                f"{min(elapsed):.3f}" if elapsed else "0.000",
                f"{max(elapsed):.3f}" if elapsed else "0.000",
            ]
        )
    return output


def reconstruction_rows(
    attempts: dict[tuple[str, str, str], list[dict[str, str]]],
    profiles: list[dict[str, str]],
) -> list[list[object]]:
    profile_groups = profiles_by_vc(profiles)
    suites = sorted({suite for suite, lane, _ in attempts if lane == "crush-verify"})
    output: list[list[object]] = []
    for suite in suites:
        verify_vcs = {
            vc: rows
            for (row_suite, lane, vc), rows in attempts.items()
            if row_suite == suite and lane == "crush-verify"
        }
        verified = {vc for vc, rows in verify_vcs.items() if all_pass(rows)}
        counts = []
        for lane in RECONSTRUCTION_LANES:
            counts.append(
                sum(
                    vc in verified
                    and reconstruction_succeeded(
                        attempts.get((suite, lane, vc), []),
                        profile_groups.get((suite, lane, vc), []),
                        lane,
                    )
                    for vc in verify_vcs
                )
            )
        output.append([suite, len(verify_vcs), len(verified), *counts])
    return output


def reconstruction_failure_rows(
    attempts: dict[tuple[str, str, str], list[dict[str, str]]],
    profiles: list[dict[str, str]],
) -> list[list[object]]:
    profile_groups = profiles_by_vc(profiles)
    counts: Counter[tuple[str, str, str]] = Counter()
    suites = {suite for suite, lane, _ in attempts if lane == "crush-verify"}
    for suite in suites:
        verified = {
            vc
            for (row_suite, lane, vc), rows in attempts.items()
            if row_suite == suite and lane == "crush-verify" and all_pass(rows)
        }
        for lane in RECONSTRUCTION_LANES:
            if not any(
                row_suite == suite and row_lane == lane
                for row_suite, row_lane, _ in attempts
            ):
                continue
            for vc in verified:
                rows = attempts.get((suite, lane, vc), [])
                vc_profiles = profile_groups[(suite, lane, vc)]
                if reconstruction_succeeded(rows, vc_profiles, lane):
                    continue
                mode = failure_mode(rows, vc_profiles, lane)
                counts[(suite, lane, mode)] += 1
    return [
        [suite, lane, mode, count]
        for (suite, lane, mode), count in sorted(counts.items())
    ]


def phase_rows(profiles: list[dict[str, str]]) -> list[list[object]]:
    phase_values: dict[tuple[str, str, str], list[int]] = defaultdict(list)
    lane_totals: Counter[tuple[str, str]] = Counter()
    for row in profiles:
        key = (row["suite"], row["lane"])
        for item in filter(None, row["phases"].split(",")):
            label, value = item.rsplit("=", 1)
            nanos = int(value)
            phase_values[(row["suite"], row["lane"], label)].append(nanos)
            lane_totals[key] += nanos
    output: list[list[object]] = []
    for (suite, lane, phase), values in sorted(phase_values.items()):
        total = sum(values)
        lane_total = lane_totals[(suite, lane)]
        output.append(
            [
                suite,
                lane,
                phase,
                len(values),
                f"{total / 1_000_000.0:.3f}",
                f"{total / len(values) / 1_000_000.0:.3f}",
                f"{min(values) / 1_000_000.0:.3f}",
                f"{max(values) / 1_000_000.0:.3f}",
                f"{100.0 * total / lane_total:.1f}" if lane_total else "0.0",
            ]
        )
    return output


def outcome_rows(profiles: list[dict[str, str]]) -> list[list[object]]:
    counts: Counter[tuple[str, str, str, str]] = Counter()
    for row in profiles:
        counts[(row["suite"], row["lane"], row["outcome"], row["replay"])] += 1
    return [
        [suite, lane, outcome, replay, events]
        for (suite, lane, outcome, replay), events in sorted(counts.items())
    ]


def alethe_scaling_rows(profiles: list[dict[str, str]]) -> list[list[object]]:
    output: list[list[object]] = []
    for row in profiles:
        if row["outcome"] != "alethe-reconstructed":
            continue
        metrics = parse_numeric_map(row.get("metrics", ""))
        phases = parse_numeric_map(row["phases"])
        commands = metrics.get("certificate_commands")
        replay_nanos = phases.get("replay")
        if commands is None or replay_nanos is None:
            continue
        steps = metrics.get("certificate_steps", 0)
        output.append(
            [
                row["suite"],
                row["lane"],
                row["repeat"],
                row["vc_key"],
                row["declaration"],
                row["goal_hash"],
                commands,
                metrics.get("certificate_assumes", 0),
                steps,
                metrics.get("certificate_anchors", 0),
                metrics.get("certificate_sexp_nodes", 0),
                metrics.get("certificate_bytes", 0),
                replay_nanos,
                f"{replay_nanos / 1_000_000.0:.3f}",
                f"{replay_nanos / commands:.1f}" if commands else "0.0",
                f"{replay_nanos / steps:.1f}" if steps else "0.0",
            ]
        )
    return output


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
    intercept = mean_y - slope * mean_x
    return correlation, slope, intercept


def fit_columns(xs: list[float], ys: list[float], scale: float) -> list[str]:
    fit = linear_fit(xs, ys)
    if fit is None:
        return ["-", "-", "-"]
    correlation, slope, _ = fit
    return [
        f"{correlation:.4f}",
        f"{correlation * correlation:.4f}",
        f"{slope * scale:.6f}",
    ]


def alethe_scaling_summary_rows(
    scaling: list[list[object]],
) -> list[list[object]]:
    grouped: dict[tuple[str, str], list[list[object]]] = defaultdict(list)
    for row in scaling:
        grouped[(str(row[0]), str(row[1]))].append(row)
    output: list[list[object]] = []
    for (suite, lane), rows in sorted(grouped.items()):
        by_vc: dict[str, list[list[object]]] = defaultdict(list)
        for row in rows:
            by_vc[str(row[3])].append(row)
        commands: list[float] = []
        certificate_bytes: list[float] = []
        replay_ms: list[float] = []
        for vc_rows in by_vc.values():
            commands.append(
                sum(float(row[6]) for row in vc_rows) / len(vc_rows)
            )
            certificate_bytes.append(
                sum(float(row[11]) for row in vc_rows) / len(vc_rows)
            )
            replay_ms.append(
                sum(float(row[12]) for row in vc_rows)
                / len(vc_rows)
                / 1_000_000.0
            )
        output.append(
            [
                suite,
                lane,
                len(by_vc),
                len(rows),
                int(min(commands)),
                int(max(commands)),
                f"{min(replay_ms):.3f}",
                f"{sum(replay_ms) / len(replay_ms):.3f}",
                f"{max(replay_ms):.3f}",
                *fit_columns(commands, replay_ms, 100.0),
                *fit_columns(certificate_bytes, replay_ms, 1024.0),
            ]
        )
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--measurements", required=True, type=Path)
    parser.add_argument("--profiles", required=True, type=Path)
    parser.add_argument("--out-dir", required=True, type=Path)
    args = parser.parse_args()

    measurements = read_tsv(args.measurements)
    profiles = read_tsv(args.profiles)
    attempts = grouped_attempts(measurements)
    args.out_dir.mkdir(parents=True, exist_ok=True)

    write_tsv(
        args.out_dir / "coverage-summary.tsv",
        [
            "suite",
            "lane",
            "attempted_vcs",
            "solved_vcs",
            "failed_vcs",
            "pass_pct",
            "total_ms",
            "mean_ms",
            "min_ms",
            "max_ms",
        ],
        coverage_rows(attempts),
    )
    write_tsv(
        args.out_dir / "reconstruction-summary.tsv",
        [
            "suite",
            "total_vcs",
            "verified_vcs",
            "core_reconstructed",
            "alethe_reconstructed",
            "portfolio_reconstructed",
        ],
        reconstruction_rows(attempts, profiles),
    )
    write_tsv(
        args.out_dir / "reconstruction-failures.tsv",
        ["suite", "lane", "failure_mode", "vcs"],
        reconstruction_failure_rows(attempts, profiles),
    )
    write_tsv(
        args.out_dir / "phase-summary.tsv",
        [
            "suite",
            "lane",
            "phase",
            "events",
            "total_ms",
            "mean_ms",
            "min_ms",
            "max_ms",
            "phase_pct",
        ],
        phase_rows(profiles),
    )
    write_tsv(
        args.out_dir / "outcome-summary.tsv",
        ["suite", "lane", "outcome", "replay", "events"],
        outcome_rows(profiles),
    )
    scaling = alethe_scaling_rows(profiles)
    write_tsv(
        args.out_dir / "alethe-replay-scaling.tsv",
        [
            "suite",
            "lane",
            "repeat",
            "vc_key",
            "declaration",
            "goal_hash",
            "commands",
            "assumes",
            "steps",
            "anchors",
            "sexp_nodes",
            "certificate_bytes",
            "replay_nanos",
            "replay_ms",
            "nanos_per_command",
            "nanos_per_step",
        ],
        scaling,
    )
    write_tsv(
        args.out_dir / "alethe-replay-scaling-summary.tsv",
        [
            "suite",
            "lane",
            "vcs",
            "samples",
            "min_commands",
            "max_commands",
            "min_replay_ms",
            "mean_replay_ms",
            "max_replay_ms",
            "commands_pearson_r",
            "commands_r_squared",
            "ms_per_100_commands",
            "bytes_pearson_r",
            "bytes_r_squared",
            "ms_per_kib",
        ],
        alethe_scaling_summary_rows(scaling),
    )


if __name__ == "__main__":
    main()
