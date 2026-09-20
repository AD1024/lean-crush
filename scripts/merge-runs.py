#!/usr/bin/env python3

"""Combine several benchmark run directories into one.

A study that measures its suites separately writes one directory per suite --
`benchmark-crush-modes.sh --case_study Cashmere` and `--case_study Velvet`
produce `cashmere/` and `velvet/` -- while the recorded datasets and the figure
renderer expect the corpora suites together under `corpora/`. This joins them.

Only the raw inputs are concatenated; every derived TSV is regenerated from the
merged inputs, so no derived file can disagree with the rows behind it. That is
the same invariant `fold-crush-series.py` keeps, for the same reason.

Provenance files are concatenated as well, so a merged directory still records
every run that produced it -- two `metadata.tsv` rows rather than one, naming
each worktree and commit.

Suites must be disjoint across sources: merging two measurements of the same
suite would silently double its VC counts. Pass `--replace` to let a later
source supersede an earlier one's suites instead.
"""

import argparse
import csv
import subprocess
import sys
from pathlib import Path

csv.field_size_limit(sys.maxsize)

# Concatenated verbatim. `measurements` and `profile-events` are the inputs the
# report reads; the rest is provenance that would otherwise be lost.
RAW = ("measurements.tsv", "profile-events.tsv")
PROVENANCE = (
    "metadata.tsv",
    "runs.tsv",
    "results.tsv",
    "summary.tsv",
    "checkpoints.tsv",
    # Written by the harness rather than the report, and only by the PLean leg,
    # so it has to be carried rather than regenerated. Leaving it out would let a
    # stale per-file breakdown survive an otherwise complete refresh.
    "file-summary.tsv",
)


def read(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        return list(reader.fieldnames or []), list(reader)


def write(path: Path, columns: list[str], rows: list[dict[str, str]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=columns, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row.get(key, "") for key in columns})


def suites_of(source: Path) -> set[str]:
    """Suites a run measured, read from its measurements."""
    path = source / "measurements.tsv"
    if not path.exists():
        return set()
    _, rows = read(path)
    # PLean's harness leaves the column empty; the report defaults it the same way.
    return {row.get("suite") or "plean" for row in rows}


def combine(
    sources: list[Path], name: str, superseded: dict[Path, set[str]]
) -> tuple[list[str], list[dict[str, str]], int]:
    """Concatenate one file across sources, dropping superseded suites."""
    columns: list[str] = []
    merged: list[dict[str, str]] = []
    present = 0
    for source in sources:
        path = source / name
        if not path.exists():
            continue
        present += 1
        source_columns, rows = read(path)
        # A later source may add a column an earlier one lacked; keep first-seen
        # order so the merged header still reads like the harness wrote it.
        for column in source_columns:
            if column not in columns:
                columns.append(column)
        drop = superseded.get(source, set())
        if drop and "suite" in source_columns:
            rows = [r for r in rows if (r.get("suite") or "plean") not in drop]
        merged.extend(rows)
    return columns, merged, present


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Merge benchmark run directories into one."
    )
    parser.add_argument("sources", nargs="+", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument(
        "--report",
        type=Path,
        default=Path(__file__).with_name("benchmark-report.py"),
        help="benchmark-report.py, run to regenerate the derived TSVs",
    )
    parser.add_argument(
        "--replace",
        action="store_true",
        help="let a later source supersede an earlier one's suites instead of "
        "refusing the overlap",
    )
    args = parser.parse_args()

    for source in args.sources:
        if not (source / "measurements.tsv").exists():
            parser.error(f"not a run directory (no measurements.tsv): {source}")

    # Resolve overlaps before writing anything, so a refusal leaves no output.
    superseded: dict[Path, set[str]] = {}
    seen: dict[str, Path] = {}
    for source in args.sources:
        for suite in sorted(suites_of(source)):
            if suite in seen:
                if not args.replace:
                    parser.error(
                        f"suite {suite!r} is measured by both {seen[suite]} and "
                        f"{source}; pass --replace to keep the later one"
                    )
                superseded.setdefault(seen[suite], set()).add(suite)
            seen[suite] = source

    args.out.mkdir(parents=True, exist_ok=True)
    for name in RAW + PROVENANCE:
        columns, rows, present = combine(args.sources, name, superseded)
        if not present:
            continue
        write(args.out / name, columns, rows)
        print(f"  {args.out.name}/{name}: {len(rows)} rows from {present} run(s)")

    subprocess.run(
        [
            sys.executable,
            str(args.report),
            "--measurements", str(args.out / "measurements.tsv"),
            "--profiles", str(args.out / "profile-events.tsv"),
            "--out-dir", str(args.out),
        ],
        check=True,
        stdout=subprocess.DEVNULL,
    )
    print(f"  {args.out.name}: regenerated derived reports")


if __name__ == "__main__":
    main()
