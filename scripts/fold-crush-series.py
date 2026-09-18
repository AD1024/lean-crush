#!/usr/bin/env python3

"""Fold a reconstruction run's Crush lanes into a coverage comparison.

`benchmark.sh` now measures Crush twice -- trusted and portfolio -- so a fresh
run already carries both series and needs none of this. It exists for the
recorded data, whose Crush lane predates that change: it swaps the trusted rows
for a newer run's and adds the portfolio rows beside them, so both series come
from the same run rather than from two machines.

Raw `measurements.tsv` and `profile-events.tsv` are combined and the reports
regenerated from them, so every derived TSV stays consistent with its inputs.
Suites the donor run did not measure keep whatever the target already had.
"""

import argparse
import csv
import subprocess
import sys
from pathlib import Path

csv.field_size_limit(sys.maxsize)

CRUSH_LANES = ("crush-verify", "crush-portfolio")


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


def suite_of(row: dict[str, str]) -> str:
    return row.get("suite") or "plean"


def fold(target: Path, donor: Path, name: str) -> list[dict[str, str]]:
    columns, rows = read(target / name)
    _, donor_rows = read(donor / name)
    donated = [r for r in donor_rows if r.get("lane") in CRUSH_LANES]
    # Only suites the donor actually measured lose their old Crush rows; the
    # rest (Loom, which the reconstruction study skips) keep theirs.
    covered = {suite_of(r) for r in donated}
    kept = [
        r
        for r in rows
        if r.get("lane") not in CRUSH_LANES or suite_of(r) not in covered
    ]
    write(target / name, columns, kept + donated)
    return donated


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", required=True, type=Path)
    parser.add_argument("--donor", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    args = parser.parse_args()

    for name in ("measurements.tsv", "profile-events.tsv"):
        donated = fold(args.target, args.donor, name)
        print(f"  {args.target.name}/{name}: folded {len(donated)} Crush rows")

    subprocess.run(
        [
            sys.executable,
            str(args.report),
            "--measurements", str(args.target / "measurements.tsv"),
            "--profiles", str(args.target / "profile-events.tsv"),
            "--out-dir", str(args.target),
        ],
        check=True,
        stdout=subprocess.DEVNULL,
    )


if __name__ == "__main__":
    main()
