#!/usr/bin/env python3

import csv
import importlib.util
import tempfile
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("merge-runs.py")
SPEC = importlib.util.spec_from_file_location("merge_runs", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
merge_runs = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(merge_runs)


def write_tsv(path: Path, columns: list[str], rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    merge_runs.write(path, columns, rows)


def make_run(root: Path, suite: str, lanes: tuple[str, ...] = ("crush-verify",)) -> Path:
    """A minimal run directory: the two raw files plus one provenance file."""
    directory = root / suite
    write_tsv(
        directory / "measurements.tsv",
        ["suite", "lane", "vc_key", "status"],
        [
            {"suite": suite, "lane": lane, "vc_key": f"{suite}-{index}", "status": "pass"}
            for lane in lanes
            for index in range(2)
        ],
    )
    write_tsv(
        directory / "profile-events.tsv",
        ["suite", "lane", "vc_key", "outcome"],
        [
            {"suite": suite, "lane": lane, "vc_key": f"{suite}-0", "outcome": "verified"}
            for lane in lanes
        ],
    )
    write_tsv(
        directory / "metadata.tsv",
        ["suite", "crush_commit"],
        [{"suite": suite, "crush_commit": f"commit-{suite}"}],
    )
    return directory


def read_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


class SuiteDiscoveryTests(unittest.TestCase):
    def test_reads_suites_from_measurements(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run = make_run(Path(tmp), "velvet")
            self.assertEqual(merge_runs.suites_of(run), {"velvet"})

    def test_blank_suite_defaults_to_plean(self) -> None:
        """PLean's harness leaves the column empty; the report defaults it too."""
        with tempfile.TemporaryDirectory() as tmp:
            run = Path(tmp) / "plean"
            write_tsv(
                run / "measurements.tsv",
                ["suite", "lane", "vc_key", "status"],
                [{"suite": "", "lane": "crush-verify", "vc_key": "a", "status": "pass"}],
            )
            self.assertEqual(merge_runs.suites_of(run), {"plean"})


class CombineTests(unittest.TestCase):
    def test_concatenates_disjoint_suites(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = [make_run(root, "cashmere"), make_run(root, "velvet")]
            columns, rows, present = merge_runs.combine(
                sources, "measurements.tsv", {}
            )
            self.assertEqual(present, 2)
            self.assertEqual(len(rows), 4)
            self.assertEqual({row["suite"] for row in rows}, {"cashmere", "velvet"})
            self.assertEqual(columns, ["suite", "lane", "vc_key", "status"])

    def test_missing_optional_file_is_skipped(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = [make_run(root, "cashmere")]
            _, rows, present = merge_runs.combine(sources, "runs.tsv", {})
            self.assertEqual((present, rows), (0, []))

    def test_superseded_suite_rows_are_dropped(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old = make_run(root / "old", "velvet")
            new = make_run(root / "new", "velvet")
            _, rows, _ = merge_runs.combine(
                [old, new], "measurements.tsv", {old: {"velvet"}}
            )
            # Only the later run's rows survive, so counts do not double.
            self.assertEqual(len(rows), 2)

    def test_union_of_columns_keeps_first_seen_order(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            first = make_run(root, "cashmere")
            second = root / "velvet"
            write_tsv(
                second / "measurements.tsv",
                ["suite", "lane", "vc_key", "status", "milliseconds"],
                [
                    {
                        "suite": "velvet",
                        "lane": "crush-verify",
                        "vc_key": "v",
                        "status": "pass",
                        "milliseconds": "5",
                    }
                ],
            )
            columns, _, _ = merge_runs.combine(
                [first, second], "measurements.tsv", {}
            )
            self.assertEqual(
                columns, ["suite", "lane", "vc_key", "status", "milliseconds"]
            )


class ProvenanceTests(unittest.TestCase):
    def test_every_source_run_is_recorded(self) -> None:
        """A merged directory must still name each run that produced it."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = [make_run(root, "cashmere"), make_run(root, "velvet")]
            _, rows, _ = merge_runs.combine(sources, "metadata.tsv", {})
            self.assertEqual(
                [row["crush_commit"] for row in rows],
                ["commit-cashmere", "commit-velvet"],
            )


class RoundTripTests(unittest.TestCase):
    def test_write_then_read_preserves_rows(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "out.tsv"
            rows = [{"suite": "velvet", "lane": "crush-verify"}]
            merge_runs.write(path, ["suite", "lane"], rows)
            self.assertEqual(read_rows(path), rows)

    def test_absent_column_is_written_empty(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "out.tsv"
            merge_runs.write(path, ["suite", "extra"], [{"suite": "velvet"}])
            self.assertEqual(read_rows(path), [{"suite": "velvet", "extra": ""}])


if __name__ == "__main__":
    unittest.main()
