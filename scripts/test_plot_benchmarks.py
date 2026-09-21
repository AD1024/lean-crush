#!/usr/bin/env python3

import importlib.util
import sys
import unittest
from pathlib import Path


sys.dont_write_bytecode = True

MODULE_PATH = Path(__file__).with_name("plot-benchmarks.py")
SPEC = importlib.util.spec_from_file_location("plot_benchmarks", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
plot_benchmarks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(plot_benchmarks)


class SuiteFilterTests(unittest.TestCase):
    def rows(self) -> list[dict[str, str]]:
        return [
            {"suite": "curated", "lane": "smt-only"},
            {"suite": "loom", "lane": "crush-verify"},
            {"suite": "velvet", "lane": "crush-verify"},
        ]

    def test_named_suites_are_dropped(self) -> None:
        kept = plot_benchmarks.drop_suites(self.rows(), {"loom"})

        self.assertEqual([row["suite"] for row in kept], ["curated", "velvet"])

    def test_no_exclusions_returns_the_same_rows(self) -> None:
        rows = self.rows()

        self.assertIs(plot_benchmarks.drop_suites(rows, set()), rows)

    def test_absent_suite_is_a_no_op(self) -> None:
        kept = plot_benchmarks.drop_suites(self.rows(), {"cashmere"})

        self.assertEqual(len(kept), 3)

    def test_rows_without_a_suite_column_survive(self) -> None:
        kept = plot_benchmarks.drop_suites([{"lane": "smt-only"}], {"loom"})

        self.assertEqual(kept, [{"lane": "smt-only"}])

    def test_loom_is_the_published_exclusion(self) -> None:
        self.assertEqual(plot_benchmarks.PAPER_EXCLUDED_SUITES, ("loom",))


class OrderingTests(unittest.TestCase):
    def test_lean_smt_sorts_between_duper_and_crush(self) -> None:
        backends = ["grind", "crush", "lean-smt", "duper", "auto"]

        self.assertEqual(
            sorted(backends, key=plot_benchmarks.backend_sort_key),
            ["auto", "duper", "lean-smt", "crush", "grind"],
        )

    def test_unknown_backend_sorts_last_without_raising(self) -> None:
        backends = ["crush", "vampire", "auto"]

        self.assertEqual(
            sorted(backends, key=plot_benchmarks.backend_sort_key),
            ["auto", "crush", "vampire"],
        )

    def test_smt_lane_sorts_before_the_crush_lanes(self) -> None:
        lanes = ["crush-alethe", "smt-only", "duper-only", "crush-portfolio"]

        self.assertEqual(
            sorted(lanes, key=plot_benchmarks.lane_sort_key),
            ["duper-only", "smt-only", "crush-alethe", "crush-portfolio"],
        )

    def test_lean_smt_has_its_own_label_and_color(self) -> None:
        self.assertEqual(plot_benchmarks.label_backend("lean-smt"), "lean-smt")
        self.assertEqual(plot_benchmarks.label_lane("smt-only"), "lean-smt")
        self.assertNotIn(
            plot_benchmarks.BACKEND_COLORS["lean-smt"],
            [
                color
                for backend, color in plot_benchmarks.BACKEND_COLORS.items()
                if backend != "lean-smt"
            ],
        )


class ReconstructionFieldTests(unittest.TestCase):
    def checked_row(self) -> dict[str, str]:
        return {
            "suite": "velvet",
            "total_vcs": "504",
            "verify_solved_vcs": "481",
            "smt_verified_vcs": "296",
            "core_reconstructed": "287",
            "alethe_reconstructed": "26",
            "portfolio_reconstructed": "287",
            "core_checked": "474",
            "alethe_checked": "172",
            "portfolio_checked": "473",
        }

    def test_checked_columns_are_preferred(self) -> None:
        names, checked = plot_benchmarks.reconstruction_fields([self.checked_row()])

        self.assertTrue(checked)
        self.assertEqual(names, plot_benchmarks.CHECKED_FIELDS)

    def test_old_schema_falls_back_to_replay_counts(self) -> None:
        row = self.checked_row()
        for field in plot_benchmarks.CHECKED_FIELDS:
            del row[field]

        names, checked = plot_benchmarks.reconstruction_fields([row])

        self.assertFalse(checked)
        self.assertEqual(names, plot_benchmarks.REPLAY_FIELDS)

    def test_a_single_old_row_downgrades_the_whole_chart(self) -> None:
        # Mixing measures on one chart would be worse than showing the
        # narrower one everywhere, so one old row decides for all of them.
        old = self.checked_row()
        for field in plot_benchmarks.CHECKED_FIELDS:
            del old[field]

        names, checked = plot_benchmarks.reconstruction_fields(
            [self.checked_row(), old]
        )

        self.assertFalse(checked)
        self.assertEqual(names, plot_benchmarks.REPLAY_FIELDS)

    def test_checked_counts_exceed_smt_cohort_replay(self) -> None:
        # The whole point of the switch: pre-SMT closures carry proofs the
        # SMT-cohort counts drop.
        row = self.checked_row()

        self.assertGreater(
            int(row["portfolio_checked"]), int(row["portfolio_reconstructed"])
        )
        self.assertGreater(int(row["portfolio_checked"]), int(row["smt_verified_vcs"]))


class CrushSeriesTests(unittest.TestCase):
    def test_both_crush_series_are_labelled_and_distinct(self) -> None:
        self.assertEqual(
            plot_benchmarks.label_backend("crush"), "Crush (SMT trusted)"
        )
        self.assertEqual(
            plot_benchmarks.label_backend("crush-checked"),
            "Crush (kernel-checked)",
        )

    def test_kernel_checked_sorts_after_grind(self) -> None:
        """The kernel-checked series reads below grind, the baseline it answers."""
        order = sorted(
            ["grind", "crush-checked", "auto", "crush", "lean-smt", "duper"],
            key=plot_benchmarks.backend_sort_key,
        )

        self.assertEqual(
            order,
            ["auto", "duper", "lean-smt", "crush", "grind", "crush-checked"],
        )

    def test_the_two_crush_series_do_not_share_a_colour(self) -> None:
        self.assertNotEqual(
            plot_benchmarks.BACKEND_COLORS["crush"],
            plot_benchmarks.BACKEND_COLORS["crush-checked"],
        )

    def test_every_ordered_backend_has_a_colour_and_label(self) -> None:
        for backend in plot_benchmarks.BACKEND_ORDER:
            with self.subTest(backend=backend):
                self.assertIn(backend, plot_benchmarks.BACKEND_COLORS)
                self.assertIn(backend, plot_benchmarks.BACKEND_LABELS)


class FailureModeTests(unittest.TestCase):
    def test_every_ordered_mode_has_a_color(self) -> None:
        missing = [
            mode
            for mode in plot_benchmarks.FAILURE_MODE_ORDER
            if mode not in plot_benchmarks.FAILURE_MODE_COLORS
        ]

        self.assertEqual(missing, [])

    def test_lean_smt_failure_modes_are_known(self) -> None:
        # The lane can emit each of these, so none should fall back to a
        # positional palette color that shifts as other modes appear.
        for mode in (
            "rule-gap",
            "term-gap",
            "no-certificate",
            "certificate-error",
            "translation-failed",
            "timeout",
            "solver-sat",
            "solver-unknown",
        ):
            with self.subTest(mode=mode):
                self.assertIn(mode, plot_benchmarks.FAILURE_MODE_COLORS)


if __name__ == "__main__":
    unittest.main()
