#!/usr/bin/env python3

import importlib.util
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("benchmark-report.py")
SPEC = importlib.util.spec_from_file_location("benchmark_report", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
benchmark_report = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(benchmark_report)


def measurement(
    lane: str, vc: str, status: str, milliseconds: str = "100"
) -> dict[str, str]:
    return {
        "suite": "Test",
        "lane": lane,
        "vc_key": vc,
        "status": status,
        "category": "" if status == "pass" else "tactic",
        "milliseconds": milliseconds,
        "message": "",
    }


def profile(lane: str, vc: str, outcome: str, replay: str = "") -> dict[str, str]:
    return {
        "suite": "Test",
        "lane": lane,
        "vc_key": vc,
        "outcome": outcome,
        "replay": replay,
        "detail": "",
    }


class ReconstructionCohortTests(unittest.TestCase):
    def test_pre_smt_success_is_not_a_reconstruction_failure(self) -> None:
        measurements = [
            measurement("crush-verify", "pre-smt", "pass"),
            measurement("crush-verify", "smt-unsat", "pass"),
            measurement("crush-core", "pre-smt", "pass"),
            measurement("crush-core", "smt-unsat", "pass"),
            measurement("crush-alethe", "pre-smt", "fail"),
            measurement("crush-alethe", "smt-unsat", "fail"),
            measurement("crush-portfolio", "pre-smt", "pass"),
            measurement("crush-portfolio", "smt-unsat", "pass"),
        ]
        profiles = [
            profile("crush-verify", "pre-smt", "pre-reconstructed"),
            profile("crush-verify", "smt-unsat", "verified"),
            profile("crush-core", "pre-smt", "pre-reconstructed"),
            profile("crush-core", "smt-unsat", "core-reconstructed"),
            profile("crush-alethe", "pre-smt", "sat"),
            profile(
                "crush-alethe",
                "smt-unsat",
                "reconstruction-failed",
                "rule-gap",
            ),
            profile("crush-portfolio", "pre-smt", "pre-reconstructed"),
            profile("crush-portfolio", "smt-unsat", "core-reconstructed"),
        ]
        attempts = benchmark_report.grouped_attempts(measurements)

        self.assertEqual(
            # suite, total, verify solved, SMT cohort, then Core/Alethe/
            # Portfolio replay counts over that cohort, then the same three
            # lanes' checked-proof counts over every VC. Core and Portfolio
            # each close both VCs with a proof but replay only the one the
            # solver proved; Alethe fails both.
            benchmark_report.reconstruction_rows(attempts, profiles),
            [["Test", 2, 2, 1, 1, 0, 1, 2, 0, 2]],
        )
        self.assertEqual(
            benchmark_report.reconstruction_failure_rows(attempts, profiles),
            [["Test", "crush-alethe", "rule-gap", 1]],
        )


class HeadlineLaneTests(unittest.TestCase):
    def test_lean_smt_is_a_headline_backend(self) -> None:
        lanes = {
            "auto-duper",
            "duper-only",
            "smt-only",
            "crush-verify",
            "grind-only",
        }

        self.assertEqual(
            benchmark_report.headline_lane_map("leanhammer", lanes),
            [
                ("auto", "auto-duper"),
                ("duper", "duper-only"),
                ("lean-smt", "smt-only"),
                ("crush", "crush-verify"),
                ("grind", "grind-only"),
            ],
        )

    def test_absent_smt_lane_is_omitted(self) -> None:
        lanes = {"auto-duper", "crush-verify"}

        self.assertEqual(
            benchmark_report.headline_lane_map("leanhammer", lanes),
            [("auto", "auto-duper"), ("crush", "crush-verify")],
        )


class ReconstructionComparisonTests(unittest.TestCase):
    """lean-smt against Crush's strict Alethe lane and its portfolio.

    `replay` closes by certificate replay in every lane. `pre` is closed by
    Crush before SMT is consulted, so it is a checked proof but not a
    certificate replay and it is outside the SMT cohort. `rule` exercises
    lean-smt leaving an unhandled Alethe step open while Crush's portfolio
    falls back to its core route. `nosolve` fails everywhere.
    """

    def build(
        self,
    ) -> tuple[dict[tuple[str, str, str], list[dict[str, str]]], list[dict[str, str]]]:
        measurements = [
            measurement("crush-verify", "replay", "pass"),
            measurement("crush-verify", "pre", "pass"),
            measurement("crush-verify", "rule", "pass"),
            measurement("crush-verify", "nosolve", "fail"),
            measurement("smt-only", "replay", "pass", "300"),
            measurement("smt-only", "pre", "pass", "100"),
            measurement("smt-only", "rule", "fail"),
            measurement("smt-only", "nosolve", "fail"),
            measurement("crush-alethe", "replay", "pass", "500"),
            measurement("crush-alethe", "pre", "pass", "100"),
            measurement("crush-alethe", "rule", "fail"),
            measurement("crush-alethe", "nosolve", "fail"),
            measurement("crush-portfolio", "replay", "pass", "400"),
            measurement("crush-portfolio", "pre", "pass", "100"),
            measurement("crush-portfolio", "rule", "pass"),
            measurement("crush-portfolio", "nosolve", "fail"),
        ]
        profiles = [
            profile("crush-verify", "replay", "verified"),
            profile("crush-verify", "pre", "pre-reconstructed"),
            profile("crush-verify", "rule", "verified"),
            profile("crush-verify", "nosolve", "sat"),
            profile("smt-only", "replay", "alethe-reconstructed"),
            profile("smt-only", "pre", "alethe-reconstructed"),
            profile("smt-only", "rule", "reconstruction-failed", "rule-gap"),
            profile("smt-only", "nosolve", "sat"),
            profile("crush-alethe", "replay", "alethe-reconstructed"),
            profile("crush-alethe", "pre", "pre-reconstructed"),
            profile(
                "crush-alethe", "rule", "reconstruction-failed", "term-gap"
            ),
            profile("crush-alethe", "nosolve", "sat"),
            profile("crush-portfolio", "replay", "alethe-reconstructed"),
            profile("crush-portfolio", "pre", "pre-reconstructed"),
            profile("crush-portfolio", "rule", "core-reconstructed"),
            profile("crush-portfolio", "nosolve", "sat"),
        ]
        return benchmark_report.grouped_attempts(measurements), profiles

    def test_checked_proofs_and_certificate_replays_are_separate(self) -> None:
        attempts, profiles = self.build()

        self.assertEqual(
            benchmark_report.reconstruction_comparison_rows(attempts, profiles),
            [
                # matched, checked, failed, pct, common, mean, common mean,
                # SMT cohort, certificate replays in that cohort
                [
                    "Test",
                    "smt-only",
                    4,
                    2,
                    2,
                    "50.0",
                    2,
                    "200.000",
                    "200.000",
                    2,
                    1,
                ],
                [
                    "Test",
                    "crush-alethe",
                    4,
                    2,
                    2,
                    "50.0",
                    2,
                    "300.000",
                    "300.000",
                    2,
                    1,
                ],
                [
                    "Test",
                    "crush-portfolio",
                    4,
                    3,
                    1,
                    "75.0",
                    2,
                    "200.000",
                    "250.000",
                    2,
                    2,
                ],
            ],
        )

    def test_alethe_cohort_column_matches_the_published_report(self) -> None:
        attempts, profiles = self.build()

        summary = benchmark_report.reconstruction_rows(attempts, profiles)
        comparison = benchmark_report.reconstruction_comparison_rows(
            attempts, profiles
        )
        alethe_summary = summary[0][5]
        alethe_comparison = next(
            row[10] for row in comparison if row[1] == "crush-alethe"
        )

        self.assertEqual(alethe_summary, alethe_comparison)

    def test_failure_modes_distinguish_the_lean_smt_replay_gap(self) -> None:
        attempts, profiles = self.build()

        self.assertEqual(
            benchmark_report.reconstruction_comparison_failure_rows(
                attempts, profiles
            ),
            [
                ["Test", "crush-alethe", "solver-sat", 1],
                ["Test", "crush-alethe", "term-gap", 1],
                ["Test", "crush-portfolio", "solver-sat", 1],
                ["Test", "smt-only", "rule-gap", 1],
                ["Test", "smt-only", "solver-sat", 1],
            ],
        )

    def test_a_single_lane_produces_no_comparison(self) -> None:
        measurements = [
            measurement("crush-alethe", "replay", "pass"),
        ]
        attempts = benchmark_report.grouped_attempts(measurements)

        self.assertEqual(
            benchmark_report.reconstruction_comparison_rows(attempts, []), []
        )

    def test_unmatched_vcs_leave_the_denominator(self) -> None:
        measurements = [
            measurement("smt-only", "shared", "pass"),
            measurement("smt-only", "smt-only-vc", "pass"),
            measurement("crush-alethe", "shared", "pass"),
        ]
        attempts = benchmark_report.grouped_attempts(measurements)

        rows = benchmark_report.reconstruction_comparison_rows(attempts, [])

        self.assertEqual([row[2] for row in rows], [1, 1])


class ReconstructionCheckedProofTests(unittest.TestCase):
    """`*_checked` counts every proof; `*_reconstructed` counts only replay."""

    def rows(self) -> list[list[object]]:
        measurements = [
            # Closed before the solver ran: a checked proof, but outside the
            # SMT cohort, so replay counts must not see it.
            measurement("crush-verify", "pre-smt", "pass"),
            measurement("crush-core", "pre-smt", "pass"),
            measurement("crush-alethe", "pre-smt", "pass"),
            measurement("crush-portfolio", "pre-smt", "pass"),
            # Closed via an SMT unsat and replayed.
            measurement("crush-verify", "smt-unsat", "pass"),
            measurement("crush-core", "smt-unsat", "pass"),
            measurement("crush-alethe", "smt-unsat", "pass"),
            measurement("crush-portfolio", "smt-unsat", "pass"),
        ]
        profiles = [
            profile("crush-verify", "pre-smt", "pre-reconstructed"),
            profile("crush-core", "pre-smt", "pre-reconstructed"),
            profile("crush-alethe", "pre-smt", "pre-reconstructed"),
            profile("crush-portfolio", "pre-smt", "pre-reconstructed"),
            profile("crush-verify", "smt-unsat", "verified"),
            profile("crush-core", "smt-unsat", "core-reconstructed"),
            profile("crush-alethe", "smt-unsat", "alethe-reconstructed"),
            profile("crush-portfolio", "smt-unsat", "alethe-reconstructed"),
        ]
        attempts = benchmark_report.grouped_attempts(measurements)
        return benchmark_report.reconstruction_rows(attempts, profiles)

    def test_pre_smt_proof_counts_as_checked_but_not_as_replay(self) -> None:
        (row,) = self.rows()
        # suite, total, verify_solved, smt_cohort, then three replay counts,
        # then three checked counts.
        _, total, _, smt_cohort = row[0], row[1], row[2], row[3]
        replay = row[4:7]
        checked = row[7:10]

        self.assertEqual(total, 2)
        self.assertEqual(smt_cohort, 1)
        self.assertEqual(list(replay), [1, 1, 1])
        self.assertEqual(list(checked), [2, 2, 2])

    def test_checked_counts_are_never_below_replay_counts(self) -> None:
        (row,) = self.rows()

        for replayed, checked in zip(row[4:7], row[7:10]):
            self.assertGreaterEqual(checked, replayed)

    def test_a_failed_lane_earns_no_checked_proof(self) -> None:
        measurements = [
            measurement("crush-verify", "goal", "pass"),
            measurement("crush-alethe", "goal", "fail"),
        ]
        profiles = [
            profile("crush-verify", "goal", "verified"),
            profile("crush-alethe", "goal", "reconstruction-failed"),
        ]
        attempts = benchmark_report.grouped_attempts(measurements)

        (row,) = benchmark_report.reconstruction_rows(attempts, profiles)

        self.assertEqual(row[8], 0)


class HeadlineSeriesTests(unittest.TestCase):
    """The portfolio lane earns its own headline backend, `crush-checked`."""

    def test_portfolio_becomes_its_own_backend(self) -> None:
        pairs = benchmark_report.headline_lane_map(
            "velvet", {"auto", "grind", "crush-verify", "crush-portfolio"}
        )

        self.assertIn(("crush", "crush-verify"), pairs)
        self.assertIn(("crush-checked", "crush-portfolio"), pairs)

    def test_a_run_without_the_portfolio_lane_is_unchanged(self) -> None:
        pairs = benchmark_report.headline_lane_map(
            "velvet", {"auto", "grind", "crush-verify"}
        )

        self.assertEqual(
            [b for b, _ in pairs if b.startswith("crush")], ["crush"]
        )

    def test_neither_crush_series_is_compared_against_itself(self) -> None:
        # The pairwise table compares Crush with the baselines; both Crush
        # series are the subject, so neither may appear as a baseline row.
        measurements = [
            measurement("crush-verify", "a", "pass"),
            measurement("crush-portfolio", "a", "pass"),
            measurement("auto", "a", "fail"),
        ]
        attempts = benchmark_report.grouped_attempts(measurements)

        rows = benchmark_report.comparison_rows(attempts)

        self.assertEqual([r[1] for r in rows], ["auto"])


if __name__ == "__main__":
    unittest.main()
