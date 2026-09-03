#!/usr/bin/env python3

import importlib.util
import unittest
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("benchmark-report.py")
SPEC = importlib.util.spec_from_file_location("benchmark_report", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
benchmark_report = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(benchmark_report)


def measurement(lane: str, vc: str, status: str) -> dict[str, str]:
    return {
        "suite": "Test",
        "lane": lane,
        "vc_key": vc,
        "status": status,
        "category": "" if status == "pass" else "tactic",
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
            benchmark_report.reconstruction_rows(attempts, profiles),
            [["Test", 2, 2, 1, 1, 0, 1]],
        )
        self.assertEqual(
            benchmark_report.reconstruction_failure_rows(attempts, profiles),
            [["Test", "crush-alethe", "rule-gap", 1]],
        )


if __name__ == "__main__":
    unittest.main()
