#!/usr/bin/env python3

import importlib.util
import sys
import unittest
from pathlib import Path


sys.dont_write_bytecode = True

MODULE_PATH = Path(__file__).with_name("plot-time-coverage.py")
SPEC = importlib.util.spec_from_file_location("plot_time_coverage", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
plot_time_coverage = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(plot_time_coverage)


class LegendOrderTests(unittest.TestCase):
    def test_crush_moves_to_the_bottom(self) -> None:
        keys = ["auto", "duper", "lean-smt", "crush", "grind"]

        order = plot_time_coverage.legend_order(keys)

        self.assertEqual([keys[i] for i in order],
                         ["auto", "duper", "lean-smt", "grind", "crush"])

    def test_baselines_keep_their_relative_order(self) -> None:
        keys = ["grind", "auto", "crush", "duper"]

        order = plot_time_coverage.legend_order(keys)

        self.assertEqual([keys[i] for i in order],
                         ["grind", "auto", "duper", "crush"])

    def test_the_reconstruction_lanes_put_portfolio_last(self) -> None:
        keys = ["smt-only", "crush-portfolio", "crush-alethe"]

        order = plot_time_coverage.legend_order(keys)

        self.assertEqual([keys[i] for i in order],
                         ["smt-only", "crush-alethe", "crush-portfolio"])

    def test_no_emphasised_curve_leaves_the_order_alone(self) -> None:
        keys = ["auto", "duper", "grind"]

        self.assertEqual(plot_time_coverage.legend_order(keys), [0, 1, 2])

    def test_an_empty_panel_is_not_an_error(self) -> None:
        self.assertEqual(plot_time_coverage.legend_order([]), [])

    def test_order_is_a_permutation_of_the_input(self) -> None:
        keys = ["auto", "crush", "duper", "crush-portfolio", "grind"]

        self.assertEqual(sorted(plot_time_coverage.legend_order(keys)),
                         list(range(len(keys))))


if __name__ == "__main__":
    unittest.main()
