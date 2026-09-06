#!/usr/bin/env python3

"""Guards on the recorded backend patches under scripts/patches.

A typo in a template costs a full corpus rebuild before it surfaces, so the
placeholders, the substitution counts, and the invariants each harness checks
after applying a patch are asserted here instead.
"""

import re
import sys
import unittest
from pathlib import Path


sys.dont_write_bytecode = True

PATCHES = Path(__file__).with_name("patches")
SMT_PATCHES = ("loom-smt", "velvet-smt", "plean-smt")


def read(name: str) -> str:
    return (PATCHES / f"{name}.patch.in").read_text(encoding="utf-8")


def added_lines(text: str) -> list[str]:
    return [
        line[1:]
        for line in text.splitlines()
        if line.startswith("+") and not line.startswith("+++")
    ]


def removed_lines(text: str) -> list[str]:
    return [
        line[1:]
        for line in text.splitlines()
        if line.startswith("-") and not line.startswith("---")
    ]


class TemplateTests(unittest.TestCase):
    def test_every_smt_patch_exists(self) -> None:
        for name in SMT_PATCHES:
            with self.subTest(patch=name):
                self.assertTrue((PATCHES / f"{name}.patch.in").is_file())

    def test_every_smt_patch_adds_one_pinned_require(self) -> None:
        for name in SMT_PATCHES:
            with self.subTest(patch=name):
                requires = [
                    line
                    for line in added_lines(read(name))
                    if line.startswith("require Smt from git")
                ]
                self.assertEqual(
                    requires,
                    ['require Smt from git "@SMT_REPO_URL@" @ "@SMT_REV@"'],
                )

    def test_no_patch_hardcodes_a_revision(self) -> None:
        # A literal revision would silently diverge from SMT_REV.
        for name in SMT_PATCHES:
            with self.subTest(patch=name):
                for line in added_lines(read(name)):
                    if "lean-smt" in line and "@SMT_REPO_URL@" not in line:
                        self.assertNotRegex(line, r"[0-9a-f]{40}")


class PLeanBackendTests(unittest.TestCase):
    def setUp(self) -> None:
        self.text = read("plean-smt")

    def test_all_three_backend_sites_are_substituted(self) -> None:
        # scripts/benchmark-plean.sh validates exactly this count after
        # applying the patch, so the two numbers have to agree.
        added = [
            line
            for line in added_lines(self.text)
            if "all_goals smt @SMT_CONFIG@ [*]" in line
        ]
        removed = [
            line
            for line in removed_lines(self.text)
            if "all_goals crush [*]" in line
        ]
        self.assertEqual(len(added), 3)
        self.assertEqual(len(removed), 3)

    def test_the_tactic_module_imports_lean_smt(self) -> None:
        self.assertIn("import Smt", added_lines(self.text))

    def test_the_close_chains_drop_every_other_backend(self) -> None:
        # Leaving these in would credit lean-smt with obligations that Crush or
        # grind closed.
        for fallback in (
            "pverify_structural_smt",
            "pverify_split_ite_smt",
            "pverify_split_smt",
            "pverify_grind",
        ):
            with self.subTest(fallback=fallback):
                self.assertFalse(
                    any(fallback in line for line in added_lines(self.text)),
                    f"{fallback} survives the lean-smt patch",
                )

    def test_it_trims_the_same_chains_the_grind_patch_does(self) -> None:
        # Both lanes have to face the same close-chain, or their coverage is
        # not comparable. Compare what each patch removes, not how much
        # context git chose to print around it.
        def trimmed(patch: str) -> set[str]:
            return {
                match.group(1)
                for line in removed_lines(patch)
                if (match := re.search(r"\|\s*(pverify_\w+|default_inv)", line))
            }

        self.assertEqual(trimmed(read("plean-grind")), trimmed(self.text))


if __name__ == "__main__":
    unittest.main()
