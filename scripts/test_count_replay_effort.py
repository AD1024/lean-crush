import unittest

from count_replay_effort import inventory, lex, render, totals


def fenced(body, category="logic", kind="handler", name="test"):
    return (f"-- table4:begin {category} {kind} {name}\n"
            + body + f"\n-- table4:end {name}\n")


class ReplayEffortTests(unittest.TestCase):
    def test_nested_comments_and_literals(self):
        source = ('def a := "-- /- literal -/" -- comment\n'
                  '/- outer /- inner -/\n comment -/\n'
                  'def b := \'"\'\n')
        code, tokens, comments = lex(source)
        self.assertEqual(code.count("\n"), source.count("\n"))
        self.assertEqual([line.strip() for line in code.splitlines() if line.strip()],
                         ['def a := "-- /- literal -/"', 'def b := \'"\''])
        self.assertNotIn("literal", tokens)
        self.assertEqual(comments, {1: "-- comment"})

    def test_one_registration_matching_multiple_rules(self):
        source = fenced('register_crush_replay rule low <<\n'
                        '  (refl ..) | (cong ..) => by rfl -- explanation\n>>')
        region, = inventory(source, "example.lean")
        self.assertEqual((region.handlers, region.loc), (1, 3))
        self.assertEqual((region.start, region.end), (2, 4))

    def test_attributed_handler_and_lemma(self):
        source = fenced('private theorem helper : True := by\n  trivial',
                        kind="lemma", name="helpers")
        source += fenced('@[crush_replay_rule "evaluate" high]\n'
                         'def handler := helper')
        rows = totals(inventory(source, "example.lean"))
        self.assertEqual(rows["logic"], [1, 2, 2])
        self.assertIn(r"\textbf{1} & \textbf{2} & \textbf{2} & \textbf{4}",
                      render(rows, "latex"))

    def test_comments_and_blanks_do_not_count(self):
        source = fenced('-- explanation\n\nprivate def x := 1 /- inline -/\n'
                        '/- nested /- comment -/ -/', kind="lemma")
        self.assertEqual(inventory(source, "example.lean")[0].loc, 1)

    def test_fake_markers_in_comments_and_strings(self):
        source = ('/-\n-- table4:begin logic handler fake\n'
                  'register_crush_replay rule low << (refl ..) => by rfl >>\n-/\n'
                  'def x := "\nregister_crush_replay rule\n"\n')
        self.assertEqual(inventory(source, "example.lean"), [])

    def test_unknown_category(self):
        with self.assertRaisesRegex(ValueError, "unknown fence"):
            inventory(fenced('def x := 0', category="typo", kind="lemma"), "x")

    def test_duplicate_and_nested_fences(self):
        block = fenced('def x := 0', kind="lemma")
        with self.assertRaisesRegex(ValueError, "duplicate"):
            inventory(block + block, "x")
        with self.assertRaisesRegex(ValueError, "nested"):
            inventory(fenced(block, kind="lemma", name="outer"), "x")

    def test_missing_and_mismatched_end(self):
        with self.assertRaisesRegex(ValueError, "unclosed"):
            inventory('-- table4:begin logic lemma x\ndef x := 0\n', "x")
        with self.assertRaisesRegex(ValueError, "mismatched"):
            inventory('-- table4:end missing\n', "x")

    def test_unfenced_registration(self):
        with self.assertRaisesRegex(ValueError, "outside handler"):
            inventory('register_crush_replay rule low << (refl ..) => by rfl >>', "x")

    def test_registration_in_lemma_region(self):
        with self.assertRaisesRegex(ValueError, "outside handler"):
            inventory(fenced('@[crush_replay_rule low]\ndef x := 0', kind="lemma"), "x")

    def test_empty_or_malformed_region(self):
        for source in (fenced(''), fenced('def x := 0'), '-- table4:begin typo\n'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                inventory(source, "x")

    def test_unclosed_lexical_construct(self):
        for source in ('/-', 'def x := "unfinished'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                lex(source)


if __name__ == "__main__":
    unittest.main()
