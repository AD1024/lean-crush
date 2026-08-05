import Crush.Solver.Alethe

/-!
Tests for the Alethe proof parser (`Crush/Solver/Alethe.lean`), the foundation of M4
(cvc5 proof replay). The parser turns cvc5's `--dump-proofs --proof-format-mode=alethe`
output into a structured `AletheProof`; it decides nothing, so it is sound on its own,
and these tests pin that it reads real cvc5 output correctly.

The fixtures are **verbatim cvc5 1.x output** (from `--proof-granularity=dsl-rewrite`),
not hand-written, so they exercise the exact surface syntax we must handle: `:named`
term sharing, `(cl …)` clauses, `:rule`/`:premises`/`:args` keyword tails, the leading
`unsat` line, and the wrapping `( … )` list. If a future cvc5 changes the format, these
break loudly rather than silently mis-parsing.
-/

open Crush.Alethe Crush.SMT

/-- A complete, small Alethe proof: `x = y`, `y = 3`, `x ≠ 3` is unsat. Verbatim cvc5
output. 3 assumptions, 13 steps, no subproofs, ending in the empty clause. -/
def linearProof : String :=
"unsat
(
(assume a0 (! (= x y) :named @p_1))
(assume a1 (! (= y 3) :named @p_2))
(assume a2 (! (not (! (= x 3) :named @p_3)) :named @p_4))
(step t0 (cl (not (! (= @p_4 false) :named @p_5)) (not @p_4) false) :rule equiv_pos2)
(step t1 (cl @p_3) :rule trans :premises (a0 a1))
(step t2 (cl (! (= 3 3) :named @p_6)) :rule refl)
(step t3 (cl (= @p_3 @p_6)) :rule cong :premises (t1 t2))
(step t4 (cl (= @p_4 (! (not @p_6) :named @p_7))) :rule cong :premises (t3))
(step t5 (cl (= @p_6 true)) :rule evaluate)
(step t6 (cl (= @p_7 (! (not true) :named @p_8))) :rule cong :premises (t5))
(step t7 (cl (= @p_8 false)) :rule evaluate)
(step t8 (cl (= @p_7 false)) :rule trans :premises (t6 t7))
(step t9 (cl @p_5) :rule trans :premises (t4 t8))
(step t10 (cl false) :rule resolution :premises (t0 t9 a2))
(step t11 (cl (not false)) :rule false)
(step t12 (cl) :rule resolution :premises (t10 t11))
)"

/-- cvc5's `(error …)` reply when a proof cannot be produced in Alethe — the shape
seen on datatype-exhaustiveness goals. Must parse as `none`, not crash or mis-read. -/
def errorReply : String :=
"unsat
(
(error \"Proof unsupported by Alethe: contains operator DUMMY_SKOLEM\"))"

/-- The parse, computed once. `Option.getD` with an empty proof keeps the accessors
total; `parses` records whether it actually succeeded. -/
def linear : AletheProof := (parseProof linearProof).getD { commands := #[] }

/-! ## The linear proof parses with the expected structure -/

/-- info: (some 3, 13, 0) -/
#guard_msgs in
#eval ((parseProof linearProof).map (·.stats.1), linear.stats.2.1, linear.stats.2.2)

-- The proof ends in the empty clause — its conclusion `false`.
/-- info: true -/
#guard_msgs in
#eval linear.emptyClauseStep?.isSome

-- Premises are read: `t1` (`x = 3` by transitivity) cites `a0` and `a1`.
/-- info: #["a0", "a1"] -/
#guard_msgs in
#eval
  match linear.commands.find? (fun | .step id .. => id == "t1" | _ => false) with
  | some (.step _ _ _ prem _) => prem
  | _ => #[]

-- `:named` sharing is stripped: an assumption's term is the bare formula, not a
-- `(! … :named …)` wrapper. `a0` is `(= x y)`.
/-- info: "(= x y)" -/
#guard_msgs in
#eval
  match linear.commands.find? (fun | .assume id _ => id == "a0" | _ => false) with
  | some (.assume _ term) => toString term
  | _ => "not found"

/-! ## The distinct rule set is what a checker must cover -/

/-- info: #["equiv_pos2", "trans", "refl", "cong", "evaluate", "resolution", "false"] -/
#guard_msgs in
#eval linear.rules

/-! ## An `(error …)` reply is `none`, not a mis-parse

This is the soundness-relevant case: when cvc5 cannot produce an Alethe proof (as for
finite-domain exhaustiveness), the replay layer must see `none` and fall back, never a
partial proof it might treat as valid. -/

/-- info: true -/
#guard_msgs in
#eval (parseProof errorReply).isNone
