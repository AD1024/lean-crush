import Crush

/-!
Tests for proof-guided reconstruction (`Crush/Solver/ProofGuide.lean`).

cvc5 runs with `--proof-format-mode=alethe --proof-granularity=dsl-rewrite`, so
`(get-proof)` yields an Alethe proof. The guide reads it and, when the refutation turns
on **ground evaluation**, extends the finisher ladder with evaluating tactics
(`decide`/`rfl`) that the default ladder omits — `grind`/`omega`/`simp_all` reason but
do not compute.

The guide can only *add* finisher attempts. Reconstruction still succeeds only when a
Lean tactic closes the goal and the kernel accepts the term, so a misread proof costs
time, never soundness. `hole` steps (cvc5 admitting an untranslated rewrite) make the
guide `none`, so an unjustified proof licenses nothing.
-/

open Crush Crush.Alethe

/-! ## The guide, as a pure function on proof text -/

/-- A proof turning on evaluation (`str.len "ab"` → `2`) — the shape that needs the
extra finishers. Verbatim cvc5 output. -/
def evalProof : String :=
"unsat
(
(assume crush_fact_0 (! (= s_0 \"ab\") :named @p_1))
(assume crush_fact_1 (! (not (! (= (! (str.len s_0) :named @p_2) 2) :named @p_3)) :named @p_4))
(step t0 (cl (not (! (= @p_4 false) :named @p_5)) (not @p_4) false) :rule equiv_pos2)
(step t1 (cl (= @p_2 (! (str.len \"ab\") :named @p_6))) :rule cong :premises (crush_fact_0))
(step t5 (cl @p_7) :rule evaluate)
(step t15 (cl) :rule resolution :premises (t13 t14))
)"

/-- A purely logical proof — no evaluation step, so no extra finishers are warranted. -/
def logicalProof : String :=
"unsat
(
(assume crush_fact_0 (=> p q))
(assume crush_fact_1 p)
(assume crush_fact_2 (not q))
(step t0 (cl (not (=> p q)) (not p) q) :rule implies)
(step t1 (cl) :rule resolution :premises (t0 crush_fact_0 crush_fact_1 crush_fact_2))
)"

/-- A proof with a `hole` — cvc5 could not justify a rewrite in Alethe. -/
def holedProof : String :=
"unsat
(
(assume crush_fact_0 (= x y))
(step t5 (cl (= @p_6 true)) :rule hole :args (\"untranslated rewrite\"))
(step t12 (cl) :rule resolution :premises (t10 t11))
)"

-- An evaluation proof is usable and flags `needsEval`.
/-- info: (true, true) -/
#guard_msgs in
#eval ((guideOf? evalProof).isSome, (guideOf? evalProof).any (·.needsEval))

-- A logical proof is usable but does NOT ask for the evaluating finishers, so the
-- common case does not pay for `decide`.
/-- info: (true, false) -/
#guard_msgs in
#eval ((guideOf? logicalProof).isSome, (guideOf? logicalProof).any (·.needsEval))

/-! ### A `hole` makes the guide `none`

The soundness-relevant case. A holed proof contains an unjustified step, so it must not
be read as saying anything — least of all as a licence to trust. -/

/-- info: true -/
#guard_msgs in
#eval (guideOf? holedProof).isNone

-- No proof text at all (z3, or proofs off) is likewise `none`, not an error.
/-- info: true -/
#guard_msgs in
#eval (guideOf? "").isNone

-- cvc5's `(error …)` reply (it emits this for datatype-exhaustiveness goals).
/-- info: true -/
#guard_msgs in
#eval (guideOf? "unsat\n(\n(error \"Proof unsupported by Alethe\"))").isNone

/-! ## End-to-end: goals that reconstruct *only* with proof guidance

Both close under the default `reconstruct` policy with cvc5. Before proof guidance they
failed reconstruction (`grind`/`omega`/`simp_all` do not evaluate `String.length "ab"`),
so these are the payoff cases. `#print axioms` pins that they are kernel-checked. -/

section Cvc5Eval
set_option crush.backend "cvc5"
set_option crush.timeout 15

theorem str_len_eval (s : String) (h : s = "ab") : s.length = 2 := by crush

theorem str_append_eval (s t : String) (h : s ++ t = "abc") :
    (s ++ t).length = 3 := by crush

/-- info: 'str_len_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms str_len_eval

/-- info: 'str_append_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms str_append_eval

end Cvc5Eval
