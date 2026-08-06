import Crush

/-!
Tests for Alethe **proof replay** (`Crush/Solver/AletheReplay.lean`) — M4 phase 3.

The core-directed finisher hands the whole goal to one tactic. That fails when the argument
is a long chain of small inferences no tactic re-finds in one shot. cvc5's Alethe proof
*is* that chain, already found, so replay walks it: each step's clause is restated as a
Lean proposition, proved from its premises' proofs, and carried forward; the final empty
clause is `False`, discharged against the negated goal by `Classical.byContradiction`.

**Soundness does not depend on rule coverage.** Every step is proved by a Lean tactic and
checked by the kernel; the Alethe rule name only picks which tactic to try first. A step
that cannot be replayed makes replay *decline*, and the finisher ladder runs instead — no
path lets an unreplayed certificate close a goal. The negative tests below pin that.

The goals here were measured (2026-08-06) to be exactly the payoff class: cvc5 returns a
hole-free proof, and the finisher ladder **fails** to reconstruct them. Before replay they
errored under the default policy.
-/

open Crush

section Payoff
set_option crush.backend "cvc5"
set_option crush.timeout 20

/-! ## Goals the finisher ladder cannot reconstruct, but replay can

Both are kernel-checked: `#print axioms` shows the standard-library trio and **no**
`crushSorry`, so the solver is outside the trusted base. -/

/-- Boolean pigeonhole: four `Bool`s, so two must agree. cvc5's proof is ~62 steps across
`cong`/`resolution`/`trans`/`rare_rewrite`/…; the single-shot ladder cannot find it. -/
theorem bool_pigeonhole (p q r s : Bool) :
    p = q ∨ p = r ∨ p = s ∨ q = r ∨ q = s ∨ r = s := by crush

/-- info: 'bool_pigeonhole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bool_pigeonhole

/-- EUF conflict: `a = b` forces `f a = f b`, contradicting `f a = 1` and `f b = 2`. Needs a
congruence step plus a literal evaluation — a 22-step chain. -/
theorem euf_conflict (f : Int → Int) (a b c : Int)
    (h1 : f a = 1) (h2 : f b = 2) (h3 : f c = 3) (hab : a = b) : False := by crush

/-- info: 'euf_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms euf_conflict

end Payoff

/-! ## Replay declines rather than trusting

Each case below is one where replay cannot produce a proof. The goal must **error**, not
close — pinned with `#guard_msgs`, so a regression that let a certificate be taken on faith
fails the build. -/

section Declines
set_option crush.backend "cvc5"
set_option crush.timeout 20

inductive Three where | a | b | c

-- Finite-domain exhaustiveness over a *datatype*. cvc5 answers `unsat` but cannot express
-- the argument in Alethe — it replies `(error "… DUMMY_SKOLEM")`, so there is no
-- certificate at all. Replay declines and the ladder cannot replay it either, so this
-- errors: the case a checker fundamentally *cannot* reach, not a coverage gap.
/-- error: crush: solver reported `unsat`, but reconstruction failed -/
#guard_msgs(error, substring := true) in
example (w x y z : Three) : w = x ∨ w = y ∨ w = z ∨ x = y ∨ x = z ∨ y = z := by crush

-- Nonlinear arithmetic: cvc5 cannot prove this at all (it times out where z3's nlsat
-- succeeds), so there is no certificate to replay.
/-- error: crush -/
#guard_msgs(error, substring := true) in
example (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by crush

-- A goal that is simply **false**: the solver returns `sat`, so replay never runs. Pins
-- that the machinery cannot manufacture a proof of a non-theorem.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (p q : Bool) : p = q := by crush

/-! ### Declining a `forall_inst` step still closes the goal

Quantifier instantiation is a `subproof` block whose inner `forall_inst` step is justified by
its `:args` witness, not its premises. Replay declines it (a tactic handed that step cannot
close it honestly — an earlier revision let one "succeed" with a term only the final *kernel*
rejected, after replay had reported success). The finisher ladder then closes the goal, so
the decline is invisible except in the trace, and the result is still kernel-checked. -/
theorem forall_inst_falls_back (f : Int → Int) (h : ∀ x, f x = 0) : f 5 = 0 := by crush

/-- info: 'forall_inst_falls_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forall_inst_falls_back

end Declines

/-! ## Replay is off by default for z3, and can be disabled

z3 emits no Alethe proof, so replay is a no-op there and the ladder does the work — the
same goals close either way. `crush.proofReplay false` turns replay off explicitly; a goal
the ladder can handle is unaffected. -/

section Toggle
set_option crush.timeout 20

-- z3 (default backend): no certificate, ladder reconstructs as before.
theorem z3_unaffected (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'z3_unaffected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms z3_unaffected

-- With replay explicitly disabled, cvc5 falls back to the ladder.
set_option crush.backend "cvc5" in
set_option crush.proofReplay false in
theorem replay_disabled (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'replay_disabled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replay_disabled

end Toggle
