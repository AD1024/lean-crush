import Crush

/-!
Tests for proof reconstruction: turning an `unsat` verdict into a *checked* Lean
proof rather than closing the goal with an axiom.

The mechanism is solver-as-oracle. The solver's real contribution is not a proof
object but a **selection**: the unsat core names which two or three of the ambient
hypotheses actually matter. That is precisely what a Lean automated tactic cannot
work out for itself, and irrelevant hypotheses are what make such tactics time out.
So we rebuild the goal with only the core hypotheses in scope and hand it to
`grind`/`omega`/`simp_all`.

When that succeeds the solver leaves the trusted computing base entirely — it was a
search heuristic, and the resulting term is kernel-checked. The assertions below are
therefore about `#print axioms`: a reconstructed theorem must **not** mention
`Crush.crushSorry`.

`propext`, `Classical.choice`, and `Quot.sound` do appear; those are Lean's own
axioms, used by `grind` and by the standard library, and are not a trust
assumption specific to this tool.
-/

open Crush

set_option crush.timeout 10

/-! ## Reconstruction succeeds — no trust axiom

Each of these is closed by a real Lean proof term. The `#guard_msgs` blocks pin the
axiom set, so a regression that silently fell back to the axiom would fail the
build rather than pass quietly. -/

section Succeeds
set_option crush.trust "reconstruct"

theorem eq_chain (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'eq_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_chain

theorem linear_arith (x y : Int) (h : x ≤ y) : x < y + 1 := by crush
/-- info: 'linear_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linear_arith

theorem propositional (p q : Prop) (hp : p) (hpq : p → q) : q := by crush
/-- info: 'propositional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms propositional

theorem uf_congruence (f : Int → Int) (a b : Int) (h : a = b) : f a = f b := by crush
/-- info: 'uf_congruence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms uf_congruence

theorem nat_truncated_sub : ∀ n : Nat, n - 1 ≤ n := by crush
/-- info: 'nat_truncated_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nat_truncated_sub

theorem quantified_uf (f : Int → Int) (h : ∀ x, f x = x + 1) : f (f 0) = 2 := by crush
/-- info: 'quantified_uf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quantified_uf

-- Core-directed selection earning its keep: six hypotheses, only two relevant.
-- Handing the whole context to `grind` is what core selection avoids.
theorem ignores_irrelevant (a b c d e f g : Int) (h1 : a = b) (h2 : b = c)
    (junk1 : d > 0) (junk2 : e > 1) (junk3 : f > 2) (junk4 : g > 3) : a = c := by crush
/-- info: 'ignores_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ignores_irrelevant

-- Theory goals also replay: the finishers know these theories natively.
theorem bitvec_add_zero (x : BitVec 8) : x + 0 = x := by crush
/-- info: 'bitvec_add_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitvec_add_zero

theorem string_assoc (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by crush
/-- info: 'string_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms string_assoc

-- Higher-order: the encoding is only used to *find* the proof; `grind` replays it
-- against the original higher-order statement.
theorem higher_order (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => x + 1) = 1 := by crush
/-- info: 'higher_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms higher_order

end Succeeds

/-! ## Reconstruction fails — the boundary

The finishers cannot replay everything the solver can prove. Nonlinear arithmetic
and finite-domain exhaustiveness (enumeration pigeonhole) are the two shapes found
so far. Under `reconstruct` this is an *error*, not a silent fallback — the whole
point of that policy is that the axiom is never used. -/

section Fails
set_option crush.trust "reconstruct"

-- Nonlinear: the solver decides `x * x = 4 ∧ x > 0 → x = 2`, `omega` is linear-only
-- and `grind` does not find it.
/-- error: crush: solver reported `unsat`, but reconstruction failed -/
#guard_msgs(error, substring := true) in
theorem nonlinear_not_replayed (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by
  crush

inductive Three where | a | b | c

-- Pigeonhole over a three-constructor enumeration. The solver gets this from
-- datatype exhaustiveness + distinctness; the finishers would need a case split the
-- core does not hand them (note the core here is *just* the negated goal).
/-- error: crush: solver reported `unsat`, but reconstruction failed -/
#guard_msgs(error, substring := true) in
theorem pigeonhole_not_replayed (w x y z : Three) :
    w = x ∨ w = y ∨ w = z ∨ x = y ∨ x = z ∨ y = z := by crush

end Fails

/-! ## `reconstructOrTrust` — the default policy

Try to reconstruct; fall back to the axiom with a warning if that fails. This gives
axiom-free proofs where possible without turning a solvable goal into an error, and
the warning makes the fallback visible rather than silent. -/

section Fallback
set_option crush.trust "reconstructOrTrust"

theorem fallback_not_needed (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'fallback_not_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fallback_not_needed

-- Not reconstructable, so the axiom is used — and the warning says so, rather than
-- the fallback being silent.
/-- warning: crush: solver reported `unsat`, but no finishing tactic could replay it -/
#guard_msgs(warning, substring := true) in
theorem fallback_used (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by crush

/-- info: 'fallback_used' depends on axioms: [crushSorry] -/
#guard_msgs in
#print axioms fallback_used

end Fallback

/-! ## `trust` — the axiom is used unconditionally

The fast path: no reconstruction attempt, so every goal costs the axiom. Kept as a
policy because reconstruction is not free and some workloads want the speed. -/

section Trust
set_option crush.trust "trust"

theorem trusted (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'trusted' depends on axioms: [crushSorry] -/
#guard_msgs in
#print axioms trusted

end Trust
