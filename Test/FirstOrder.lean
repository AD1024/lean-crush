import Crush

/-!
End-to-end tests for the first-order path: the `crush` tactic closing real goals
via z3. Each `theorem` that elaborates without error is a passing test.

Negative tests — goals that are *false* and must be rejected rather than closed —
are wrapped in `#guard_msgs`, which pins the rejection message. If a regression
ever lets `crush` close one of them, the expected error is not produced and the
build **fails**. `substring := true` matches only the stable prefix, so the
solver-dependent counterexample text does not make the test brittle.
-/

open Crush

set_option crush.trust "trust"

-- The basic case: a quantified linear-arithmetic identity.
example : ∀ x : Int, x + 0 = x := by crush

-- Uses a hypothesis.
example (a b : Int) (h : a = b) : b = a := by crush

-- Propositional.
example (p q : Prop) (hp : p) (hpq : p → q) : q := by crush

-- Linear arithmetic with a hypothesis.
example (x y : Int) (h : x ≤ y) : x < y + 1 := by crush

-- Uninterpreted function congruence.
example (f : Int → Int) (a b : Int) (h : a = b) : f a = f b := by crush

-- A true arithmetic fact.
example (x : Int) : x + 1 > x := by crush

-- Negative test: a *false* goal must be rejected (the solver finds a countermodel),
-- not silently closed.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_false_arith (x : Int) : x + 1 = x := by crush
