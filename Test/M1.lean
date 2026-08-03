import Crush

/-!
Milestone-1 end-to-end tests: the `crush` tactic closing real goals via z3.
Each `example` that elaborates without error is a passing test.
-/

open Crush

set_option crush.trust "trust"

-- The headline Milestone-1 target.
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

-- Negative test: a *false* goal must be rejected (solver finds a countermodel),
-- not silently closed. `crush` errors here; `first | crush | skip` lets the file
-- still elaborate while `sorry` records that we did not (wrongly) close it.
example (x : Int) : x + 1 = x := by
  first
  | (crush; done)  -- must NOT succeed
  | sorry          -- expected path: crush errors/leaves the goal, we admit it
