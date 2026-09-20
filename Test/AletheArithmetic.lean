import Crush
import Init.Data.Int.Order

/-!
Live cvc5 regressions for square signs, absolute-value comparison, and expanded
sign tests in arithmetic subproofs. Require Alethe replay without core fallback.
-/

namespace AletheArithmetic

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"

-- Exercises `la_mult_sign`.
/-- [crush.result] proof replay succeeded; no axiom used -/
#guard_msgs(trace, substring := true) in
set_option trace.crush.result true in
theorem square_positive (x : Int) (h : x ≠ 0) : x * x > 0 := by
  crush

/-- info: 'AletheArithmetic.square_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_positive

-- Exercises `rare_rewrite "arith-abs-int-gt"` and arithmetic subproof discharge.
/-- [crush.result] proof replay succeeded; no axiom used -/
#guard_msgs(trace, substring := true) in
set_option trace.crush.result true in
theorem square_above_one (x : Int) (h : 1 < x) : 1 < x * x := by
  crush

/-- info: 'AletheArithmetic.square_above_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_above_one

-- Exercises `la_mult_abs_comparison` in the square-root loop's upper bound.
/-- [crush.result] proof replay succeeded; no axiom used -/
#guard_msgs(trace, substring := true) in
set_option trace.crush.result true in
theorem square_root_upper_bound (i x : Nat) (h : x < i * i) :
    ∀ j : Nat, j * j ≤ x → j ≤ i - 1 := by
  crush

/-- info: 'AletheArithmetic.square_root_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_root_upper_bound

-- An ambient comparison omitted from the selected facts cannot justify the goal.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example (x y : Nat) (h : x < y) : x * x < y * y := by
  crush []

end AletheArithmetic

theorem square_above_one (x : Int) (h : 1 < x) : 1 < x * x := by
  have hx : 0 < x := Int.lt_trans Int.zero_lt_one h
  have hmul : 1 * x < x * x :=
    Int.mul_lt_mul_of_pos_right h hx
  rw [Int.one_mul] at hmul
  exact Int.lt_trans h hmul
