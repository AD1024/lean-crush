import Crush
import Mathlib

/-!
# Case study: crush on mathlib-scale goals
-/

open Crush

set_option crush.trust "trust"
set_option crush.timeout 15

/-! ## Nonlinear arithmetic

z3's `nlsat` decides these; no general Lean tactic can, and `nlinarith` needs a manual
`sq_nonneg` witness that crush's translation avoids by sending the raw polynomial. -/

section Nonlinear

/-- AM-GM: `2ab ≤ a² + b²`. -/
theorem amgm (a b : Int) : 2 * a * b ≤ a * a + b * b := by crush

/-- Three-variable AM-GM. -/
theorem amgm3 (a b c : Int) : a * b + b * c + c * a ≤ a * a + b * b + c * c := by crush

/-- Product-sign dichotomy: a disjunctive conclusion, dispatched by case-split on sign. -/
theorem prod_sign (a b : Int) (h : 0 < a * b) :
    (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by crush

/-- Sum of squares is zero only at the origin. -/
theorem sq_sum_zero (a b : Int) (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by crush

/-- Cubic lower bound in a bounded regime. -/
theorem cube_lower (a : Int) (h : 1 ≤ a) : a ≤ a * a * a := by crush

/-- Square is monotone over the non-negatives. -/
theorem sq_mono (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * a ≤ b * b) :
    a ≤ b := by crush

end Nonlinear

/-! ## Quantifier + uninterpreted function -/

section QuantifierUF

/-- Involution implies injectivity: needs `h` instantiated at both `a` and `b`, chained
through `f (f a) = a`, `f (f b) = b`, `f a = f b`. -/
theorem invol_inj (f : Int → Int) (h : ∀ x, f (f x) = x) (a b : Int)
    (hab : f a = f b) : a = b := by crush

end QuantifierUF

/-! ## Array read-over-write

The pointwise-update *lambda* is opaque to the first-order path (crush treats it as an
uninterpreted function, so the goal is not provable). The hypothesis form —
`∀ k, arr' k = if k = i then v else arr k` — does translate; see `Loom.lean`. -/

/-! ## Mathlib datatype: `BinaryTree`

Real recursive inductive from `Mathlib.Data.Tree.Basic`. -/

/-- Exhaustiveness with witnesses. The `∃ v l r` packaging defeats `grind`/`aesop`;
z3 closes it from the `declare-datatypes` constructor set. -/
theorem bt_exhaust (t : BinaryTree Int) :
    t = .nil ∨ ∃ v l r, t = .node v l r := by crush

/-! ## Mathlib datatype: `SignType`

Regression pin for the `OfNat` fix in `Translate.lean`: `(0 : SignType)` is the
constructor `SignType.zero`, not the `Int` literal `0` (which would clash sorts). -/

/-- `SignType` exhaustiveness. `grind` also closes this — kept for the translation, not
as a discriminator. -/
theorem sign_exhaust (s : SignType) :
    s = 0 ∨ s = SignType.neg ∨ s = SignType.pos := by crush
