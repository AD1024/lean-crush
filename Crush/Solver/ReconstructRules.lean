import Lean
import Crush.Solver.ReconstructAttr

open Lean

/-!
# Built-in proof-reconstruction rules

These are ordinary Lean theorems registered through the same public mechanism available
to downstream libraries. The reconstruction engine does not inspect `Nat`, multiplication,
or a fixed polynomial degree.
-/

namespace Crush

universe u v

/-- Reconstruct a dependent function witness from pointwise witnesses.

SMT skolemization proves this shape directly, but a checked Lean proof must materialize
the Skolem function. This theorem keeps that bridge in ordinary kernel-checked Lean. -/
@[crush_reconstruct]
theorem existsPiOfForallExists {α : Sort u} {β : α → Sort v}
    {p : (x : α) → β x → Prop} (h : ∀ x, ∃ y, p x y) :
    ∃ f : (x : α) → β x, ∀ x, p x (f x) :=
  ⟨fun x => Classical.choose (h x), fun x => Classical.choose_spec (h x)⟩

@[crush_reconstruct]
theorem natLeSquare (n : Nat) : n ≤ n * n := by
  simpa [Nat.pow_succ] using Nat.le_pow (a := n) (b := 2) (by decide)

@[crush_reconstruct]
theorem natCubeMono {a b : Nat} (h : a ≤ b) : a * a * a ≤ b * b * b :=
  Nat.mul_le_mul (Nat.mul_le_mul h h) h

@[crush_reconstruct]
theorem natLeCube (n : Nat) : n ≤ n * n * n := by
  simpa [Nat.pow_succ] using Nat.le_pow (a := n) (b := 3) (by decide)

@[crush_reconstruct]
theorem natLePredCases {i j : Nat} (h : j ≤ i - 1) : j < i ∨ j = 0 := by
  omega

/-- Extend an invariant when every new element is either old or the current boundary.

This is independent of the index datatype and relation. Concrete domains only need to
provide their one-step coverage fact. -/
theorem invariantOfEarlierOrEq {ι : Sort u} {R : ι → ι → Prop} {P : ι → Prop}
    {current j : ι} (previous : ∀ k, R k current → P k) (atCurrent : P current)
    (cases : R j current ∨ j = current) : P j := by
  rcases cases with earlier | rfl
  · exact previous j earlier
  · exact atCurrent

/-- Predicate-level `Nat` successor extension, independent of the invariant's contents. -/
theorem natSuccInvariant {P : Nat → Prop} {i j : Nat}
    (previous : ∀ k < i, P k) (current : P i) (h : j < i + 1) : P j := by
  apply invariantOfEarlierOrEq previous current
  exact Nat.lt_succ_iff_lt_or_eq.mp (by simpa using h)

/-- Predicate-level predecessor projection. The explicit base case makes the theorem valid
for every predicate, rather than baking arithmetic facts into the structural rule. -/
theorem natPredInvariant {P : Nat → Prop} {i j : Nat}
    (base : P 0) (previous : ∀ k < i, P k) (h : j ≤ i - 1) : P j := by
  rcases natLePredCases h with h | rfl
  · exact previous j h
  · exact base

@[crush_reconstruct]
theorem natSquareSuccInvariant {x i j : Nat}
    (previous : ∀ k < i, k * k ≤ x) (current : i * i ≤ x) (h : j < i + 1) :
    j * j ≤ x :=
  natSuccInvariant (P := fun k => k * k ≤ x) (i := i) (j := j) previous current h

@[crush_reconstruct]
theorem natCubeSuccInvariant {x i j : Nat}
    (previous : ∀ k < i, k * k * k ≤ x) (current : i * i * i ≤ x)
    (h : j < i + 1) : j * j * j ≤ x :=
  natSuccInvariant (P := fun k => k * k * k ≤ x) (i := i) (j := j) previous current h

@[crush_reconstruct]
theorem natSquarePredInvariant {x i j : Nat}
    (previous : ∀ k < i, k * k ≤ x) (h : j ≤ i - 1) : j * j ≤ x :=
  natPredInvariant (P := fun k => k * k ≤ x) (i := i) (j := j)
    (by omega) previous h

@[crush_reconstruct]
theorem natCubePredInvariant {x i j : Nat}
    (previous : ∀ k < i, k * k * k ≤ x) (h : j ≤ i - 1) : j * j * j ≤ x :=
  natPredInvariant (P := fun k => k * k * k ≤ x) (i := i) (j := j)
    (by omega) previous h

@[crush_reconstruct]
theorem natSquareDown {x a b : Nat} (bound : b * b ≤ x) (h : a ≤ b) :
    a * a ≤ x :=
  Nat.le_trans (Nat.mul_self_le_mul_self h) bound

@[crush_reconstruct]
theorem natCubeDown {x a b : Nat} (bound : b * b * b ≤ x) (h : a ≤ b) :
    a * a * a ≤ x :=
  Nat.le_trans (natCubeMono h) bound

/-- If two loop bounds are at most one apart, a value below the predecessor of the upper
bound is below the lower bound. Put the gap premise first so backward search learns `upper`
from the loop-exit hypothesis before proving the intermediate inequality. -/
@[crush_reconstruct]
theorem natLeOfSubGapAtMostOne {value lower upper : Nat}
    (gap : ¬1 < upper - lower) (h : value ≤ upper - 1) : value ≤ lower := by
  omega

@[crush_reconstruct]
theorem natSquareMax {x i j : Nat} (hj : j * j ≤ x) (hi : x < i * i) :
    j ≤ i - 1 := by
  have hsquares : j * j < i * i := Nat.lt_of_le_of_lt hj hi
  have hji : j < i := Nat.mul_self_lt_mul_self_iff.mp hsquares
  omega

@[crush_reconstruct]
theorem natCubeMax {x i j : Nat} (hj : j * j * j ≤ x) (hi : x < i * i * i) :
    j ≤ i - 1 := by
  have hcubes : j * j * j < i * i * i := Nat.lt_of_le_of_lt hj hi
  have hji : j < i := by
    apply Classical.byContradiction
    intro h
    have hij : i ≤ j := by omega
    have := natCubeMono hij
    omega
  omega

attribute [crush_reconstruct]
  Nat.lt_succ_iff_lt_or_eq
  Nat.mul_self_le_mul_self
  Nat.mul_self_lt_mul_self_iff
  Int.mul_self_le_mul_self

end Crush
