import Crush

/-!
Milestone-2 tests: theory correctness, especially the Nat→Int soundness
obligations from `Doc/PLAN.md` §10. Each `example`/`theorem` that elaborates is a
passing test; the negative cases use `first | (crush; done) | sorry` so a
regression (crush wrongly closing a false goal) turns the `sorry` into a *closed*
proof and the file's `sorry` warning disappears — a signal we watch for.
-/

open Crush

set_option crush.trust "trust"

/-! ## Nat well-formedness (non-negativity) -/

-- A bare `Nat` variable must carry `≥ 0` in the encoding.
theorem nat_nonneg (n : Nat) : 0 ≤ n := by crush

-- Truncated subtraction: `n - 1 ≤ n` always, and `n - (n+1) = 0`.
theorem nat_sub_le : ∀ n : Nat, n - 1 ≤ n := by crush
theorem nat_sub_trunc : ∀ n : Nat, n - (n + 1) = 0 := by crush

-- Nat-valued uninterpreted function result is non-negative.
theorem nat_fun_nonneg (f : Nat → Nat) (n : Nat) : 0 ≤ f n := by crush

/-! ## Negative cases — must be REJECTED, not closed -/

-- FALSE: n = 0 gives 0 - 1 = 0, so `0 < 0` is false. The pre-fix naive `Int`
-- translation wrongly proved this; the `≥0` guard + truncated `sub` fix it.
theorem must_reject_sub : ∀ n : Nat, n - 1 < n := by
  first | (crush; done) | sorry

/-! ## Int arithmetic (signed, no truncation) -/

theorem int_sub_neg : ∀ x : Int, x - (x + 1) = -1 := by crush
theorem int_order (x y : Int) (h : x < y) : x + 1 ≤ y := by crush

/-! ## Int division/mod — Lean's default `Int./`/`%` are Euclidean (remainder
    ≥ 0), matching SMT-LIB `div`/`mod`, so the direct mapping is sound. -/

theorem int_ediv : ((-7 : Int) / 2) = -4 := by crush
theorem int_emod : ((-7 : Int) % 2) = 1 := by crush
theorem int_mod_nonneg : ∀ x : Int, x % 2 ≥ 0 := by crush

-- FALSE under Euclidean division (that would be truncated T-division): rejected.
theorem must_reject_tdiv : ((-7 : Int) / 2) = -3 := by
  first | (crush; done) | sorry

/-! ## if-then-else -/

theorem ite_prop (x : Int) : (if x > 0 then x else -x) ≥ 0 := by crush
theorem ite_bool (b : Bool) (x y : Int) (h : b = true) : (if b then x else y) = x := by crush

/-! ## Datatypes: enumerations and structures -/

inductive Color where | red | green | blue

theorem col_distinct : Color.red ≠ Color.green := by crush
theorem col_cases (c : Color) : c = Color.red ∨ c = Color.green ∨ c = Color.blue := by crush

structure Point where
  x : Int
  y : Int

theorem pt_proj (a b : Int) : (Point.mk a b).x = a := by crush
theorem pt_cong (p q : Point) (h : p = q) : p.x = q.x := by crush
