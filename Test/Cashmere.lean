import Crush

/-!
Regression for the Cashmere incorrectness-logic VC whose existential witness is
created by a two-lemma forward chain.
-/

open Crush

set_option crush.timeout 3
set_option crush.trust "reconstruct"

theorem cashmere_sum_lt {y : Int} (x : Int) :
    x < y → x < (([Int.toNat y] : List Nat).sum : Int) := by
  intro h
  simpa [List.sum] using Int.lt_of_lt_of_le h (Int.le_max_left y 0)

theorem cashmere_balance_lt (x : Int) : x < x + 1 :=
  Int.lt_succ x

theorem cashmere_exists_larger_balance (x : Int) (_h : x > 0) :
    ∃ amounts : List Nat, x < (amounts.sum : Int) := by
  crush [cashmere_sum_lt, cashmere_balance_lt, *]

axiom cashmereNonEmpty : List Nat → Prop

axiom cashmereTailLength :
  ∀ q : List Nat, cashmereNonEmpty q → q.tail.length < q.length

theorem cashmereEmpSum : (([] : List Nat).sum : Int) = 0 := by
  rfl

-- The unrelated quantified hint used to trigger an unbounded list-tail
-- E-matching loop in Z3. The empty list is already a sufficient witness.
theorem cashmere_exists_bounded_balance (x : Int) (h : 0 ≤ x) :
    ∃ amounts : List Nat, (amounts.sum : Int) ≤ x := by
  crush [cashmereTailLength, cashmereEmpSum, *]
