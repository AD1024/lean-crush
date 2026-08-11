import Crush
import Lean.Elab.Tactic.Grind
import Lean.Elab.Tactic.Omega

/-!
Array obligations extracted from Velvet verification conditions.

The direct proofs establish the intended semantics independently. The `crush`
versions are regressions for finite Array lowering: bounded and defaulting reads
share one representation, and `set!` uses SMT read-over-write semantics.
-/

open Crush

set_option crush.timeout 3

theorem boundedArrayReadLean
    (arr : Array Int) (n : Nat) (mx : Int)
    (hinv : ∀ j, j < n → arr[j]! ≤ mx)
    (hdone : n = arr.size) :
    ∀ j, (h : j < arr.size) → arr[j]'h ≤ mx := by
  intro j hj
  rw [← getElem!_pos arr j hj]
  exact hinv j (by omega)

theorem boundedArrayReadCrush
    (arr : Array Int) (n : Nat) (mx : Int)
    (hinv : ∀ j, j < n → arr[j]! ≤ mx)
    (hdone : n = arr.size) :
    ∀ j, (h : j < arr.size) → arr[j]'h ≤ mx := by
  crush

private theorem arrayGetSetInt
    (i j : Nat) (val : Int) (arr : Array Int) :
    i < arr.size →
      (arr.set! j val)[i]! = if i = j then val else arr[i]! := by
  intro hi
  by_cases hij : i = j
  · subst j
    simpa using Array.getElem!_set!_self arr i val hi
  · rw [if_neg hij]
    exact Array.getElem!_set!_ne arr j i val (fun hji => hij (Eq.symm hji))

theorem nestedArraySetLean
    (arr : Array Int) (n mind : Nat)
    (hmind : mind ≤ n)
    (hmind0 : mind ≠ 0)
    (hnsize : n ≤ arr.size)
    (hnne : n ≠ arr.size)
    (hswap : arr[mind]! < arr[mind - 1]!)
    (hsorted :
      ∀ i j, i < j → j ≤ n → j ≠ mind → arr[i]! ≤ arr[j]!) :
    ∀ i j,
      i < j →
      j ≤ n →
      j ≠ mind - 1 →
        ((arr.set! (mind - 1) arr[mind]!).set! mind arr[mind - 1]!)[i]! ≤
        ((arr.set! (mind - 1) arr[mind]!).set! mind arr[mind - 1]!)[j]! := by
  intro i j hij hjn hjne
  have hmind : mind < arr.size := by omega
  have hpred : mind - 1 < arr.size := by omega
  have hpredne : mind - 1 ≠ mind := by omega
  have hi : i < arr.size := by omega
  have hj : j < arr.size := by omega
  simp only [arrayGetSetInt, Array.size_set!, hi, hj]
  by_cases him : i = mind <;>
    by_cases hip : i = mind - 1 <;>
      by_cases hjm : j = mind <;>
        simp [him, hip, hjm, hjne, hpredne]
  all_goals first
    | omega
    | apply hsorted (mind - 1) j <;> omega
    | apply hsorted mind j <;> omega
    | apply hsorted i (mind - 1) <;> omega
    | apply hsorted i j <;> omega

theorem nestedArraySetCrush
    (arr : Array Int) (n mind : Nat)
    (hmind : mind ≤ n)
    (hmind0 : mind ≠ 0)
    (hnsize : n ≤ arr.size)
    (hnne : n ≠ arr.size)
    (hswap : arr[mind]! < arr[mind - 1]!)
    (hsorted :
      ∀ i j, i < j → j ≤ n → j ≠ mind → arr[i]! ≤ arr[j]!) :
    ∀ i j,
      i < j →
      j ≤ n →
      j ≠ mind - 1 →
        ((arr.set! (mind - 1) arr[mind]!).set! mind arr[mind - 1]!)[i]! ≤
        ((arr.set! (mind - 1) arr[mind]!).set! mind arr[mind - 1]!)[j]! := by
  crush
