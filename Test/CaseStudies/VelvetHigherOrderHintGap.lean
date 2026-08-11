import Crush
import Lean.Elab.Tactic.Grind

/-!
A higher-order solver-hint obligation extracted from Velvet.

The hint quantifies over a predicate `p : Nat -> Bool`. This checks that Crush
uses the concrete predicate lambda as pattern evidence and sends bounded ground
instances instead of leaving the obligation to solver E-matching.
-/

open Crush

private theorem filterSumSnoc (arr : Array Nat) (p : Nat → Bool) :
    ∀ i, i < arr.size →
      (Array.filter p (Array.extract arr 0 i)).sum +
          (if p arr[i]! then arr[i]! else 0) =
        (Array.filter p (Array.extract arr 0 (i + 1))).sum := by
  intro i hi
  have extractApp :
      Array.extract arr 0 (i + 1) = Array.extract arr 0 i ++ #[arr[i]!] := by
    have h := Array.extract_succ_right (as := arr) (i := 0) (j := i)
      (Nat.zero_lt_succ i) hi
    rw [← getElem!_pos arr i hi] at h
    simpa only [Array.push_eq_append] using h
  rw [extractApp]
  rw [Array.filter_append]
  · simp
    grind
  · rw [Array.size_append]

private theorem filterSumExtractSize (arr : Array Nat) (p : Nat → Bool) :
    (Array.filter p (Array.extract arr 0 arr.size)).sum =
      (Array.filter p arr).sum := by
  simp

theorem filterHintDirectLean
    (arr : Array Nat) (i s : Nat)
    (hinv :
      s = (Array.filter (fun x => decide (x % 2 = 0)) (arr.extract 0 i)).sum)
    (hbound : i < arr.size)
    (heven : ¬(arr[i]! % 2 != 0) = true) :
    (Array.filter (fun x => decide (x % 2 = 0)) (arr.extract 0 i)).sum +
        arr[i]! =
      (Array.filter (fun x => decide (x % 2 = 0))
        (arr.extract 0 (i + 1))).sum := by
  have h := filterSumSnoc arr
    (fun x => decide (x % 2 = 0)) i hbound
  simp_all

theorem filterHintContextCrush
    (arr : Array Nat) (i s : Nat)
    (hinv :
      s = (Array.filter (fun x => decide (x % 2 = 0)) (arr.extract 0 i)).sum)
    (hbound : i < arr.size)
    (heven : ¬(arr[i]! % 2 != 0) = true) :
    (Array.filter (fun x => decide (x % 2 = 0)) (arr.extract 0 i)).sum +
        arr[i]! =
      (Array.filter (fun x => decide (x % 2 = 0))
        (arr.extract 0 (i + 1))).sum := by
  crush [filterSumSnoc, filterSumExtractSize, *]
