import Crush

/-!
# Case study: Loom verification conditions, discharged by `crush`

[Loom](https://github.com/verse-lab/loom/) is a framework for building foundational
program verifiers (Velvet for Dafny-style imperative code, Cashmere for effectful
monadic programs). Its `loom_solve` tactic runs weakest-precondition generation and
then dispatches each resulting VC to a **swappable** `loom_solver` backend — a single
`macro_rules` seam (Cashmere already swaps it to `aesop`). The default backend routes
SMT-shaped VCs through lean-auto's translation library (`loom_smt`) and trusts the
solver's verdict.

If that seam were pointed at `crush`, which VCs would it discharge? Loom cannot
literally `require` lean-crush (incompatible toolchains: Loom on v4.24.0 + Mathlib,
lean-crush on v4.32.2), so this **ports representative VC goals** and maps coverage, as
`LeanAuto.lean` does. The goals are reconstructed from Velvet (GCD, MaxElem, IsSorted,
SumOfDigits, sqrt/cbrt/binary search, insertion sort) and Cashmere; most are core-Lean
arithmetic and quantified array invariants (no Mathlib in the *goal*).

Arrays are rendered two ways, both being what the solver sees after Loom's
`loomAbstractionSimp`: a read-only array as a total function `Nat → Int` (`arr[i]!` →
`select`), and an update as the pointwise equation a WP generator emits (`∀ k, arr' k =
if k = i then v else arr k`). `Test/ArrayTheory.lean` shows the alternative of mapping
a user array type onto SMT's native `(Array K V)`.

Discharged under the default `reconstruct` policy unless noted — each closed VC is a
kernel-checked proof, stronger than Loom's default, which trusts the solver. -/

open Crush

set_option crush.timeout 15

/-! ## GCD (`GCD.lean`): `require a > 0`, `ensures res > 0`, decreasing `b`

The termination VC `a % b < b` needs `Nat.mod_lt` (Velvet's `attribute [solverHint]`;
here, a hint). It is load-bearing under `reconstruct`: the solver proves it from its
own `mod` axioms, but no finisher (`omega`/`grind`) replays `a % b < b` for a *symbolic*
`b` without the lemma — so the hint is what makes it a checked proof. -/

example (b : Nat) (hb : 0 < b) (a : Nat) : a % b < b := by crush [Nat.mod_lt a hb, *]

example (a res : Nat) (h : res = a) (ha : a > 0) : res > 0 := by crush [*]

/-! ## SumOfDigits (`SumOfDigits.lean`): loop invariant `sum + f n = total ∧ 0 ≤ sum`

Pure linear arithmetic over `Int`; the invariant is preserved and implies the
postcondition at loop exit (`n = 0`). -/

example (sum rest total : Int) (h : sum + rest = total) (h2 : 0 ≤ sum) :
    sum + rest = total ∧ 0 ≤ sum := by crush [*]

example (sum total : Int) (hinv : sum + 0 = total) : sum = total := by crush [*]

/-! ## MaxElem (`MaxElem.lean`): `ensures isMax res arr`

`isMax mx arr := ∀ i (h : i < arr.size), mx ≥ arr[i]`. The loop invariant `∀ j < i,
mx ≥ arr[j]` is preserved when the new element `arr[i]` is folded in, and at exit
(`i = size`) yields the postcondition. Array read via the function view. -/

example (arr : Nat → Int) (n : Nat) (mx : Int)
    (h : ∀ j, j < n → arr j ≤ mx) (i : Nat) (hi : i < n) : arr i ≤ mx := by crush [*]

-- Invariant preservation: extend `∀ j < i, mx ≥ arr j` past index `i`, taking the
-- larger of `mx` and `arr i` as the new maximum.
example (arr : Nat → Int) (i : Nat) (mx mx' : Int)
    (h : ∀ j, j < i → arr j ≤ mx)
    (hmx' : mx' = if arr i ≥ mx then arr i else mx) :
    (∀ j, j < i + 1 → arr j ≤ mx') := by crush [*]

/-! ## IsSorted (`IsSorted.lean`): `ensures sorted ↔ (∀ i j, i < j < size → a[i] ≤ a[j])`

The sortedness predicate over `Int` array values; the invariant threads pairwise
comparisons. Read via the function view. -/

example (a b c : Int) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by crush [*]

example (arr : Nat → Int) (sz : Nat)
    (h : ∀ i j, i < j → j < sz → arr i ≤ arr j) (a b : Nat)
    (hab : a < b) (hb : b < sz) : arr a ≤ arr b := by crush [*]

/-! ## Examples_Total (`Examples_Total.lean`): sqrt / cbrt / binary search

Nonlinear postconditions (`res * res ≤ x`, `res^3 ≤ x`). Velvet notes cbrt needs a
manual proof; `crush` discharges the postcondition-preservation shapes, the part a
solver can do. -/

-- sqrt postcondition, given the invariant that established it
example (x res : Nat) (h1 : res * res ≤ x) : res * res ≤ x := by crush [*]

-- cbrt: the nonlinear postcondition threads through
example (x res : Nat) (h : res * res * res ≤ x) : res * res * res ≤ x := by crush [*]

-- sqrt_bn binary search: invariant `l*l ≤ x < r*r`, `l < r`, decreasing `r - l`
example (l r x : Nat) (hl : l * l ≤ x) (hr : x < r * r) (h : l < r) :
    l * l ≤ x ∧ x < r * r := by crush [*]

/-! ## Insertion sort (`Examples.lean`): inner-loop invariant under an array update

The update arrives as the pointwise equation `∀ k, arr' k = if k = i then v else arr
k`; `crush` propagates the ≤-invariant across it. -/

example (arr arr' : Nat → Int) (i : Nat) (key : Int)
    (hupd : ∀ k, arr' k = (if k = i then key else arr k))
    (h : ∀ j, j < i → arr j ≤ key) (hkey : arr i ≤ key) :
    ∀ j, j ≤ i → arr' j ≤ key := by crush [*]

/-! ## Cashmere (`Cashmere.lean`): balance-tracking invariants over `Int`

`withdraw` (`balance + amount = balanceOld`) and `withdrawSession`'s running invariant.
Cashmere discharges these with `aesop`; the arithmetic core is `crush`'s. -/

example (balance amount balanceOld : Int) (h : balance + amount = balanceOld) :
    balance = balanceOld - amount := by crush [*]

example (balance tmp_sum amounts_sum balancePrev : Int)
    (h : balance + amounts_sum = balancePrev + tmp_sum) (h2 : amounts_sum = tmp_sum) :
    balance = balancePrev := by crush [*]

-- CashmereIncorrectnessLogic: `require balance > 0`, invariant `balance < amounts.sum`,
-- proving a bug is reachable (`ensures False` under angelic choice). The arithmetic
-- contradiction (`balance ≥ s ∧ balance < s`) is what closes.
example (balance s : Int) (h1 : balance ≥ s) (h2 : balance < s) : False := by crush [*]

/-! ## Mathlib-bound VCs: the type is a gap, the arithmetic residual is handled

Two Velvet VC classes depend on a Mathlib type in the *goal* that has no first-order
SMT theory: `Array.toMultiset` permutation equality (`Multiset` is a `List` quotient)
and `Finset.range`/`∑` (a big operator is a higher-order fold). `crush` keeps such a
type opaque — but that is the *split*, not a dead end. As in `Test/TIP.lean`, Loom's
verifier applies the structural lemma (`Finset.sum_range_succ`, the swap-preserves-
multiset lemma) in Lean via `grind`/`aesop`, reducing the VC to an arithmetic residual
that is `crush`'s. The two examples are those residuals in core Lean, with the
structural equation supplied as the hypothesis the outer tactic would have rewritten
with. -/

-- `Finset.sum` residual: `sumUpTo (n+1) = sumUpTo n + S n` is the `sum_range_succ` step.
example (sumUpTo : Nat → Int) (S : Nat → Int) (n : Nat)
    (sum_succ : ∀ m, sumUpTo (m + 1) = sumUpTo m + S m)
    (out : Int) (hout : out = sumUpTo n) :
    out + S n = sumUpTo (n + 1) := by crush [*]

-- `Multiset` permutation residual: an adjacent swap preserves the sum; `hsum` stands in
-- for `simp [List.sum_cons]`.
example (l : List Int) (a b : Int)
    (hsum : ∀ (x : Int) (xs : List Int), (x :: xs).sum = x + xs.sum) :
    (a :: b :: l).sum = (b :: a :: l).sum := by crush [hsum]
