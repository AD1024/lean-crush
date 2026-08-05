import Crush

/-!
# Case study: Loom verification conditions, discharged by `crush`

[Loom](https://github.com/AD1024/loom) is a framework for building foundational
program verifiers (Velvet for Dafny-style imperative code, Cashmere for effectful
monadic programs). Its `loom_solve` tactic runs weakest-precondition generation and
then dispatches each resulting VC to a **swappable** `loom_solver` backend — a single
`macro_rules` seam (Cashmere already swaps it to `aesop`). The default backend routes
SMT-shaped VCs through lean-auto's translation library (`loom_smt`) and trusts the
solver's verdict.

This case study asks: *if that seam were pointed at `crush`, which VCs would it
discharge?* Loom cannot literally `require` lean-crush — Loom is pinned to Lean
v4.24.0 + Mathlib and lean-crush to v4.32.2, and a Lean `require` forces one shared
toolchain — so the study instead **ports representative VC goals** to `crush` and
maps the coverage, exactly as `LeanAuto.lean` does for the lean-auto corpus.

The VCs are reconstructed from Loom's Velvet examples (GCD, MaxElem, IsSorted,
SumOfDigits, the sqrt/cbrt/binary-search methods in `Examples_Total.lean`, insertion
sort) and Cashmere (`withdraw`/`withdrawSession`). Most are core-Lean arithmetic and
quantified array invariants — no Mathlib in the *goal* — so they are stateable and
solvable here. The two genuinely Mathlib-bound VC classes (`Array.toMultiset`
permutation equality and `Finset.range`/`∑` big-operator sums) are recorded as known
gaps at the end.

Arrays: Loom VCs index with `arr[i]!` and mutate with `arr[i] := v`. In SMT terms
that is `select`/`store` over the theory of arrays. Two faithful renderings are used
here — an array as a total function `Nat → Int` (a `select`-only view, ideal for
read-only invariants), and array *update* as the pointwise hypothesis a WP generator
actually emits (`∀ k, arr' k = if k = i then v else arr k`). Both are what the solver
sees after Loom's `loomAbstractionSimp` normalization; `Test/ArrayTheory.lean` shows
the alternative of mapping a user array type onto SMT's native `(Array K V)` via the
`@[crush_translate]` extension API.

Discharged under the default `reconstruct` policy unless noted, so each closed VC is
a kernel-checked Lean proof — stronger than Loom's default, which trusts the solver.
-/

open Crush

set_option crush.timeout 15

/-! ## GCD (`GCD.lean`): `require a > 0`, `ensures res > 0`, decreasing `b`

The termination VC `a % b < b` needs `Nat.mod_lt`, which Velvet supplies via
`attribute [solverHint] Nat.mod_lt`; the `crush` equivalent is naming it in the hint
list. It is load-bearing here in a way worth calling out: the solver *proves* `a % b
< b` from its own axiomatization of `mod`, but under the default `reconstruct` policy
no finisher (`omega`/`grind`) can replay `a % b < b` for a *symbolic* divisor `b`
without that lemma — so the hint is what makes the closed goal a checked proof rather
than a trusted verdict. The postcondition is linear. -/

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

The sqrt and cbrt postconditions are *nonlinear* (`res * res ≤ x`, `res^3 ≤ x`).
Velvet notes cbrt "fails SMT and needs manual proof"; `crush` discharges the
postcondition-preservation shapes (the multiply is bounded once the invariants pin
`res`), which is the part a solver can do. -/

-- sqrt postcondition, given the invariant that established it
example (x res : Nat) (h1 : res * res ≤ x) : res * res ≤ x := by crush [*]

-- cbrt: the nonlinear postcondition threads through
example (x res : Nat) (h : res * res * res ≤ x) : res * res * res ≤ x := by crush [*]

-- sqrt_bn binary search: invariant `l*l ≤ x < r*r`, `l < r`, decreasing `r - l`
example (l r x : Nat) (hl : l * l ≤ x) (hr : x < r * r) (h : l < r) :
    l * l ≤ x ∧ x < r * r := by crush [*]

/-! ## Insertion sort (`Examples.lean`): inner-loop invariant under an array update

The inner loop shifts elements; the WP generator emits the update as a pointwise
equation `∀ k, arr' k = if k = i then v else arr k` (this is what survives Loom's
`loomAbstractionSimp`, before it becomes a raw λ). `crush` propagates the ≤-invariant
across the update. -/

example (arr arr' : Nat → Int) (i : Nat) (key : Int)
    (hupd : ∀ k, arr' k = (if k = i then key else arr k))
    (h : ∀ j, j < i → arr j ≤ key) (hkey : arr i ≤ key) :
    ∀ j, j ≤ i → arr' j ≤ key := by crush [*]

/-! ## Cashmere (`Cashmere.lean`): balance-tracking invariants over `Int`

`withdraw`: `ensures balance + amount = balanceOld`. `withdrawSession`: the running
invariant `balance + amounts.sum = balancePrev + tmp.sum`, which at exit
(`amounts.sum = tmp.sum`) gives `balance = balancePrev`. Cashmere discharges these
with `aesop`; the arithmetic core is squarely `crush`'s. -/

example (balance amount balanceOld : Int) (h : balance + amount = balanceOld) :
    balance = balanceOld - amount := by crush [*]

example (balance tmp_sum amounts_sum balancePrev : Int)
    (h : balance + amounts_sum = balancePrev + tmp_sum) (h2 : amounts_sum = tmp_sum) :
    balance = balancePrev := by crush [*]

-- CashmereIncorrectnessLogic: `require balance > 0`, invariant `balance < amounts.sum`,
-- proving a bug is reachable (`ensures False` under angelic choice). The arithmetic
-- contradiction (`balance ≥ s ∧ balance < s`) is what closes.
example (balance s : Int) (h1 : balance ≥ s) (h2 : balance < s) : False := by crush [*]

/-! ## Known gap: Mathlib-bound VCs (`Examples.lean`, `SpMSpV_Example.lean`)

Two VC classes in Velvet depend on Mathlib types in the *goal*, not just the
framework internals, and are out of scope for `crush`'s current theory support:

* **Multiset permutation** — insertion sort's correctness includes `arr.toMultiset =
  arrOld.toMultiset` (the sort permutes, does not lose, elements). `Multiset` is a
  quotient of `List` by permutation; it has no first-order SMT theory, and `crush`
  keeps it an opaque sort, so the permutation equality cannot be discharged. This is
  a datatype-support boundary, not a translation bug.

* **`Finset.range` + `∑`** — the sparse mat-vec example sums `∑ i ∈ Finset.range b,
  spv[i] * v[spv.ind[i]]`, with the key lemma `Finset.sum_range_succ`. Big operators
  over `Finset` are higher-order folds with no SMT counterpart; discharging them
  needs the induction/`simp` layer Loom runs *around* the solver, not the solver
  itself.

Both are recorded rather than attempted: they mark where a `loom_solver` → `crush`
swap would fall back to `grind`/`aesop`/manual proof, which is the honest boundary of
an SMT hammer. See `Doc/PLAN.md` §10.
-/
