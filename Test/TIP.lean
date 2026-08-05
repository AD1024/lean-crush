import Crush

/-!
Cases from the TIP `prod` benchmarks (Ireland & Bundy, "Productive Use of Failure
in Inductive Proof", JAR 1996): https://github.com/tip-org/benchmarks/tree/master/benchmarks/prod

These are *inductive* theorems, and SMT solvers do **not** do induction. The realistic
way to use a hammer on them is therefore the **hammer-in-the-loop** style: do the
structural `induction` by hand in Lean, and let `crush` discharge each resulting
subgoal — the base case, and the inductive step *given the induction hypothesis*. Each
subgoal, once the recursion is unfolded one layer, is a first-order equational/
arithmetic fact `crush` can send to the solver. This file shows that pattern working on
the TIP `prod` list/Nat theorems, alongside a couple that close outright because they
reduce to linear arithmetic after translation.

The recursive functions carry **`@[crush_unfold]`**, so their equation lemmas are folded
into every `crush` query automatically (relevance-filtered to the constants the goal
touches) — no per-call `u[…]` hint needed. Compare an earlier revision of this file,
where every `crush` spelled out `u[N.add]`, `u[L.append, L.rev]`, etc.
-/

open Crush

set_option crush.timeout 5

/-! ## prop_15 (native): `x + (x + 1) = (x + x) + 1`

Faithful to TIP prop_15 (`x + S x = S (x + x)`) but over Lean `Nat`, so `+`/`S` become
SMT `+`/`+1`. This is a pure linear-arithmetic identity — no induction — so it closes. -/

theorem prop_15_native (x : Nat) : x + (x + 1) = (x + x) + 1 := by crush

/-! ## prop_01 (native): `2 * x = x + x`

TIP prop_01 is `double x = x + x`. With `double x := 2 * x` and a *constant* multiplier,
this is linear and closes. -/

theorem prop_01_native (x : Nat) : 2 * x = x + x := by crush

/-! ## A faithful Peano formalization (TIP style) -/

inductive N where
  | Z
  | S (n : N)

namespace N

@[crush_unfold]
def add : N → N → N
  | Z, y => y
  | S x, y => S (add x y)

@[crush_unfold]
def double : N → N
  | Z => Z
  | S x => S (S (double x))

end N

/-! ## prop_01 (Peano): `double x = add x x` — induction, crush per case

`crush` cannot induct, but each case of a hand-written `induction` is first-order once
the definitions are unfolded. Because `N.add`/`N.double` carry `@[crush_unfold]`, their
equation lemmas are in every query automatically — no `u[…]` hint. In the step case the
induction hypothesis `ih` is a local hypothesis `crush` picks up on its own; only
genuine *lemmas* (like `add_succ`) still need to be named. This is the intended
hammer-in-the-loop use.

We first need `add`'s successor law, itself by induction — a helper `crush` finishes
per case. -/

theorem add_succ (x y : N) : N.add x (N.S y) = N.S (N.add x y) := by
  induction x with
  | Z => crush
  | S x ih => crush [ih]

theorem prop_01_peano (x : N) : N.double x = N.add x x := by
  induction x with
  | Z => crush
  | S x ih => crush [ih, add_succ x x]

/-! ## List benchmarks: `++` and `rev` — over an *arbitrary* element type

The classic list lemmas, each by induction with `crush` finishing every case, stated
over a polymorphic `List α`.

**These used to require a ground element type.** Each SMT symbol is keyed on a
constant together with its type arguments (it must be — `@append Int` and
`@append Bool` have different SMT sorts), so a polymorphic `append`'s equation lemmas
were emitted at an *abstract* instantiation and produced symbols disjoint from the
goal's. The lemma could not discharge the goal even when the goal was ground, which is
why these were originally written against a monomorphic
`append : List Int → List Int → List Int`. Lemma-instantiation monomorphization now
specializes those equations at the element type in play, so the polymorphic statements
go through — `List α` with an fvar `α` is already a real SMT datatype over an opaque
element sort, which is all the `cons`-injectivity an inductive step needs. -/

namespace L

@[crush_unfold]
def append {α : Type} : List α → List α → List α
  | [], y => y
  | x :: xs, y => x :: append xs y

@[crush_unfold]
def rev {α : Type} : List α → List α
  | [] => []
  | x :: xs => append (rev xs) [x]

end L

theorem append_nil {α : Type} (x : List α) : L.append x [] = x := by
  induction x with
  | nil => crush
  | cons a as ih => crush [ih]

theorem append_assoc {α : Type} (x y z : List α) :
    L.append (L.append x y) z = L.append x (L.append y z) := by
  induction x with
  | nil => crush
  | cons a as ih => crush [ih]

theorem rev_append {α : Type} (x y : List α) :
    L.rev (L.append x y) = L.append (L.rev y) (L.rev x) := by
  induction x with
  | nil => crush [append_nil (L.rev y)]
  | cons a as ih =>
    crush [ih, append_assoc (L.rev y) (L.rev as) [a]]

/-- **prop_10**: `rev (rev x) = x`, the reverse-involution theorem, by induction with
`crush` per case (the step uses `rev_append`). Note there are **no** `u[…]` hints: `rev`
and `append` are `@[crush_unfold]`, so their equations arrive automatically. -/
theorem prop_10_rev_rev {α : Type} (x : List α) : L.rev (L.rev x) = x := by
  induction x with
  | nil => crush
  | cons a as ih => crush [ih, rev_append (L.rev as) [a]]

/-! ## prop_06: `length (rev (x ++ y)) = length x + length y`

This one mixes the *list* datatype with *Nat* arithmetic: `length` returns a `Nat`
(→ SMT `Int` with the `≥0` guard), so each `crush` call spans the datatype and
arithmetic theories at once. `length` distributes over `++` (lemma `length_append`,
by induction), and `rev` preserves `length` — both towers finished by `crush`. -/

namespace L

@[crush_unfold]
def length {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => length xs + 1

end L

theorem length_append {α : Type} (x y : List α) :
    L.length (L.append x y) = L.length x + L.length y := by
  induction x with
  | nil => crush
  | cons a as ih => crush [ih]

theorem length_rev {α : Type} (x : List α) : L.length (L.rev x) = L.length x := by
  induction x with
  | nil => crush
  | cons a as ih =>
    crush [ih, length_append (L.rev as) [a]]

theorem prop_06 {α : Type} (x y : List α) :
    L.length (L.rev (L.append x y)) = L.length x + L.length y := by
  -- `rev` preserves length, `length` distributes over `++`; both are lemmas above,
  -- and `crush` combines them (a pure arithmetic/UF step, no further induction).
  crush [length_rev (L.append x y), length_append x y]
