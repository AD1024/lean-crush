import Crush

/-!
Tests for lemma-instantiation monomorphization: a *polymorphic* fact is specialized
at the concrete types the query mentions, so it talks about the same SMT symbols as
the goal.

Why this is needed at all is worth stating, because it is not the obvious "the goal
is polymorphic" story. Each SMT symbol is keyed on a constant *together with its type
arguments* — it has to be, since `@f Int` and `@f Bool` have genuinely different SMT
sorts. So before this pass a polymorphic fact emitted at an abstract instantiation
produced symbols **disjoint from the goal's**, and could not discharge it *even when
the goal was fully ground*:

```smtlib
(assert (forall ((q_1 s_0)) (= (app2_6 List_2_nil q_5) q_5)))  ; the lemma, abstract
(assert (not (= (app2_19 List_20_nil y_24) y_24)))             ; the goal, at Int
```

Two unrelated symbols over two unrelated datatypes. That is why the list theorems in
`Test/TIP.lean` originally had to be stated over a hand-written monomorphic
`append : List Int → List Int → List Int`; with this pass they go through over a
polymorphic `List α`, which is what `TIP.lean` now does.

Instantiation only ever *weakens* the asserted set (`P Int` follows from `∀ α, P α`),
so the pass cannot cause a false `unsat` — the negative tests at the end pin that
false goals are still rejected.
-/

open Crush

set_option crush.timeout 10
-- Ask for reconstruction rather than the shipped `trust` default, so the `#print axioms`
-- pins below actually witness kernel-checked proofs.
set_option crush.trust "reconstruct"

/-! ## A polymorphic function, at a ground goal

The case that fails without the pass. `app` is polymorphic, the goal is about
`List Int`; the equation lemmas must be specialized to `Int` to connect. -/

namespace M

@[crush_unfold]
def app {α : Type} : List α → List α → List α
  | [], y => y
  | x :: xs, y => x :: app xs y

end M

theorem app_nil_ground (y : List Int) : M.app [] y = y := by crush

/-! ## The same function at a *polymorphic* goal

`α` is an fvar here. The datatype encoding already gives `List α` a real SMT datatype
over an opaque element sort, so once the lemma is instantiated at `α` itself the
proof goes through. -/

theorem app_nil_poly {α : Type} (y : List α) : M.app [] y = y := by crush

/-! ## A polymorphic hypothesis specialized at a ground type -/

theorem poly_hyp_at_int (h : ∀ (α : Type) (x : α), x = x) (a : Int) : a = a := by
  crush [h]

theorem poly_hyp_useful (f : ∀ (α : Type), List α → Nat)
    (h : ∀ (α : Type) (l : List α), f α l = 0) (l : List Int) : f Int l = 0 := by
  crush [h]

/-! ## Saturation: an instance introduces a type nothing else mentioned

Instantiating a lemma about `List α` at `α := Int` introduces `List Int`, which is
then a candidate for the *next* polymorphic fact. One round would not suffice. -/

theorem saturates (len : ∀ (α : Type), List α → Nat)
    (wrap : ∀ (α : Type), α → List α)
    (hwrap : ∀ (α : Type) (x : α), len α (wrap α x) = 1)
    (a : Int) : len Int (wrap Int a) = 1 := by
  crush [hwrap]

/-! ## The polymorphic TIP list theorems

The payoff: these are the theorems that forced `List Int` before. Same
hammer-in-the-loop structure, now over an arbitrary element type. -/

namespace M

@[crush_unfold]
def rev {α : Type} : List α → List α
  | [] => []
  | x :: xs => app (rev xs) [x]

end M

theorem append_nil {α : Type} (x : List α) : M.app x [] = x := by
  induction x with
  | nil => crush
  | cons a as ih => crush [ih]

theorem append_assoc {α : Type} (x y z : List α) :
    M.app (M.app x y) z = M.app x (M.app y z) := by
  induction x with
  | nil => crush
  | cons a as ih => crush [ih]

theorem rev_append {α : Type} (x y : List α) :
    M.rev (M.app x y) = M.app (M.rev y) (M.rev x) := by
  induction x with
  | nil => crush [append_nil (M.rev y)]
  | cons a as ih => crush [ih, append_assoc (M.rev y) (M.rev as) [a]]

/-- **TIP prop_10** over a polymorphic element type: `rev (rev x) = x`. -/
theorem prop_10_rev_rev {α : Type} (x : List α) : M.rev (M.rev x) = x := by
  induction x with
  | nil => crush
  | cons a as ih => crush [ih, rev_append (M.rev as) [a]]

-- Genuinely kernel-checked over a polymorphic element type. The shipped default is
-- `crush.trust "trust"`, which would close these on the solver's word, so the
-- reconstructing policy is requested for the section above (see the `set_option` at the
-- top) to make this pin meaningful.
/-- info: 'prop_10_rev_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prop_10_rev_rev

/-- `rev³ = rev`, proved **without** the involution `rev (rev x) = x` — the same
`rev_append` hint suffices, since the `cons` step is the same shape of rewrite:
`rev (app (rev as) [a])` becomes `a :: rev (rev as)`, unfolding `rev` gives
`app (rev³ as) [a]`, and the hypothesis finishes it.

The hint is *required*: `crush [ih]` alone times out, having no way to distribute `rev`
over `app`. -/
theorem rev_three {α : Type} (x : List α) : M.rev (M.rev (M.rev x)) = M.rev x := by
  induction x with
  | nil => crush
  | cons a as ih => crush [ih, rev_append (M.rev as) [a]]

/-- info: 'rev_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rev_three

/-! ## Soundness: instantiation must not prove anything false

Instantiation weakens, so these must all still be rejected. `unknown` is also a
sound rejection — it never closes a goal — so one expectation below pins that
instead of a counterexample. -/

/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_distinct (h : ∀ (α : Type) (x : α), x = x) (a b : Int) :
    a = b := by crush [h]

-- A fact about `Int` must not transfer to `Bool`.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_cross_type (f : ∀ (α : Type), α → Nat)
    (h : ∀ (x : Int), f Int x = 0) (b : Bool) : f Bool b = 0 := by crush [h]

-- An instance must not become *stronger* than the polymorphic fact it came from.
/-- error: crush: solver returned `unknown` -/
#guard_msgs(error, substring := true) in
theorem must_reject_stronger (g : ∀ (α : Type), List α → Nat)
    (h : ∀ (α : Type) (l : List α), g α l = 0) (l : List Int) : g Int l = 1 := by
  crush [h]

/-! ## `crush.mono.fuel 0` disables the pass

With the pass off, the polymorphic equation lemmas are emitted at an abstract
instantiation again and the ground goal is no longer provable — the negative test
pins that the option really gates the behavior. -/

set_option crush.mono.fuel 0 in
/-- error: crush -/
#guard_msgs(error, substring := true) in
theorem disabled_no_mono (y : List Int) : M.app [] y = y := by crush

/-! ## `crush.mono.certify` — the instance-certification guard

Each generated instance carries a proof term (`proof` applied to the chosen type
arguments) alongside its proposition, and by construction the proof has that type.
`crush.mono.certify` re-checks that with `isDefEq` at generation time and drops any
instance that fails — turning the pass's soundness from argued into checked, which
matters under `trust`/`reconstructOrTrust` where nothing else re-checks the proof
(the default `reconstruct` policy already re-checks via the kernel during replay, so
the guard is redundant there and off by default).

Since a certification failure only fires on an *internal* bug in the monomorphizer,
there is nothing to trigger it here; what these pin is that turning the guard on is
harmless — the same polymorphic goals still close, and no spurious rejection warning
appears — and that it composes with the trusting policy it is meant for. -/

section Certify
set_option crush.mono.certify true

theorem certify_app_ground (y : List Int) : M.app [] y = y := by crush

theorem certify_poly_hyp (h : ∀ (α : Type) (x : α), x = x) (a : Int) : a = a := by
  crush [h]

-- With the guard on *and* a trusting policy, the certification is the only thing
-- standing between a mis-built instance and the solver. This closes cleanly, so the
-- guard passes every real instance through.
set_option crush.trust "trust" in
theorem certify_under_trust (f : ∀ (α : Type), List α → Nat)
    (h : ∀ (α : Type) (l : List α), f α l = 0) (l : List Int) : f Int l = 0 := by
  crush [h]

end Certify
