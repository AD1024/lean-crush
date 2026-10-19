import Crush

/-!
Built-in SMT sorts must not capture variables bound inside translated quantifiers
or lambdas. This includes class-indexed carriers, proposition-dependent function
spaces, and type variables distinguishable by type equality. Direct sort allocation
must enforce the same boundary, while original query-local types remain fixed sorts.
-/

open Lean Meta Crush

set_option crush.timeout 2

namespace SoundnessSortCapture

inductive IndexedInhabited (i : Inhabited Int) : Type
  | mk : i.default = 0 → IndexedInhabited i

inductive IndexedAdd (i : Add Int) : Type
  | mk : i.add 0 0 = 0 → IndexedAdd i

inductive Phantom (α : Type) : Type
  | mk

-- Class-indexed carriers.
example : True := by
  have h1 : ∀ i : Inhabited Int, (∃ x : IndexedInhabited i, x = x) ↔ i.default = 0 :=
    fun i => ⟨fun ⟨⟨h⟩, _⟩ => h, fun h => ⟨⟨h⟩, rfl⟩⟩
  have h2 : ∃ i : Inhabited Int, i.default = 0 := ⟨⟨0⟩, rfl⟩
  have h3 : ∃ i : Inhabited Int, i.default = 1 := ⟨⟨1⟩, rfl⟩
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h1 : ∀ i : Add Int, (∃ x : IndexedAdd i, x = x) ↔ i.add 0 0 = 0 :=
    fun i => ⟨fun ⟨⟨h⟩, _⟩ => h, fun h => ⟨⟨h⟩, rfl⟩⟩
  have h2 : ∃ i : Add Int, i.add 0 0 = 0 := ⟨⟨fun _ _ => 0⟩, rfl⟩
  have h3 : ∃ i : Add Int, i.add 0 0 = 1 := ⟨⟨fun _ _ => 1⟩, rfl⟩
  fail_if_success have : False := by crush
  trivial

-- Proof-domain function spaces.
example : True := by
  have h : ∀ x : Int, (∀ f g : x > 0 → Int, f = g) ↔ x ≤ 0 := fun x => by
    constructor
    · intro hfg
      refine Int.not_lt.mp fun hx => ?_
      have := congrFun (hfg (fun _ => 0) (fun _ => 1)) hx
      simp at this
    · intro hx f g
      funext h
      omega
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : ∀ p : Prop, (∀ f g : p → Int, f = g) ↔ ¬p := fun p => by
    constructor
    · intro hfg hp
      have := congrFun (hfg (fun _ => 0) (fun _ => 1)) hp
      simp at this
    · intro hnp f g
      funext hp
      exact absurd hp hnp
  fail_if_success have : False := by crush
  trivial

-- Quantified type equality distinguishes empty and inhabited carriers.
example : True := by
  have h : ∀ α : Type,
      ((α = Empty) → ¬ ∃ x : α, x = x) ∧ ((α = Unit) → ∃ x : α, x = x) := by
    intro α
    constructor
    · intro h ⟨x, _⟩
      cases h
      exact x.elim
    · intro h
      cases h
      exact ⟨(), rfl⟩
  fail_if_success have : False := by crush
  trivial

-- Exercise direct allocation independently of premise recovery and solvers.
private def expectCaptureRefused (action : TranslateM Unit) (cfg : Crush.Config := {}) : MetaM Unit := do
  let refused ← try
    discard <| TranslateM.run cfg action
    pure false
  catch ex =>
    unless (← ex.toMessageData.toString).startsWith
        "crush: cannot translate a sort depending on a bound variable:" do
      throw ex
    pure true
  unless refused do
    throwError "accepted a sort capturing a translation binder"

run_meta do
  withLocalDeclD `α (mkSort (.succ .zero)) fun α => do
    let arrow ← mkArrow α (mkConst ``Int)
    for mode in #[HOMode.defunctionalize, .native] do
      expectCaptureRefused (cfg := { hoMode := mode }) do
        TranslateM.withBoundVar α.fvarId! "α" do
          discard <| emitSort α
      expectCaptureRefused (cfg := { hoMode := mode }) do
        TranslateM.withBoundVar α.fvarId! "α" do
          discard <| emitSort arrow
    expectCaptureRefused do
      TranslateM.withBoundVar α.fvarId! "α" do
        discard <| declareArrowSort arrow
    expectCaptureRefused do
      TranslateM.withBoundVar α.fvarId! "α" do
        discard <| declareUninterpretedSort α
    expectCaptureRefused do
      TranslateM.withFunVar α.fvarId! "α" do
        discard <| declareOpaqueCarrier α
    expectCaptureRefused do
      TranslateM.withBoundVar α.fvarId! "α" do
        discard <| declareDatatype ``Phantom #[α]
    expectCaptureRefused do
      TranslateM.withBoundVar α.fvarId! "α" do
        discard <| declareFiniteArray α
    -- An arbitrary type from the original query context is still a fixed sort.
    discard <| TranslateM.run {} <| emitSort α

end SoundnessSortCapture
