import Crush.Metatheory.SMT.GuardedSoundness
import Crush.Metatheory.SMT.IntRepr

/-!
# Interpreted integer guards

This module gives the emitted term `(>= t 0)` its standard integer
denotation inside the shared raw SMT model. It is independent of datatypes:
datatype well-formedness bodies merely reuse its `TermSemantics` when a field
is represented by the nonnegative part of an integer carrier.
-/

namespace Crush.Metatheory.SMT

open Defunctionalization.Flattened
open Crush.SMT
open Crush.SMT.Theory
open scoped Crush.SMT

variable {symbols : FO.SymbolFamily}

namespace Int.Carrier

variable {encoding : Encoding symbols} {target : FO.FamilyModel symbols}

/-- The emitted nonnegativity syntax at the represented integer sort. -/
def guarding (repr : Int.Carrier encoding target) : GuardedEncoding symbols where
  encoding
  guard := fun sort term =>
    if sort = repr.sort then some (smt| (>= $term 0)) else none

/-- Semantic subset selected by `guarding`: nonnegative integers at the
distinguished sort and the complete carrier everywhere else. -/
def guard (repr : Int.Carrier encoding target) :
    ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop :=
  fun sort input =>
    if equal : sort = repr.sort then
      0 ≤ repr.toInt (equal ▸ input)
    else True

@[simp] theorem guard_at (repr : Int.Carrier encoding target)
    (input : repr.sort.Denote target.carriers) :
    repr.guard repr.sort input ↔ 0 ≤ repr.toInt input := by
  simp [guard]

/-- `(>= t 0)` denotes exactly nonnegativity in the shared raw model. -/
theorem termSemantics (repr : Int.Carrier encoding target) :
    repr.guarding.TermSemantics target repr.extra repr.guard where
  omitted := by
    intro sort raw guardEq input
    simp only [guarding] at guardEq
    split at guardEq
    · contradiction
    · simp [guard, *]
  encoded := by
    intro sort raw input environment condition rawEval guardEq
    simp only [guarding] at guardEq
    split at guardEq
    next equal =>
      subst sort
      simp only [Option.some.injEq] at guardEq
      subst condition
      have zeroEval : Eval
          (modelWith encoding target repr.extra) environment (smt| 0)
          (.typed repr.sort (repr.«from» 0)) := by
        exact Eval.literal (.num 0) (by intro value impossible; cases impossible)
      apply Eval.symbol (by decide)
      · exact .cons rawEval (.cons zeroEval .nil)
      · apply Or.inr
        refine ⟨.typed repr.sort input,
          .typed repr.sort (repr.«from» 0), rfl, rfl, ?_⟩
        simp [guard, value, repr.to_from]
    next unequal => simp at guardEq

/-- A family of allocated unary predicates is disjoint from interpreted `>=`
when none of its identifiers is `>=`. -/
theorem guardsFresh (repr : Int.Carrier encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    guards.Fresh repr.extra := by
  intro sort identifier identEq values output applied
  rcases applied with ⟨left, right, appliedIdent, valuesEq, outputEq⟩
  exact separate sort identifier identEq appliedIdent

/-- Emitted guard syntax with integer nonnegativity taking precedence over
fresh datatype predicates. -/
def withGuards (repr : Int.Carrier encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard) : GuardedEncoding symbols where
  encoding
  guard := fun sort term =>
    if sort = repr.sort then some (smt| (>= $term 0))
    else guards.guarding.guard sort term

/-- Semantics selected by `withGuards`. -/
def guardWith (repr : Int.Carrier encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard) :
    ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop :=
  fun sort input =>
    if equal : sort = repr.sort then
      0 ≤ repr.toInt (equal ▸ input)
    else guard sort input

/-- Integer and unary datatype guards share one exact raw model and one
component-independent `TermSemantics` contract. -/
theorem termSemantics_withGuards (repr : Int.Carrier encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (omitted : ∀ sort, sort ≠ repr.sort → guards.ident sort = none →
      ∀ value, guard sort value) :
    (repr.withGuards guards).TermSemantics target
      (guards.over repr.extra) (repr.guardWith guards) where
  omitted := by
    intro sort raw guardEq input
    simp only [withGuards] at guardEq
    split at guardEq
    · contradiction
    next unequal =>
      unfold UnaryGuards.guarding at guardEq
      cases identEq : guards.ident sort with
      | none =>
          simpa [guardWith, unequal] using omitted sort unequal identEq input
      | some identifier => simp [identEq] at guardEq
  encoded := by
    intro sort raw input environment condition rawEval guardEq
    simp only [withGuards] at guardEq
    split at guardEq
    next equal =>
      subst sort
      simp only [Option.some.injEq] at guardEq
      subst condition
      have zeroEval : Eval
          (modelWith encoding target (guards.over repr.extra))
          environment (smt| 0) (.typed repr.sort (repr.«from» 0)) := by
        exact Eval.literal (.num 0)
          (by intro value impossible; cases impossible)
      apply Eval.symbol (by decide)
      · exact .cons rawEval (.cons zeroEval .nil)
      · apply Or.inr
        apply Or.inl
        refine ⟨.typed repr.sort input,
          .typed repr.sort (repr.«from» 0), rfl, rfl, ?_⟩
        simp [guardWith, value, repr.to_from]
    next unequal =>
      have evaluated := guards.encoded_over repr.extra rawEval guardEq
      simpa [withGuards, UnaryGuards.guarding, guardWith, unequal] using evaluated

/-- Functionality of the complete interpreted-integer/unary-predicate graph. -/
theorem applyUnique_withGuards (repr : Int.Carrier encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    ApplyUnique
      (modelWith encoding target (guards.over repr.extra)) :=
  guards.applyUnique_over repr.extra repr.applyUnique
    (repr.guardsFresh guards separate)

/-- Installing fresh unary datatype guards leaves every observation in the
integer signature unchanged. -/
def reductIsoWithGuards (repr : Int.Carrier encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    Struct.Iso
      (Model.reduct (modelWith encoding target repr.extra) intSig)
      (Model.reduct
        (modelWith encoding target (guards.over repr.extra)) intSig) where
  to := id
  inv := id
  to_inv := by simp
  inv_to := by simp
  inSort := by intro sort present value; rfl
  bool := by intro value; rfl
  literal := by intro literal present; cases literal <;> rfl
  apply := by
    intro identifier present values output
    change intContainsIdent identifier = true at present
    have identifierEq : identifier = .symb ">=" := of_decide_eq_true present
    change (Applies encoding target identifier values output ∨
        repr.extra.apply identifier values output) ↔
      Applies encoding target identifier (values.map id) (id output) ∨
        (repr.extra.apply identifier (values.map id) (id output) ∨
          guards.extra.apply identifier (values.map id) (id output))
    simp only [List.map_id_fun, id_eq]
    constructor
    · rintro (ordinary | integer)
      · exact Or.inl ordinary
      · exact Or.inr (Or.inl integer)
    · rintro (ordinary | integer | unary)
      · exact Or.inl ordinary
      · exact Or.inr integer
      · rcases unary with ⟨sort, value, guardIdent, valuesEq, outputEq⟩
        exact False.elim
          (separate sort identifier guardIdent identifierEq)

/-- Adding fresh unary datatype guards preserves the theory-independent logical
laws. -/
theorem wfWithGuards (repr : Int.Carrier encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    (modelWith encoding target (guards.over repr.extra)).WF where
  bool_exhaustive :=
    modelWith_bool_exhaustive encoding target (guards.over repr.extra)
  apply_unique := repr.applyUnique_withGuards guards separate

/-- Adding fresh unary datatype guards preserves the registered integer
theory. -/
theorem modelsWithGuards (repr : Int.Carrier encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    Int.Models (Model.reduct
      (modelWith encoding target (guards.over repr.extra)) intSig) :=
  Int.models_ofIso (repr.reductIsoWithGuards guards separate) repr.models

end Int.Carrier

end Crush.Metatheory.SMT
