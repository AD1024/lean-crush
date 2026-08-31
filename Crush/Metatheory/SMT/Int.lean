import Crush.Metatheory.SMT.GuardedSoundness

/-!
# Interpreted integer guards

This module gives the emitted term `(>= t 0)` its standard integer
denotation inside the shared raw SMT model. It is independent of datatypes:
datatype well-formedness bodies merely reuse its `TermSemantics` when a field
is represented by the nonnegative part of an integer carrier.
-/

namespace Crush.Metatheory.SMT

open Defunctionalization.Flattened
open scoped Crush.SMT

variable {symbols : FO.SymbolFamily}

/-- One typed source sort represented by SMT `Int`, together with its actual
integer carrier and the freshness needed to interpret SMT's `>=` symbol. -/
structure IntView (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) where
  sort : FO.FOSort
  sort_eq : encoding.sort sort = Crush.SMT.intSort
  toInt : sort.Denote target.carriers → Int
  «from» : Int → sort.Denote target.carriers
  to_from : ∀ value, toInt («from» value) = value
  from_to : ∀ value, «from» (toInt value) = value
  ge_fresh : ∀ {decl : FO.SymbolDecl} (symbol : symbols decl),
    encoding.ident symbol ≠ .symb ">="

namespace IntView

variable {encoding : Encoding symbols} {target : FO.FamilyModel symbols}

/-- Read an arbitrary raw value as an integer. Only the matching typed branch
is observable in typed guard proofs; other inputs totalize the SMT graph. -/
noncomputable def value (view : IntView encoding target) :
    Value target → Int
  | .typed sort input => by
      classical
      exact if equal : sort = view.sort then
        view.toInt (equal ▸ input)
      else 0
  | .raw _ => 0

@[simp] theorem value_typed (view : IntView encoding target)
    (input : view.sort.Denote target.carriers) :
    view.value (.typed view.sort input) = view.toInt input := by
  simp [value]

/-- Standard interpretation of integer numerals, retaining the ordinary
interpretation for every other literal class. -/
noncomputable def literal (view : IntView encoding target) :
    Crush.SMT.Literal → Value target
  | .num numeral =>
      .typed view.sort (view.«from» (Int.ofNat numeral))
  | other => literalValue encoding target other

theorem literal_typed (view : IntView encoding target)
    (literal : Crush.SMT.Literal) :
    Value.InSort encoding literal.sort (view.literal literal) := by
  cases literal with
  | num numeral => simpa [IntView.literal, Value.InSort,
      Crush.SMT.Literal.sort] using view.sort_eq
  | bool value | str value | bitvec width value =>
      exact literalValue_typed encoding target _

/-- Total standard graph for SMT integer `>=`. -/
def applies (view : IntView encoding target) (identifier : Crush.SMT.Ident)
    (values : List (Value target)) (output : Value target) : Prop :=
  ∃ left right, identifier = .symb ">=" ∧ values = [left, right] ∧
    output = .typed .bool (view.value right ≤ view.value left)

/-- Raw SMT model extension containing interpreted numerals and `>=`. -/
noncomputable def extra (view : IntView encoding target) :
    ExtraGraph encoding target where
  apply := view.applies
  source_fresh := by
    intro decl symbol values output applied
    rcases applied with ⟨left, right, identEq, valuesEq, outputEq⟩
    exact view.ge_fresh symbol identEq
  literal := view.literal
  literal_typed := view.literal_typed

/-- The emitted nonnegativity syntax at the represented integer sort. -/
def guarding (view : IntView encoding target) : GuardedEncoding symbols where
  encoding
  guard := fun sort term =>
    if sort = view.sort then some (smt| (>= $term 0)) else none

/-- Semantic subset selected by `guarding`: nonnegative integers at the
distinguished sort and the complete carrier everywhere else. -/
def guard (view : IntView encoding target) :
    ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop :=
  fun sort input =>
    if equal : sort = view.sort then
      0 ≤ view.toInt (equal ▸ input)
    else True

@[simp] theorem guard_at (view : IntView encoding target)
    (input : view.sort.Denote target.carriers) :
    view.guard view.sort input ↔ 0 ≤ view.toInt input := by
  simp [guard]

/-- `(>= t 0)` denotes exactly nonnegativity in the shared raw model. -/
theorem termSemantics (view : IntView encoding target) :
    view.guarding.TermSemantics target view.extra view.guard where
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
      have zeroEval : Crush.SMT.Eval
          (modelWith encoding target view.extra) environment (smt| 0)
          (.typed view.sort (view.«from» 0)) := by
        exact Crush.SMT.Eval.literal (.num 0) (by intro value impossible; cases impossible)
      apply Crush.SMT.Eval.symbol (by decide)
      · exact .cons rawEval (.cons zeroEval .nil)
      · apply Or.inr
        refine ⟨.typed view.sort input,
          .typed view.sort (view.«from» 0), rfl, rfl, ?_⟩
        simp [guard, value, view.to_from]
    next unequal => simp at guardEq

/-- The combined ordinary/integer graph is deterministic. -/
theorem applyUnique (view : IntView encoding target) :
    Crush.SMT.ApplyUnique (modelWith encoding target view.extra) := by
  intro identifier values left right leftApply rightApply
  rcases leftApply with leftOrdinary | leftInt <;>
    rcases rightApply with rightOrdinary | rightInt
  · rcases leftOrdinary with
      ⟨leftDecl, leftSymbol, leftIdent, leftEq⟩
    rcases rightOrdinary with
      ⟨rightDecl, rightSymbol, rightIdent, rightEq⟩
    have identEq : encoding.ident leftSymbol = encoding.ident rightSymbol :=
      leftIdent.symm.trans rightIdent
    have declEq := encoding.ident_decl_injective leftSymbol rightSymbol identEq
    subst rightDecl
    have symbolEq := encoding.ident_injective leftSymbol rightSymbol identEq
    subst rightSymbol
    exact leftEq.trans rightEq.symm
  · rcases leftOrdinary with ⟨decl, symbol, identEq, outputEq⟩
    rw [identEq] at rightInt
    exact False.elim (view.extra.source_fresh symbol values right rightInt)
  · rcases rightOrdinary with ⟨decl, symbol, identEq, outputEq⟩
    rw [identEq] at leftInt
    exact False.elim (view.extra.source_fresh symbol values left leftInt)
  · rcases leftInt with
      ⟨leftArg, leftZero, leftIdent, leftValues, leftEq⟩
    rcases rightInt with
      ⟨rightArg, rightZero, rightIdent, rightValues, rightEq⟩
    rw [leftValues] at rightValues
    injection rightValues with argEq zeroEq
    subst rightArg
    injection zeroEq with zeroEq
    subst rightZero
    exact leftEq.trans rightEq.symm

/-- A family of allocated unary predicates is disjoint from interpreted `>=`
when none of its identifiers is `>=`. -/
theorem guardsFresh (view : IntView encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    guards.Fresh view.extra := by
  intro sort identifier identEq values output applied
  rcases applied with ⟨left, right, appliedIdent, valuesEq, outputEq⟩
  exact separate sort identifier identEq appliedIdent

/-- Emitted guard syntax with integer nonnegativity taking precedence over
fresh datatype predicates. -/
def withGuards (view : IntView encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard) : GuardedEncoding symbols where
  encoding
  guard := fun sort term =>
    if sort = view.sort then some (smt| (>= $term 0))
    else guards.guarding.guard sort term

/-- Semantics selected by `withGuards`. -/
def guardWith (view : IntView encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard) :
    ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop :=
  fun sort input =>
    if equal : sort = view.sort then
      0 ≤ view.toInt (equal ▸ input)
    else guard sort input

/-- Integer and unary datatype guards share one exact raw model and one
component-independent `TermSemantics` contract. -/
theorem termSemantics_withGuards (view : IntView encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (omitted : ∀ sort, sort ≠ view.sort → guards.ident sort = none →
      ∀ value, guard sort value) :
    (view.withGuards guards).TermSemantics target
      (guards.over view.extra) (view.guardWith guards) where
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
      have zeroEval : Crush.SMT.Eval
          (modelWith encoding target (guards.over view.extra))
          environment (smt| 0) (.typed view.sort (view.«from» 0)) := by
        exact Crush.SMT.Eval.literal (.num 0)
          (by intro value impossible; cases impossible)
      apply Crush.SMT.Eval.symbol (by decide)
      · exact .cons rawEval (.cons zeroEval .nil)
      · apply Or.inr
        apply Or.inl
        refine ⟨.typed view.sort input,
          .typed view.sort (view.«from» 0), rfl, rfl, ?_⟩
        simp [guardWith, value, view.to_from]
    next unequal =>
      have evaluated := guards.encoded_over view.extra rawEval guardEq
      simpa [withGuards, UnaryGuards.guarding, guardWith, unequal] using evaluated

/-- Functionality of the complete interpreted-integer/unary-predicate graph. -/
theorem applyUnique_withGuards (view : IntView encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    Crush.SMT.ApplyUnique
      (modelWith encoding target (guards.over view.extra)) :=
  guards.applyUnique_over view.extra view.applyUnique
    (view.guardsFresh guards separate)

end IntView

end Crush.Metatheory.SMT
