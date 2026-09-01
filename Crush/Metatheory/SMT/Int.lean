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

/-- Evidence needed to give an induced raw model the standard SMT integer
interpretation. It selects one FO sort whose concrete encoding is SMT `Int`,
proves that the corresponding target carrier is isomorphic to Lean `Int`, and
keeps the source-symbol namespace disjoint from the interpreted `>=` operator.

This is an explicit model-construction premise. It is not implied by
`Encoding`: an encoding fixes sort syntax, whereas the carrier and its
isomorphism depend on the particular target model. -/
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

private theorem propositionValue_eq_true (target : FO.FamilyModel symbols)
    {proposition : Prop} (valid : proposition) :
    Value.typed .bool proposition = boolValue target true := by
  have equal : proposition = True :=
    propext ⟨fun _ => trivial, fun _ => valid⟩
  subst proposition
  rfl

private theorem propositionValue_eq_false (target : FO.FamilyModel symbols)
    {proposition : Prop} (invalid : ¬proposition) :
    Value.typed .bool proposition = boolValue target false := by
  have equal : proposition = False := propext ⟨invalid, False.elim⟩
  subst proposition
  rfl

/-- The standard integer structure induced by an `IntView`. -/
noncomputable def integerInterpretation (view : IntView encoding target) :
    Crush.SMT.Model.IntegerInterpretation
      (modelWith encoding target view.extra) where
  int := fun value => .typed view.sort (view.«from» value)
  int_typed := by
    intro value
    simpa only [modelWith_inSort, Value.InSort] using view.sort_eq
  int_injective := by
    intro left right equal
    have valuesEqual : view.«from» left = view.«from» right :=
      eq_of_heq (Value.typed.inj equal).2
    have := congrArg view.toInt valuesEqual
    simpa only [view.to_from] using this
  int_exhaustive := by
    intro value typed
    simp only [modelWith_inSort] at typed
    cases value with
    | typed sort input =>
        simp only [Value.InSort] at typed
        have sortEq : sort = view.sort := by
          apply encoding.sort_injective
          exact typed.trans view.sort_eq.symm
        subst sort
        refine ⟨view.toInt input, ?_⟩
        exact congrArg (Value.typed view.sort) (view.from_to input).symm
    | raw sort =>
        simp only [Value.InSort] at typed
        exact False.elim (typed.2 view.sort (view.sort_eq.trans typed.1.symm))
  numeral := by
    intro value
    rfl
  ge := by
    intro left right output
    constructor
    · intro applied
      rcases applied with ordinary | integer
      · rcases ordinary with ⟨decl, symbol, identifierEq, outputEq⟩
        exact False.elim (view.ge_fresh symbol identifierEq.symm)
      · rcases integer with
          ⟨leftValue, rightValue, identifierEq, valuesEq, outputEq⟩
        cases valuesEq
        simp only [value_typed, view.to_from] at outputEq
        by_cases valid : right ≤ left
        · exact Or.inl ⟨valid,
            outputEq.trans (propositionValue_eq_true target valid)⟩
        · exact Or.inr ⟨valid,
            outputEq.trans (propositionValue_eq_false target valid)⟩
    · intro standardOutput
      apply Or.inr
      refine ⟨.typed view.sort (view.«from» left),
        .typed view.sort (view.«from» right), rfl, rfl, ?_⟩
      simp only [value_typed, view.to_from]
      rcases standardOutput with ⟨valid, outputEq⟩ | ⟨invalid, outputEq⟩
      · exact outputEq.trans (propositionValue_eq_true target valid).symm
      · exact outputEq.trans (propositionValue_eq_false target invalid).symm

/-- `IntView` upgrades the induced relational model to the standard Boolean
and integer model required at the external SMT boundary. -/
theorem standard (view : IntView encoding target) :
    Crush.SMT.Model.Standard (modelWith encoding target view.extra) where
  bool_exhaustive := modelWith_bool_exhaustive encoding target view.extra
  integer := ⟨view.integerInterpretation⟩
  apply_unique := view.applyUnique

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

/-- The integer structure remains standard after installing fresh unary
datatype guards. -/
noncomputable def integerInterpretation_withGuards (view : IntView encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    Crush.SMT.Model.IntegerInterpretation
      (modelWith encoding target (guards.over view.extra)) where
  int := fun value => .typed view.sort (view.«from» value)
  int_typed := by
    intro value
    simpa only [modelWith_inSort, Value.InSort] using view.sort_eq
  int_injective := by
    intro left right equal
    have valuesEqual : view.«from» left = view.«from» right :=
      eq_of_heq (Value.typed.inj equal).2
    have := congrArg view.toInt valuesEqual
    simpa only [view.to_from] using this
  int_exhaustive := by
    intro value typed
    simp only [modelWith_inSort] at typed
    cases value with
    | typed sort input =>
        simp only [Value.InSort] at typed
        have sortEq : sort = view.sort := by
          apply encoding.sort_injective
          exact typed.trans view.sort_eq.symm
        subst sort
        refine ⟨view.toInt input, ?_⟩
        exact congrArg (Value.typed view.sort) (view.from_to input).symm
    | raw sort =>
        simp only [Value.InSort] at typed
        exact False.elim (typed.2 view.sort (view.sort_eq.trans typed.1.symm))
  numeral := by
    intro value
    rfl
  ge := by
    intro left right output
    constructor
    · intro applied
      rcases applied with ordinary | native
      · rcases ordinary with ⟨decl, symbol, identifierEq, outputEq⟩
        exact False.elim (view.ge_fresh symbol identifierEq.symm)
      · rcases native with integer | unary
        · rcases integer with
            ⟨leftValue, rightValue, identifierEq, valuesEq, outputEq⟩
          cases valuesEq
          simp only [value_typed, view.to_from] at outputEq
          by_cases valid : right ≤ left
          · exact Or.inl ⟨valid,
              outputEq.trans (propositionValue_eq_true target valid)⟩
          · exact Or.inr ⟨valid,
              outputEq.trans (propositionValue_eq_false target valid)⟩
        · rcases unary with ⟨sort, value, identEq, valuesEq, outputEq⟩
          exact False.elim (separate sort _ identEq rfl)
    · intro standardOutput
      apply Or.inr
      apply Or.inl
      refine ⟨.typed view.sort (view.«from» left),
        .typed view.sort (view.«from» right), rfl, rfl, ?_⟩
      simp only [value_typed, view.to_from]
      rcases standardOutput with ⟨valid, outputEq⟩ | ⟨invalid, outputEq⟩
      · exact outputEq.trans (propositionValue_eq_true target valid).symm
      · exact outputEq.trans (propositionValue_eq_false target invalid).symm

/-- Adding fresh unary datatype guards preserves the standard integer
interpretation supplied by `IntView`. -/
theorem standard_withGuards (view : IntView encoding target)
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=") :
    Crush.SMT.Model.Standard
      (modelWith encoding target (guards.over view.extra)) where
  bool_exhaustive :=
    modelWith_bool_exhaustive encoding target (guards.over view.extra)
  integer := ⟨view.integerInterpretation_withGuards guards separate⟩
  apply_unique := view.applyUnique_withGuards guards separate

end IntView

end Crush.Metatheory.SMT
