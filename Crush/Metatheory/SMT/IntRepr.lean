import Crush.Metatheory.SMT.Int
import Crush.Metatheory.SMT.ModelExt

/-!
# Integer representation in an encoded FO model

`Int.Carrier` identifies one encoded FO carrier with the standard integers.
From that isomorphism this module constructs numeral values, the graph of
integer `>=`, and a model of the semantic theory in `SMT.Int`.
-/

namespace Crush.Metatheory.SMT.Int

open Defunctionalization.Flattened
open Crush.SMT
open Crush.SMT.Theory

variable {symbols : FO.SymbolFamily}

/-- An encoded FO carrier representing the SMT integer sort. The two maps and
inverse laws state that the carrier is isomorphic to Lean `Int`; this is the
model-construction evidence needed by the standard integer theory. -/
structure Carrier (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) where
  sort : FO.FOSort
  sort_eq : encoding.sort sort = intSort
  toInt : sort.Denote target.carriers → Int
  «from» : Int → sort.Denote target.carriers
  to_from : ∀ value, toInt («from» value) = value
  from_to : ∀ value, «from» (toInt value) = value

namespace Carrier

variable {encoding : Encoding symbols} {target : FO.FamilyModel symbols}

/-- Read any value as an integer. Typed integer values use the carrier
isomorphism; other values receive an arbitrary total interpretation because
SMT function graphs are total outside well-sorted applications as well. -/
noncomputable def value (repr : Carrier encoding target) : Value target → Int
  | .typed sort input => by
      classical
      exact if equal : sort = repr.sort then
        repr.toInt (equal ▸ input)
      else 0
  | .raw _ => 0

@[simp] theorem value_typed (repr : Carrier encoding target)
    (input : repr.sort.Denote target.carriers) :
    repr.value (.typed repr.sort input) = repr.toInt input := by
  simp [value]

/-- Standard interpretation of integer numerals, retaining the ordinary
interpretation for every other literal class. -/
noncomputable def literal (repr : Carrier encoding target) :
    Literal → Value target
  | .num numeral => .typed repr.sort (repr.«from» (Int.ofNat numeral))
  | other => literalValue encoding target other

theorem literal_typed (repr : Carrier encoding target) (literal : Literal) :
    Value.InSort encoding literal.sort (repr.literal literal) := by
  cases literal with
  | num numeral => simpa [Carrier.literal, Value.InSort, Literal.sort] using
      repr.sort_eq
  | bool value | str value | bitvec width value =>
      exact literalValue_typed encoding target _

/-- Total standard graph for SMT integer `>=`. -/
def applies (repr : Carrier encoding target) (identifier : Ident)
    (values : List (Value target)) (output : Value target) : Prop :=
  ∃ left right, identifier = .symb ">=" ∧ values = [left, right] ∧
    output = .typed .bool (repr.value right ≤ repr.value left)

/-- SMT model extension containing interpreted numerals and `>=`. -/
noncomputable def extra (repr : Carrier encoding target) :
    SourceExt encoding target where
  apply := repr.applies
  source_fresh := by
    intro decl symbol values output applied
    rcases applied with ⟨left, right, identEq, valuesEq, outputEq⟩
    exact (encoding.ident_fresh symbol).ne
      (by simp [default_known_ident, knownContainsIdent]) identEq
  literal := repr.literal
  literal_typed := repr.literal_typed

/-- The ordinary encoded graph and integer graph are jointly single-valued. -/
theorem applyUnique (repr : Carrier encoding target) :
    ApplyUnique (modelWith encoding target repr.extra) := by
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
    exact False.elim (repr.extra.source_fresh symbol values right rightInt)
  · rcases rightOrdinary with ⟨decl, symbol, identEq, outputEq⟩
    rw [identEq] at leftInt
    exact False.elim (repr.extra.source_fresh symbol values left leftInt)
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

private theorem propValue_true (target : FO.FamilyModel symbols)
    {proposition : Prop} (valid : proposition) :
    Value.typed .bool proposition = boolValue target true := by
  have equal : proposition = True :=
    propext ⟨fun _ => trivial, fun _ => valid⟩
  subst proposition
  rfl

private theorem propValue_false (target : FO.FamilyModel symbols)
    {proposition : Prop} (invalid : ¬proposition) :
    Value.typed .bool proposition = boolValue target false := by
  have equal : proposition = False := propext ⟨invalid, False.elim⟩
  subst proposition
  rfl

/-- Integer-theory interpretation induced by a represented carrier. -/
noncomputable def interp (repr : Carrier encoding target) :
    Interp (Model.reduct (modelWith encoding target repr.extra) intSig) where
  int := fun value => .typed repr.sort (repr.«from» value)
  intTyped := by
    intro value
    change Value.InSort encoding intSort
      (.typed repr.sort (repr.«from» value))
    simpa only [modelWith_inSort, Value.InSort] using repr.sort_eq
  intInjective := by
    intro left right equal
    have valuesEqual : repr.«from» left = repr.«from» right :=
      eq_of_heq (Value.typed.inj equal).2
    have mapped := congrArg repr.toInt valuesEqual
    simpa only [repr.to_from] using mapped
  intExhaustive := by
    intro value typed
    change Value target at value
    change Value.InSort encoding intSort value at typed
    change ∃ integer, value = .typed repr.sort (repr.«from» integer)
    cases value with
    | typed sort input =>
        simp only [Value.InSort] at typed
        have sortEq : sort = repr.sort := by
          apply encoding.sort_injective
          exact typed.trans repr.sort_eq.symm
        subst sort
        refine ⟨repr.toInt input, ?_⟩
        exact congrArg (Value.typed repr.sort) (repr.from_to input).symm
    | raw sort =>
        simp only [Value.InSort] at typed
        exact False.elim
          (typed.2 repr.sort (repr.sort_eq.trans typed.1.symm))
  numeral := by intro value; rfl
  ge := by
    intro left right output
    constructor
    · intro applied
      rcases applied with ordinary | integer
      · rcases ordinary with ⟨decl, symbol, identifierEq, outputEq⟩
        exact False.elim
          ((encoding.ident_fresh symbol).ne
            (by simp [default_known_ident, knownContainsIdent])
            identifierEq.symm)
      · rcases integer with
          ⟨leftValue, rightValue, identifierEq, valuesEq, outputEq⟩
        cases valuesEq
        simp only [value_typed, repr.to_from] at outputEq
        by_cases valid : right ≤ left
        · exact Or.inl ⟨valid,
            outputEq.trans (propValue_true target valid)⟩
        · exact Or.inr ⟨valid,
            outputEq.trans (propValue_false target valid)⟩
    · intro standardOutput
      apply Or.inr
      refine ⟨.typed repr.sort (repr.«from» left),
        .typed repr.sort (repr.«from» right), rfl, rfl, ?_⟩
      simp only [value_typed, repr.to_from]
      rcases standardOutput with ⟨valid, outputEq⟩ | ⟨invalid, outputEq⟩
      · exact outputEq.trans (propValue_true target valid).symm
      · exact outputEq.trans (propValue_false target invalid).symm

/-- The induced full model satisfies the theory-independent logical laws. -/
theorem wf (repr : Carrier encoding target) :
    (modelWith encoding target repr.extra).WF where
  bool_exhaustive := modelWith_bool_exhaustive encoding target repr.extra
  apply_unique := repr.applyUnique

/-- The induced model satisfies the registered integer theory. -/
theorem models (repr : Carrier encoding target) :
    Models (Model.reduct (modelWith encoding target repr.extra) intSig) :=
  Int.models _ repr.wf repr.interp

end Carrier

end Crush.Metatheory.SMT.Int
