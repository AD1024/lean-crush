import Crush.Metatheory.FO.Family
import Crush.Metatheory.FO.Semantics

/-!
# Semantics of abstract-symbol first-order syntax
-/

namespace Crush.Metatheory.FO

variable {symbols : SymbolFamily} {context : Context}
variable {sort result domain : FOSort} {sorts : List FOSort}
variable {decl : SymbolDecl}

/-- A model of an abstract typed symbol family. -/
structure FamilyModel (symbols : SymbolFamily) where
  carriers : Carriers
  symbol : {decl : SymbolDecl} → symbols decl →
    SymbolDenote carriers decl.args decl.result

abbrev FamilyValuation {symbols : SymbolFamily} (model : FamilyModel symbols)
    (context : Context) :=
  Valuation model.carriers context

mutual
  def FamilyTerm.denote {symbols : SymbolFamily} (model : FamilyModel symbols) :
      {context : Context} → {sort : FOSort} →
        FamilyTerm symbols context sort → FamilyValuation model context →
          sort.Denote model.carriers
    | _, _, .var ref, valuation => valuation ref
    | _, _, .symbol symbol arguments, valuation =>
        arguments.apply model valuation (model.symbol symbol)
    | _, _, .boolLit true, _ => True
    | _, _, .boolLit false, _ => False
    | _, _, .not body, valuation => ¬body.denote model valuation
    | _, _, .and left right, valuation =>
        left.denote model valuation ∧ right.denote model valuation
    | _, _, .or left right, valuation =>
        left.denote model valuation ∨ right.denote model valuation
    | _, _, .imp left right, valuation =>
        left.denote model valuation → right.denote model valuation
    | _, _, .iff left right, valuation =>
        left.denote model valuation ↔ right.denote model valuation
    | _, _, .eq left right, valuation =>
        left.denote model valuation = right.denote model valuation
    | _, _, .forallE body, valuation => ∀ value,
        body.denote model (valuation.extend value)
    | _, _, .existsE body, valuation => ∃ value,
        body.denote model (valuation.extend value)
  termination_by _ _ term _ => sizeOf term

  def FamilyArgs.apply {symbols : SymbolFamily} {context : Context}
      {sorts : List FOSort} {result : FOSort} :
      (arguments : FamilyArgs symbols context sorts) →
      (model : FamilyModel symbols) → (valuation : FamilyValuation model context) →
      SymbolDenote model.carriers sorts result → result.Denote model.carriers
    | .nil, _, _, function => function
    | .cons argument rest, model, valuation, function =>
        rest.apply model valuation (function (argument.denote model valuation))
  termination_by arguments _ _ _ => sizeOf arguments
end

attribute [simp]
  FamilyTerm.denote.eq_1 FamilyTerm.denote.eq_2
  FamilyTerm.denote.eq_3 FamilyTerm.denote.eq_4
  FamilyTerm.denote.eq_5 FamilyTerm.denote.eq_6
  FamilyTerm.denote.eq_7 FamilyTerm.denote.eq_8
  FamilyTerm.denote.eq_9 FamilyTerm.denote.eq_10
  FamilyTerm.denote.eq_11 FamilyTerm.denote.eq_12
  FamilyArgs.apply.eq_1 FamilyArgs.apply.eq_2

/-
@[simp] theorem FamilyTerm.denote_var
    (model : FamilyModel symbols) (ref : Var context sort)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.var ref) valuation = valuation ref := rfl

@[simp] theorem FamilyTerm.denote_symbol
    (model : FamilyModel symbols) (symbol : symbols decl)
    (arguments : FamilyArgs symbols context decl.args)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.symbol symbol arguments) valuation =
      arguments.apply model valuation (model.symbol symbol) := rfl

@[simp] theorem FamilyArgs.apply_nil
    (model : FamilyModel symbols) (valuation : FamilyValuation model context)
    (value : result.Denote model.carriers) :
    FamilyArgs.apply (.nil : FamilyArgs symbols context []) model valuation value = value := rfl

@[simp] theorem FamilyArgs.apply_cons
    (model : FamilyModel symbols) (valuation : FamilyValuation model context)
    (argument : FamilyTerm symbols context sort)
    (rest : FamilyArgs symbols context sorts)
    (function : SymbolDenote model.carriers (sort :: sorts) result) :
    FamilyArgs.apply (.cons argument rest) model valuation function =
      rest.apply model valuation (function (argument.denote model valuation)) := rfl

@[simp] theorem FamilyTerm.denote_boolLit
    (model : FamilyModel symbols) (value : Bool)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.boolLit value) valuation = if value then True else False := by
  cases value <;> rfl

@[simp] theorem FamilyTerm.denote_not
    (model : FamilyModel symbols) (body : FamilyFormula symbols context)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.not body) valuation =
      (¬body.denote model valuation) := rfl

@[simp] theorem FamilyTerm.denote_and
    (model : FamilyModel symbols) (left right : FamilyFormula symbols context)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.and left right) valuation =
      (left.denote model valuation ∧ right.denote model valuation) := rfl

@[simp] theorem FamilyTerm.denote_or
    (model : FamilyModel symbols) (left right : FamilyFormula symbols context)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.or left right) valuation =
      (left.denote model valuation ∨ right.denote model valuation) := rfl

@[simp] theorem FamilyTerm.denote_imp
    (model : FamilyModel symbols) (left right : FamilyFormula symbols context)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.imp left right) valuation =
      (left.denote model valuation → right.denote model valuation) := rfl

@[simp] theorem FamilyTerm.denote_iff
    (model : FamilyModel symbols) (left right : FamilyFormula symbols context)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.iff left right) valuation =
      (left.denote model valuation ↔ right.denote model valuation) := rfl

@[simp] theorem FamilyTerm.denote_eq
    (model : FamilyModel symbols) (left right : FamilyTerm symbols context sort)
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.eq left right) valuation =
      (left.denote model valuation = right.denote model valuation) := rfl

@[simp] theorem FamilyTerm.denote_forallE
    (model : FamilyModel symbols)
    (body : FamilyFormula symbols (domain :: context))
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.forallE body) valuation =
      (∀ value, body.denote model (valuation.extend value)) := rfl

@[simp] theorem FamilyTerm.denote_existsE
    (model : FamilyModel symbols)
    (body : FamilyFormula symbols (domain :: context))
    (valuation : FamilyValuation model context) :
    FamilyTerm.denote model (.existsE body) valuation =
      (∃ value, body.denote model (valuation.extend value)) := rfl
-/

def FamilyModel.Satisfies {symbols : SymbolFamily} (model : FamilyModel symbols)
    (formula : FamilySentence symbols) : Prop :=
  formula.denote model (Valuation.empty model.carriers)

def FamilyModel.SatisfiesTheory {symbols : SymbolFamily} (model : FamilyModel symbols)
    (theory : FamilyTheory symbols) : Prop :=
  ∀ formula ∈ theory, model.Satisfies formula

def FamilyTheorySatisfiable {symbols : SymbolFamily}
    (theory : FamilyTheory symbols) : Prop :=
  ∃ model : FamilyModel symbols, model.SatisfiesTheory theory

def FamilyTheoryUnsatisfiable {symbols : SymbolFamily}
    (theory : FamilyTheory symbols) : Prop :=
  ∀ model : FamilyModel symbols, ¬model.SatisfiesTheory theory

/-- To prove a universally closed formula, it suffices to prove its open body
under every valuation of the original context. -/
theorem FamilyModel.satisfies_closeForall_of_forall_denote
    {symbols : SymbolFamily} (model : FamilyModel symbols) :
    {context : Context} → (formula : FamilyFormula symbols context) →
    (∀ valuation : FamilyValuation model context,
      FamilyTerm.denote model formula valuation) →
    model.Satisfies formula.closeForall := by
  intro context formula universallyTrue
  induction context with
  | nil =>
      exact universallyTrue (Valuation.empty model.carriers)
  | cons sort context inductionHypothesis =>
      apply inductionHypothesis (.forallE formula)
      intro valuation
      simp only [FamilyTerm.denote.eq_11]
      intro value
      exact universallyTrue (valuation.extend value)

end Crush.Metatheory.FO
