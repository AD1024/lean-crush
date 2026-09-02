import Crush.Metatheory.FO.Core

/-!
# Model semantics for the first-order target

Function-value sorts are interpreted by arbitrary carrier types.  In particular,
they are *not* interpreted as Lean functions: generated `app` and closure symbols
are uninterpreted until the defunctionalization theory constrains them.  This is
the semantics required for the later model-extension proof.
-/

namespace Crush.Metatheory.FO

/-- The carriers of an FO model.  A distinct arbitrary carrier is supplied for
every complete source arrow type. -/
structure Carriers where
  Base : BaseSort → Type
  Fn : Ty → Ty → Type
  baseNonempty : (sort : BaseSort) → Nonempty (Base sort)
  fnNonempty : (domain codomain : Ty) → Nonempty (Fn domain codomain)

namespace FOSort

/-- Interpretation of a first-order sort in a collection of model carriers. -/
@[reducible] def Denote (carriers : Carriers) : FOSort → Type
  | .bool => Prop
  | .base sort => carriers.Base sort
  | .fn domain codomain => carriers.Fn domain codomain

end FOSort

/-- Curried semantic type of a first-order symbol declaration. -/
def SymbolDenote (carriers : Carriers) : List FOSort → FOSort → Type
  | [], result => result.Denote carriers
  | argument :: arguments, result =>
      argument.Denote carriers → SymbolDenote carriers arguments result

/-- An FO model assigns arbitrary carriers and an interpretation to every symbol. -/
structure Model (signature : Signature) where
  carriers : Carriers
  symbol : {decl : SymbolDecl} → Symbol signature decl →
    SymbolDenote carriers decl.args decl.result

/-- A valuation assigns values to the typed target variables. -/
abbrev Valuation (carriers : Carriers) (context : Context) :=
  {sort : FOSort} → Var context sort → sort.Denote carriers

namespace Valuation

def extend {carriers : Carriers} {context : Context} {sort : FOSort}
    (valuation : Valuation carriers context) (value : sort.Denote carriers) :
    Valuation carriers (sort :: context)
  | _, .here => value
  | _, .there ref => valuation ref

def empty (carriers : Carriers) : Valuation carriers [] :=
  fun {_} ref => nomatch ref

end Valuation

mutual
  /-- Standard compositional semantics of target terms. -/
  def Term.denote {signature : Signature} (model : Model signature) :
      {context : Context} → {sort : FOSort} →
        Term signature context sort → Valuation model.carriers context →
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

  /-- Feed an intrinsically typed argument vector to a curried symbol
  interpretation. -/
  def Args.apply {signature : Signature} {context : Context}
      {sorts : List FOSort} {result : FOSort} :
      (arguments : Args signature context sorts) → (model : Model signature) →
      (valuation : Valuation model.carriers context) →
      SymbolDenote model.carriers sorts result → result.Denote model.carriers
    | .nil, _, _, function => function
    | .cons argument rest, model, valuation, function =>
        rest.apply model valuation (function (argument.denote model valuation))
  termination_by arguments _ _ _ => sizeOf arguments
end

/-- Satisfaction of a closed target formula. -/
def Model.Satisfies {signature : Signature} (model : Model signature)
    (formula : Sentence signature) : Prop :=
  formula.denote model (Valuation.empty model.carriers)

/-- Satisfaction of every axiom in a target theory. -/
def Model.SatisfiesTheory {signature : Signature} (model : Model signature)
    (theory : Theory signature) : Prop :=
  ∀ formula ∈ theory, model.Satisfies formula

def Satisfiable {signature : Signature} (formula : Sentence signature) : Prop :=
  ∃ model : Model signature, model.Satisfies formula

def Unsatisfiable {signature : Signature} (formula : Sentence signature) : Prop :=
  ∀ model : Model signature, ¬model.Satisfies formula

def TheorySatisfiable {signature : Signature} (theory : Theory signature) : Prop :=
  ∃ model : Model signature, model.SatisfiesTheory theory

def TheoryUnsatisfiable {signature : Signature} (theory : Theory signature) : Prop :=
  ∀ model : Model signature, ¬model.SatisfiesTheory theory

end Crush.Metatheory.FO
