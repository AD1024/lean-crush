import Crush.Metatheory.HO.Core

/-!
# Model semantics for the higher-order core

Boolean terms denote Lean propositions.  Base sorts are supplied by a model and
arrows denote genuine Lean function spaces.  Thus lambda and application receive
their ordinary semantics, while uninterpreted constants may be assigned arbitrary
values of their intrinsically recorded types.
-/

namespace Crush.Metatheory

namespace Ty

/-- Set-theoretic interpretation of a source type. -/
@[reducible] def Denote (base : BaseSort → Type) : Ty → Type
  | .bool => Prop
  | .base sort => base sort
  | .arrow domain codomain => Denote base domain → Denote base codomain

end Ty

/-- A higher-order model assigns a carrier to each opaque base sort and a value
to each declared constant. -/
structure Model (signature : Signature) where
  Base : BaseSort → Type
  baseNonempty : (sort : BaseSort) → Nonempty (Base sort)
  const : {ty : Ty} → Const signature ty → ty.Denote Base

/-- Every interpreted source type is nonempty when opaque base sorts are.  This
matches SMT-LIB's nonempty-sort convention and will supply the carriers used by
model extension. -/
theorem Ty.denoteNonempty (base : BaseSort → Type)
    (baseNonempty : (sort : BaseSort) → Nonempty (base sort)) :
    (ty : Ty) → Nonempty (ty.Denote base)
  | .bool => ⟨True⟩
  | .base sort => baseNonempty sort
  | .arrow _ codomain =>
      let ⟨value⟩ := denoteNonempty base baseNonempty codomain
      ⟨fun _ => value⟩

/-- A valuation assigns a semantic value to every typed local variable. -/
abbrev Valuation (base : BaseSort → Type) (context : Context) :=
  {ty : Ty} → Var context ty → ty.Denote base

namespace Valuation

/-- Extend a valuation under one binder. -/
def extend {base : BaseSort → Type} {context : Context} {ty : Ty}
    (valuation : Valuation base context) (value : ty.Denote base) :
    Valuation base (ty :: context)
  | _, .here => value
  | _, .there ref => valuation ref

/-- The unique valuation of the empty context. -/
def empty (base : BaseSort → Type) : Valuation base [] :=
  fun {_} ref => nomatch ref

end Valuation

/-- Standard compositional semantics of intrinsically typed source terms. -/
def Term.denote {signature : Signature} (model : Model signature) :
    {context : Context} → {ty : Ty} →
      Term signature context ty → Valuation model.Base context → ty.Denote model.Base
  | _, _, .var ref, valuation => valuation ref
  | _, _, .const ref, _ => model.const ref
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
  | _, _, .lam body, valuation => fun value =>
      body.denote model (valuation.extend value)
  | _, _, .app fn arg, valuation =>
      fn.denote model valuation (arg.denote model valuation)
  | _, _, .forallE body, valuation => ∀ value,
      body.denote model (valuation.extend value)
  | _, _, .existsE body, valuation => ∃ value,
      body.denote model (valuation.extend value)

/-- Satisfaction of a closed source formula. -/
def Model.Satisfies {signature : Signature} (model : Model signature)
    (formula : Sentence signature) : Prop :=
  formula.denote model (Valuation.empty model.Base)

/-- Satisfaction of every sentence in a source theory. -/
def Model.SatisfiesTheory {signature : Signature} (model : Model signature)
    (theory : Theory signature) : Prop :=
  ∀ formula ∈ theory, model.Satisfies formula

/-- Satisfiability allows the model's carriers and interpretations to vary. -/
def Satisfiable {signature : Signature} (formula : Sentence signature) : Prop :=
  ∃ model : Model signature, model.Satisfies formula

/-- Unsatisfiability is stated semantically, independently of a solver. -/
def Unsatisfiable {signature : Signature} (formula : Sentence signature) : Prop :=
  ∀ model : Model signature, ¬model.Satisfies formula

def TheoryUnsatisfiable {signature : Signature} (theory : Theory signature) : Prop :=
  ∀ model : Model signature, ¬model.SatisfiesTheory theory

@[simp] theorem Term.denote_trueE {signature : Signature} (model : Model signature)
    {context : Context} (valuation : Valuation model.Base context) :
    Term.denote model (Term.trueE (signature := signature)) valuation :=
  trivial

@[simp] theorem Term.denote_falseE {signature : Signature} (model : Model signature)
    {context : Context} (valuation : Valuation model.Base context) :
    ¬Term.denote model (Term.falseE (signature := signature)) valuation :=
  fun falseProof => falseProof.elim

end Crush.Metatheory
