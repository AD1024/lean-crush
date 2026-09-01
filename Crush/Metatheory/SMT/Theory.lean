import Crush.Metatheory.SMT.Struct

/-!
# Semantic SMT theories and theory combination

An SMT theory is a signature together with an isomorphism-closed class of
well-formed structures. Compatible theories combine by requiring one common
structure whose reduct is a model of each component theory.
-/

namespace Crush.SMT

namespace Model

/-- Laws required of every full model used at the SMT semantic boundary.
Logical evaluation already fixes Boolean operations and equality; these fields
make the Boolean carrier exactly two-valued and every application graph
single-valued. -/
structure WF (model : Model) : Prop where
  bool_exhaustive : ∀ value, model.inSort boolSort value →
    ∃ boolean, value = model.bool boolean
  apply_unique : ApplyUnique model

/-- Existing globally standard models satisfy the theory-independent laws. -/
theorem Standard.wf {model : Model} (standard : model.Standard) : model.WF :=
  ⟨standard.bool_exhaustive, standard.apply_unique⟩

/-- Existing command-indexed standard models satisfy the theory-independent
laws. -/
theorem StandardFor.wf {model : Model} {commands : Array Command}
    (standard : model.StandardFor commands) : model.WF :=
  ⟨standard.bool_exhaustive, standard.apply_unique⟩

/-- The full-model well-formedness class is inhabited. -/
theorem wf_exists : ∃ model : Model, model.WF := by
  rcases standardModel_exists with ⟨model, standard⟩
  exact ⟨model, standard.wf⟩

end Model

end Crush.SMT

namespace Crush.Metatheory.SMT

open Crush.SMT
open Crush.SMT.Theory

/-- An SMT theory over `sig`: an isomorphism-closed class of well-formed
structures for that signature. -/
structure Theory (sig : Sig) where
  Models : Struct sig → Prop
  models_wf : ∀ {model}, Models model → model.WF
  iso_closed : ∀ {left right}, Struct.Iso left right →
    Models left → Models right

namespace Theory

/-- The empty theory contains every well-formed structure of the empty
signature. -/
def empty : Theory Sig.empty where
  Models := Struct.WF
  models_wf := id
  iso_closed := Struct.WF.ofIso

/-- The empty theory has a concrete model. -/
theorem empty_inhabited : ∃ model, empty.Models model :=
  ⟨Struct.unit, Struct.WF.unit⟩

/-- Reduct-based combination of two compatible semantic theories. The common
structure must be well formed because mixed sorts can use constructors from
both signatures, while each component law sees only its own reduct. -/
def sum {leftSig rightSig : Sig} (left : Theory leftSig)
    (right : Theory rightSig) (compatible : leftSig.Compatible rightSig) :
    Theory (leftSig.sum rightSig compatible) :=
  let leftSub := Sig.sub_sum_left leftSig rightSig compatible
  let rightSub := Sig.sub_sum_right leftSig rightSig compatible
  {
    Models := fun model => model.WF ∧
      left.Models (Struct.reduct leftSub model) ∧
      right.Models (Struct.reduct rightSub model)
    models_wf := And.left
    iso_closed := by
      intro first second iso models
      exact ⟨Struct.WF.ofIso iso models.1,
        left.iso_closed (Struct.Iso.reduct leftSub iso) models.2.1,
        right.iso_closed (Struct.Iso.reduct rightSub iso) models.2.2⟩ }

/-- A model of a semantic sum is exactly a well-formed common structure whose
two reducts model the component theories. -/
theorem sum_models_iff {leftSig rightSig : Sig}
    (left : Theory leftSig) (right : Theory rightSig)
    (compatible : leftSig.Compatible rightSig)
    (model : Struct (leftSig.sum rightSig compatible)) :
    (sum left right compatible).Models model ↔
      model.WF ∧
      left.Models
        (Struct.reduct (Sig.sub_sum_left leftSig rightSig compatible) model) ∧
      right.Models
        (Struct.reduct (Sig.sub_sum_right leftSig rightSig compatible) model) :=
  Iff.rfl

end Theory

end Crush.Metatheory.SMT
