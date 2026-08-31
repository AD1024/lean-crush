import Crush.Metatheory.Defunctionalization.Eta
import Crush.Metatheory.Notation

/-!
# Semantic correctness of eta-long normalization

The executable translator's `emitFunValue`/`mkLambdaFVars'` path materializes
every residual function value as an eta-expanded closure before using the
emitted n-ary application symbol.  This file proves the corresponding pure,
total `etaLong` transformation semantics-preserving.
-/

namespace Crush.Metatheory

open scoped Crush.Metatheory

variable {signature : Signature} {source target : Context}
variable {ty domain codomain : Ty}

private theorem pullback_lift_extend
    {base : BaseSort → Type} (r : Renaming source target)
    (valuation : Valuation base target) (value : domain.Denote base) :
    (fun {refTy} (ref : Var (domain :: source) refTy) =>
      valuation.extend value (r.lift ref)) =
    (fun {refTy} (ref : Var (domain :: source) refTy) =>
      Valuation.extend (fun {_} sourceRef => valuation (r sourceRef)) value ref) := by
  apply @funext Ty
    (fun refTy => Var (domain :: source) refTy → refTy.Denote base)
  intro refTy
  apply funext
  intro ref
  cases ref <;> rfl

/-- Renaming commutes with source denotation when the valuation is pulled back
along the same typed renaming. -/
theorem Term.denote_rename (model : Model signature)
    (r : Renaming source target) (term : Term signature source ty)
    (valuation : Valuation model.Base target) :
    ⟦term.rename r⟧[model, valuation] =
      ⟦term⟧[model, fun {_} ref => valuation (r ref)] := by
  induction term generalizing target with
  | var => rfl
  | const => rfl
  | boolLit value => cases value <;> rfl
  | not body ih => simp only [Term.rename, Term.denote, ih]
  | and left right leftIH rightIH =>
      simp only [Term.rename, Term.denote, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp only [Term.rename, Term.denote, leftIH, rightIH]
  | imp left right leftIH rightIH =>
      simp only [Term.rename, Term.denote, leftIH, rightIH]
  | iff left right leftIH rightIH =>
      simp only [Term.rename, Term.denote, leftIH, rightIH]
  | eq left right leftIH rightIH =>
      simp only [Term.rename, Term.denote, leftIH, rightIH]
  | lam body ih =>
      simp only [Term.rename, Term.denote]
      funext value
      rw [ih r.lift (valuation.extend value)]
      rw [pullback_lift_extend r valuation value]
  | app fn argument fnIH argumentIH =>
      simp only [Term.rename, Term.denote, fnIH, argumentIH]
  | forallE body ih =>
      simp only [Term.rename, Term.denote]
      apply propext
      apply forall_congr'
      intro value
      have denotationEq := ih r.lift (valuation.extend value)
      rw [pullback_lift_extend r valuation value] at denotationEq
      exact denotationEq.to_iff
  | existsE body ih =>
      simp only [Term.rename, Term.denote]
      apply propext
      apply exists_congr
      intro value
      have denotationEq := ih r.lift (valuation.extend value)
      rw [pullback_lift_extend r valuation value] at denotationEq
      exact denotationEq.to_iff

@[simp] theorem Term.denote_weaken (model : Model signature)
    (term : Term signature source ty)
    (valuation : Valuation model.Base source)
    (value : domain.Denote model.Base) :
    ⟦term.weaken (domain := domain)⟧[model, valuation.extend value] =
      ⟦term⟧[model, valuation] := by
  simpa [Term.weaken, Renaming.weaken, Valuation.extend] using
    Term.denote_rename model (Renaming.weaken (source := source)
      (domain := domain)) term (valuation.extend value)

namespace Defunctionalization

/-- Outer eta expansion is semantically the identity at every source type. -/
theorem etaAt_denote (model : Model signature) :
    (ty : Ty) → (term : Term signature source ty) →
    (valuation : Valuation model.Base source) →
    ⟦etaAt ty term⟧[model, valuation] = ⟦term⟧[model, valuation] := by
  intro resultTy
  induction resultTy generalizing source with
  | bool => intros; rfl
  | base sort => intros; rfl
  | arrow domain codomain domainIH codomainIH =>
      intro term valuation
      cases term with
      | var ref =>
          simp only [etaAt, Term.denote]
          funext argument
          rw [codomainIH]
          simp only [Term.denote]
          rw [Term.denote_weaken]
          rfl
      | const constant =>
          simp only [etaAt, Term.denote]
          funext argument
          rw [codomainIH]
          simp only [Term.denote]
          rw [Term.denote_weaken]
          rfl
      | lam body => rfl
      | app fn argument =>
          simp only [etaAt, Term.denote]
          funext value
          rw [codomainIH]
          simp only [Term.denote]
          rw [Term.denote_weaken]
          rfl

/-- Full recursive eta-long normalization preserves source denotation. -/
theorem etaLong_denote (model : Model signature) :
    {context : Context} → {ty : Ty} →
    (term : Term signature context ty) →
    (valuation : Valuation model.Base context) →
    ⟦etaLong term⟧[model, valuation] = ⟦term⟧[model, valuation] := by
  intro context resultTy term
  induction term with
  | var ref =>
      intro valuation
      exact etaAt_denote model _ _ valuation
  | const constant =>
      intro valuation
      exact etaAt_denote model _ _ valuation
  | boolLit value => intros; rfl
  | not body ih =>
      intro valuation
      simp only [etaLong, Term.denote, ih]
  | and left right leftIH rightIH =>
      intro valuation
      simp only [etaLong, Term.denote, leftIH, rightIH]
  | or left right leftIH rightIH =>
      intro valuation
      simp only [etaLong, Term.denote, leftIH, rightIH]
  | imp left right leftIH rightIH =>
      intro valuation
      simp only [etaLong, Term.denote, leftIH, rightIH]
  | iff left right leftIH rightIH =>
      intro valuation
      simp only [etaLong, Term.denote, leftIH, rightIH]
  | eq left right leftIH rightIH =>
      intro valuation
      simp only [etaLong, Term.denote, leftIH, rightIH]
  | lam body ih =>
      intro valuation
      simp only [etaLong, Term.denote]
      funext value
      exact ih (valuation.extend value)
  | app fn argument fnIH argumentIH =>
      intro valuation
      rw [etaLong]
      rw [etaAt_denote]
      simp only [Term.denote, fnIH, argumentIH]
  | forallE body ih =>
      intro valuation
      simp only [etaLong, Term.denote]
      apply propext
      apply forall_congr'
      intro value
      exact (ih (valuation.extend value)).to_iff
  | existsE body ih =>
      intro valuation
      simp only [etaLong, Term.denote]
      apply propext
      apply exists_congr
      intro value
      exact (ih (valuation.extend value)).to_iff

/-- In particular, η-expanding a partial application into the closure form used
by the Crush translator preserves the residual function value exactly. -/
theorem partialApplication_eta_correct (model : Model signature)
    (fn : Term signature source (.arrow domain codomain))
    (argument : Term signature source domain)
    (valuation : Valuation model.Base source) :
    ⟦etaLong (.app fn argument)⟧[model, valuation] =
      ⟦Term.app fn argument⟧[model, valuation] :=
  etaLong_denote model (.app fn argument) valuation

end Defunctionalization
end Crush.Metatheory
