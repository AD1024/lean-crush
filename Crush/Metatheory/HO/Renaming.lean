import Crush.Metatheory.HO.Core
import Crush.Metatheory.HO.Semantics

/-!
# Typed renaming and weakening

Renaming is the binder infrastructure needed for total eta expansion and, later,
closure equations.  Because variables are intrinsically typed, a renaming preserves
types by construction.
-/

namespace Crush.Metatheory

variable {signature : Signature} {source target : Context}
variable {ty domain : Ty}

/-- A type-preserving map between local contexts. -/
abbrev Renaming (source target : Context) :=
  {ty : Ty} → Var source ty → Var target ty

namespace Renaming

/-- Lift a renaming under a binder. -/
def lift (r : Renaming source target) :
    Renaming (domain :: source) (domain :: target)
  | _, .here => .here
  | _, .there ref => .there (r ref)

/-- Embed a context underneath one fresh head variable. -/
def weaken : Renaming source (domain :: source) :=
  fun {_} ref => .there ref

/-- Identity renaming. -/
def id : Renaming source source := fun {_} ref => ref

end Renaming

/-- Apply a typed renaming throughout a source term. -/
def Term.rename {signature : Signature} {source target : Context}
    (r : Renaming source target) :
    {ty : Ty} → Term signature source ty → Term signature target ty
  | _, .var ref => .var (r ref)
  | _, .const ref => .const ref
  | _, .boolLit value => .boolLit value
  | _, .not body => .not (body.rename r)
  | _, .and left right => .and (left.rename r) (right.rename r)
  | _, .or left right => .or (left.rename r) (right.rename r)
  | _, .imp left right => .imp (left.rename r) (right.rename r)
  | _, .iff left right => .iff (left.rename r) (right.rename r)
  | _, .eq left right => .eq (left.rename r) (right.rename r)
  | _, .lam body => .lam (body.rename r.lift)
  | _, .app fn argument => .app (fn.rename r) (argument.rename r)
  | _, .forallE body => .forallE (body.rename r.lift)
  | _, .existsE body => .existsE (body.rename r.lift)

/-- Move a term underneath one fresh binder. -/
def Term.weaken (term : Term signature source ty) :
    Term signature (domain :: source) ty :=
  term.rename Renaming.weaken

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
  funext ref
  cases ref <;> rfl

/-- Renaming commutes with denotation when the valuation is pulled back along
the same typed renaming. -/
theorem Term.denote_rename (model : Model signature)
    (r : Renaming source target) (term : Term signature source ty)
    (valuation : Valuation model.Base target) :
    (term.rename r).denote model valuation =
      term.denote model (fun {_} ref => valuation (r ref)) := by
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
    term.weaken.denote model (valuation.extend value) =
      term.denote model valuation := by
  simpa [Term.weaken, Renaming.weaken, Valuation.extend] using
    Term.denote_rename model (Renaming.weaken (source := source)
      (domain := domain)) term (valuation.extend value)

end Crush.Metatheory
