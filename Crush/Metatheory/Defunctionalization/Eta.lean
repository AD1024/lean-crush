import Crush.Metatheory.HO.Renaming

/-!
# Total eta-long normalization

The translator defunctionalizer uses an n-ary `app` symbol for the fully flattened
shape of an arrow.  Consequently a partial application cannot be emitted as an
under-applied target symbol: it must become a closure for its residual arrow type.

`etaLong` makes that invariant explicit.  Every function-valued subterm is a
lambda, including variables, constants, and partial applications.  Existing
lambdas retain their binder and only have their bodies normalized.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature} {context : Context}
variable {ty domain codomain : Ty}

/-- Eta-expand only at the outer type.  Its input has already had all original
subterms recursively normalized. -/
def etaAt {signature : Signature} {context : Context} :
    (ty : Ty) → Term signature context ty → Term signature context ty
  | .arrow _ _, term@(.lam _) => term
  | .arrow domain codomain, term =>
      .lam (etaAt codomain (.app (term.weaken (domain := domain)) (.var .here)))
  | .bool, term => term
  | .base _, term => term

/-- Recursively normalize original subterms, then eta-expand the reconstructed
term whenever its result type is an arrow. -/
def etaLong {signature : Signature} {context : Context} :
    {ty : Ty} → Term signature context ty → Term signature context ty
  | ty, .var ref => etaAt ty (.var ref)
  | ty, .const ref => etaAt ty (.const ref)
  | _, .boolLit value => .boolLit value
  | _, .not body => .not (etaLong body)
  | _, .and left right => .and (etaLong left) (etaLong right)
  | _, .or left right => .or (etaLong left) (etaLong right)
  | _, .imp left right => .imp (etaLong left) (etaLong right)
  | _, .iff left right => .iff (etaLong left) (etaLong right)
  | _, .eq left right => .eq (etaLong left) (etaLong right)
  | _, .lam body => .lam (etaLong body)
  | ty, .app fn argument => etaAt ty (.app (etaLong fn) (etaLong argument))
  | _, .forallE body => .forallE (etaLong body)
  | _, .existsE body => .existsE (etaLong body)

/-- A small proposition exposing the syntactic invariant needed by flattened
defunctionalization. -/
inductive IsLambda : Term signature context (.arrow domain codomain) → Prop where
  | intro (body : Term signature (domain :: context) codomain) : IsLambda (.lam body)

theorem etaAt_isLambda (term : Term signature context (.arrow domain codomain)) :
    IsLambda (etaAt (.arrow domain codomain) term) := by
  cases term with
  | lam body => exact .intro body
  | var ref => exact .intro _
  | const ref => exact .intro _
  | app fn argument => exact .intro _
  | _ => contradiction

/-- Every arrow-valued result of full normalization is syntactically a lambda. -/
theorem etaLong_isLambda (term : Term signature context (.arrow domain codomain)) :
    IsLambda (etaLong term) := by
  cases term <;> simp only [etaLong]
  · exact etaAt_isLambda _
  · exact etaAt_isLambda _
  · exact .intro _
  · exact etaAt_isLambda _

/-- An existing lambda keeps its outer binder. -/
@[simp] theorem etaLong_lam
    (body : Term signature (domain :: context) codomain) :
    etaLong (.lam body) = .lam (etaLong body) := rfl

end Crush.Metatheory.Defunctionalization
