import Crush.Metatheory.Defunctionalization.Flattened.Spine
import Crush.Metatheory.Defunctionalization.EtaCorrectness

/-!
# Total opening of flattened lambda telescopes

The Crush translator opens every binder in a curried lambda before emitting
one flattened closure equation. `LambdaBody` models that operation without
partiality: it peels existing lambdas and eta-expands any residual function value
until a Boolean or base result is reached.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

variable {signature : Signature} {context : Context}
variable {start current domain codomain : Ty}

/-- A function telescope whose terminal body has a non-function result.  The
context index grows at every arrow, retaining exact binder order. -/
inductive LambdaBody (signature : Signature) : Context → Ty → Type where
  | ground {context : Context} {result : Ty}
      (isGround : GroundResult result)
      (body : Term signature context result) :
      LambdaBody signature context result
  | arrow {context : Context} {domain codomain : Ty}
      (body : LambdaBody signature (domain :: context) codomain) :
      LambdaBody signature context (.arrow domain codomain)

namespace LambdaBody

/-- Totally expose the complete leading arrow telescope.  A non-lambda function
value is eta-expanded one binder at a time; an existing lambda contributes its
actual body. -/
def ofTerm {context : Context} : (ty : Ty) → Term signature context ty →
    LambdaBody signature context ty
  | .bool, term => .ground .bool term
  | .base sort, term => .ground (.base sort) term
  | .arrow domain codomain, term =>
      match term with
      | .lam body => .arrow (ofTerm codomain body)
      | term =>
          .arrow (ofTerm codomain
            (.app (term.weaken (domain := domain)) (.var .here)))

/-- Binder types in source application order. -/
def binders {context : Context} : {ty : Ty} →
    LambdaBody signature context ty → List Ty
  | _, .ground _ _ => []
  | _, .arrow (domain := domain) body => domain :: body.binders

/-- Reconstruct the eta-expanded lambda term represented by the telescope. -/
def toTerm {context : Context} : {ty : Ty} →
    LambdaBody signature context ty → Term signature context ty
  | _, .ground _ body => body
  | _, .arrow body => .lam body.toTerm

/-- Body of the complete eta-expanded lambda for a function value. -/
def etaBody {context : Context} {domain codomain : Ty}
    (term : Term signature context (.arrow domain codomain)) :
    Term signature (domain :: context) codomain :=
  match term with
  | .lam body => (ofTerm codomain body).toTerm
  | term =>
      (ofTerm codomain
        (.app (term.weaken (domain := domain)) (.var .here))).toTerm

@[simp] theorem toTerm_ofTerm_arrow {context : Context}
    {domain codomain : Ty}
    (term : Term signature context (.arrow domain codomain)) :
    (ofTerm (.arrow domain codomain) term).toTerm = .lam (etaBody term) := by
  cases term <;> rfl

/-- The opened binder telescope is exactly the leading flattened arrow shape. -/
@[simp] theorem binders_ofTerm (ty : Ty) (term : Term signature context ty) :
    (ofTerm ty term).binders = (FO.flattenArrow ty).1 := by
  induction ty generalizing context with
  | bool => simp [ofTerm, binders]
  | base sort => simp [ofTerm, binders]
  | arrow domain codomain domainIH codomainIH =>
      cases term with
      | lam body =>
          simp only [ofTerm, binders]
          exact congrArg (List.cons domain) (codomainIH body)
      | var ref | const ref | app fn argument =>
          simp only [ofTerm, binders]
          apply congrArg (List.cons domain)
          apply codomainIH

/-- Opening and reconstructing the complete leading lambda telescope is
semantics-preserving.  This is the eta theorem used for residual function
values in the total flattened translator. -/
theorem denote_toTerm_ofTerm (source : Model signature) :
    {context : Context} → (ty : Ty) → (term : Term signature context ty) →
    (valuation : Valuation source.Base context) →
    Term.denote source (ofTerm ty term).toTerm valuation =
      Term.denote source term valuation := by
  intro context ty
  induction ty generalizing context with
  | bool => intros; rfl
  | base sort => intros; rfl
  | arrow domain codomain domainIH codomainIH =>
      intro term valuation
      cases term with
      | lam body =>
          simp only [ofTerm, toTerm, Term.denote]
          funext argument
          exact codomainIH body (valuation.extend argument)
      | var ref | const ref | app fn argument =>
          simp only [ofTerm, toTerm, Term.denote]
          funext value
          rw [codomainIH]
          simp only [Term.denote]
          rw [Term.denote_weaken]
          rfl

/-- The closure body selected for any function term denotes its eta expansion,
which is extensionally equal to the original function value. -/
theorem denote_etaBody (source : Model signature)
    {context : Context} {domain codomain : Ty}
    (term : Term signature context (.arrow domain codomain))
    (valuation : Valuation source.Base context) :
    Term.denote source (.lam (etaBody term)) valuation =
      Term.denote source term valuation := by
  rw [← toTerm_ofTerm_arrow term]
  exact denote_toTerm_ofTerm source (.arrow domain codomain) term valuation

end LambdaBody

/-- Fully opened source body together with the weakened closure head and the
fresh target arguments accumulated beneath its binders. -/
structure OpenedBody (signature : Signature) (start : Ty) where
  context : Context
  result : Ty
  ground : GroundResult result
  body : Term signature context result
  head : TargetTerm signature context start
  arguments : TargetArguments signature context start result

namespace LambdaBody

/-- Open a lambda telescope while weakening an existing head and argument prefix
beneath each new binder. -/
def openTarget
    {context : Context} {start current : Ty}
    (lambdaBody : LambdaBody signature context current)
    (head : TargetTerm signature context start)
    (arguments : TargetArguments signature context start current) :
    OpenedBody signature start :=
  match lambdaBody with
  | .ground isGround body =>
      { context
        result := current
        ground := isGround
        body
        head
        arguments }
  | .arrow (domain := domain) body =>
      body.openTarget
        (head.weaken (domain := FO.FOSort.ofTy domain))
        (.snoc (arguments.weaken (domain := domain)) (.var .here))

end LambdaBody

namespace OpenedBody

/-- Close the defining equation for a fully opened closure body. -/
def equation {domain codomain : Ty}
    (opened : OpenedBody signature (.arrow domain codomain))
    (translatedBody : TargetTerm signature opened.context opened.result) :
    TargetSentence signature :=
  FO.FamilyFormula.closeForall
    (.eq (opened.arguments.completeApplication opened.head opened.ground)
      translatedBody)

end OpenedBody

end Crush.Metatheory.Defunctionalization.Flattened
