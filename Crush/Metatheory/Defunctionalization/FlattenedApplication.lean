import Crush.Metatheory.Defunctionalization.Flattened.Symbol
import Crush.Metatheory.Defunctionalization.EtaCorrectness

/-!
# Emitted flattened application

The Crush translator's `arrowShape?` flattens every leading nondependent arrow and
`declareArrowSort` declares one application symbol whose arguments are the
function value followed by the entire arrow telescope.  This module gives that
symbol family a total typed semantics.

This module discharges the local semantic obligation for complete application
spines.  It does not yet define the total flattened term translation, compose
the recursively generated theory, assign semantics to concrete SMT commands, or
compare the verified translation with the Crush translator's output. Those
results are separate from this
application lemma and from Lean `Expr` reification and handler dispatch.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

variable {signature : Signature}

/-- Binary curried application is represented by one ternary emitted symbol,
and its canonical interpretation is exactly two source applications. -/
theorem flattened_binary_application (source : Model signature)
    (first second result : Ty)
    (fn : (Ty.arrow first (Ty.arrow second result)).Denote source.Base)
    (firstArg : (FO.FOSort.ofTy first).Denote (canonicalCarriers source))
    (secondArg : (FO.FOSort.ofTy second).Denote (canonicalCarriers source)) :
    flattenedDenote source (.arrow first (.arrow second result)) fn
        firstArg secondArg =
      flattenedDenote source result
        (fn (fromCanonical source first firstArg)
          (fromCanonical source second secondArg)) := rfl

/-- The declaration used in the preceding theorem is definitionally the same
fully-flattened declaration produced by `Plan.appDecls`. -/
theorem flattened_binary_declaration_base (first second : Ty)
    (result : BaseSort) :
    FO.appDecl first (.arrow second (.base result)) =
      { args :=
          [.fn first (.arrow second (.base result)),
            FO.FOSort.ofTy first, FO.FOSort.ofTy second]
        result := .base result } := by
  simp [FO.appDecl, FO.arrowSort]

/-! ## Typed complete application spines -/

/-- A heterogeneous list of source terms with the indicated source types. -/
inductive SourceArgs (signature : Signature) (context : Context) :
    List Ty → Type where
  | nil : SourceArgs signature context []
  | cons {ty : Ty} {types : List Ty} :
      Term signature context ty → SourceArgs signature context types →
      SourceArgs signature context (ty :: types)

/-- Apply a semantic source value to a complete leading-arrow telescope. -/
@[reducible] def SourceArgs.applyDenote (source : Model signature)
    {context : Context} (valuation : Valuation source.Base context) :
    (ty : Ty) → ty.Denote source.Base →
      SourceArgs signature context (FO.flattenArrow ty).1 →
      (FO.flattenArrow ty).2.Denote source.Base
  | .bool, value, .nil => value
  | .base _, value, .nil => value
  | .arrow domain codomain, fn, .cons argument rest =>
      rest.applyDenote source valuation codomain
        (fn (Term.denote source argument valuation))

/-- Syntactically apply a term to its complete leading-arrow telescope.  This is
the pure counterpart of the Crush translator's `mkAppN`/`getAppArgs` fully-applied path. -/
@[reducible] def SourceArgs.applyTerm {context : Context} :
    (ty : Ty) → Term signature context ty →
      SourceArgs signature context (FO.flattenArrow ty).1 →
      Term signature context (FO.flattenArrow ty).2
  | .bool, term, .nil => term
  | .base _, term, .nil => term
  | .arrow domain codomain, fn, .cons argument rest =>
      rest.applyTerm codomain (.app fn argument)

theorem SourceArgs.denote_applyTerm (source : Model signature)
    {context : Context} (valuation : Valuation source.Base context) :
    (ty : Ty) → (term : Term signature context ty) →
    (arguments : SourceArgs signature context (FO.flattenArrow ty).1) →
    Term.denote source (arguments.applyTerm ty term) valuation =
      arguments.applyDenote source valuation ty
        (Term.denote source term valuation) := by
  intro ty
  induction ty with
  | bool =>
      intro term arguments
      cases arguments
      rfl
  | base sort =>
      intro term arguments
      cases arguments
      rfl
  | arrow domain codomain domainIH codomainIH =>
      intro fn arguments
      cases arguments with
      | cons argument rest =>
          unfold SourceArgs.applyTerm SourceArgs.applyDenote
          exact codomainIH _ rest

/-- Translate a typed source argument telescope using any type-preserving term
translation.  This isolates application-spine flattening from the surrounding
term cases. -/
def SourceArgs.translate
    {symbols : FO.SymbolFamily} {context : Context}
    (translate : {ty : Ty} → Term signature context ty →
      FO.FamilyTerm symbols (targetContext context) (FO.FOSort.ofTy ty)) :
    {types : List Ty} → SourceArgs signature context types →
      FO.FamilyArgs symbols (targetContext context)
        (types.map FO.FOSort.ofTy)
  | [], .nil => .nil
  | _ :: _, .cons argument rest =>
      .cons (translate argument) (rest.translate translate)

/-- Applying translated arguments to `flattenedDenote` agrees with complete
source application, provided the surrounding term translation is correct on
each argument.  This is the semantic core of n-ary application flattening. -/
theorem SourceArgs.translate_apply_correct
    (source : Model signature) {context : Context}
    (translate : {ty : Ty} → Term signature context ty →
      TargetTerm signature context ty)
    (targetValuation : TargetValuation source context)
    (sourceValuation : Valuation source.Base context)
    (translateCorrect : ∀ {argTy : Ty}
      (term : Term signature context argTy),
      FO.FamilyTerm.denote (canonicalModel source)
          (translate term) targetValuation =
        toCanonical source argTy (Term.denote source term sourceValuation)) :
    (ty : Ty) → (value : ty.Denote source.Base) →
    (arguments : SourceArgs signature context (FO.flattenArrow ty).1) →
    FO.FamilyArgs.apply (arguments.translate translate)
        (canonicalModel source) targetValuation
        (flattenedDenote source ty value) =
      toCanonical source (FO.flattenArrow ty).2
        (arguments.applyDenote source sourceValuation ty value) := by
  intro ty
  induction ty with
  | bool =>
      intro value arguments
      cases arguments
      simp [SourceArgs.translate, FO.FamilyArgs.apply,
        flattenedDenote, SourceArgs.applyDenote]
  | base sort =>
      intro value arguments
      cases arguments
      simp [SourceArgs.translate, FO.FamilyArgs.apply,
        flattenedDenote, SourceArgs.applyDenote]
  | arrow domain codomain domainIH codomainIH =>
      intro fn arguments
      cases arguments with
      | cons argument rest =>
          unfold SourceArgs.translate flattenedDenote SourceArgs.applyDenote
          simp only [List.map_cons]
          rw [FO.FamilyArgs.apply.eq_2]
          rw [translateCorrect argument]
          simp only [fromCanonical_toCanonical]
          exact codomainIH _ rest

/-- An emitted n-ary `app` term built from a function value and the complete
argument telescope of its arrow type. -/
def flattenedApplicationTerm {context : Context} (domain codomain : Ty)
    (fn : FO.FamilyTerm (Symbol signature) (targetContext context)
      (FO.arrowSort domain codomain))
    (translate : {ty : Ty} → Term signature context ty →
      TargetTerm signature context ty)
    (arguments : SourceArgs signature context
      (FO.flattenArrow (.arrow domain codomain)).1) :
    TargetTerm signature context (FO.flattenArrow (.arrow domain codomain)).2 :=
  .symbol (Symbol.application { domain, codomain })
    (.cons fn (arguments.translate translate))

theorem flattenedApplicationTerm_correct
    (source : Model signature) {context : Context} (domain codomain : Ty)
    (sourceFn : (Ty.arrow domain codomain).Denote source.Base)
    (targetFn : FO.FamilyTerm (Symbol signature) (targetContext context)
      (FO.arrowSort domain codomain))
    (translate : {ty : Ty} → Term signature context ty →
      TargetTerm signature context ty)
    (arguments : SourceArgs signature context
      (FO.flattenArrow (.arrow domain codomain)).1)
    (sourceValuation : Valuation source.Base context)
    (targetValuation : TargetValuation source context)
    (fnCorrect :
      FO.FamilyTerm.denote (canonicalModel source) targetFn
          targetValuation =
        toCanonical source (.arrow domain codomain) sourceFn)
    (translateCorrect : ∀ {argTy : Ty}
      (term : Term signature context argTy),
      FO.FamilyTerm.denote (canonicalModel source)
          (translate term) targetValuation =
        toCanonical source argTy (Term.denote source term sourceValuation)) :
    FO.FamilyTerm.denote (canonicalModel source)
        (flattenedApplicationTerm domain codomain targetFn translate arguments)
        targetValuation =
      toCanonical source (FO.flattenArrow (.arrow domain codomain)).2
        (arguments.applyDenote source sourceValuation
          (.arrow domain codomain) sourceFn) := by
  unfold flattenedApplicationTerm FO.FamilyTerm.denote
  unfold FO.FamilyArgs.apply
  simp only [List.map_cons]
  rw [fnCorrect]
  rw [show toCanonical source (.arrow domain codomain) sourceFn = sourceFn by rfl]
  exact arguments.translate_apply_correct source translate targetValuation
    sourceValuation translateCorrect _ sourceFn

/-- End-to-end statement for one fully-applied spine: the single n-ary target
symbol denotes the same value as the left-associated source application chain. -/
theorem flattenedApplicationTerm_preserves_application
    (source : Model signature) {context : Context} (domain codomain : Ty)
    (sourceFnTerm : Term signature context (.arrow domain codomain))
    (targetFn : FO.FamilyTerm (Symbol signature) (targetContext context)
      (FO.arrowSort domain codomain))
    (translate : {ty : Ty} → Term signature context ty →
      TargetTerm signature context ty)
    (arguments : SourceArgs signature context
      (FO.flattenArrow (.arrow domain codomain)).1)
    (sourceValuation : Valuation source.Base context)
    (targetValuation : TargetValuation source context)
    (fnCorrect :
      FO.FamilyTerm.denote (canonicalModel source) targetFn
          targetValuation =
        toCanonical source (.arrow domain codomain)
          (Term.denote source sourceFnTerm sourceValuation))
    (translateCorrect : ∀ {argTy : Ty}
      (term : Term signature context argTy),
      FO.FamilyTerm.denote (canonicalModel source)
          (translate term) targetValuation =
        toCanonical source argTy (Term.denote source term sourceValuation)) :
    FO.FamilyTerm.denote (canonicalModel source)
        (flattenedApplicationTerm domain codomain targetFn translate arguments)
        targetValuation =
      toCanonical source (FO.flattenArrow (.arrow domain codomain)).2
        (Term.denote source
          (arguments.applyTerm (.arrow domain codomain) sourceFnTerm)
          sourceValuation) := by
  rw [arguments.denote_applyTerm source sourceValuation]
  exact flattenedApplicationTerm_correct source domain codomain
    (Term.denote source sourceFnTerm sourceValuation) targetFn translate arguments
    sourceValuation targetValuation fnCorrect translateCorrect

end Crush.Metatheory.Defunctionalization.Flattened
