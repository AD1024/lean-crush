import Crush.Metatheory.Defunctionalization.ModelExtension
import Crush.Metatheory.Defunctionalization.EtaCorrectness

/-!
# Production-shaped flattened application

Production's `arrowShape?` flattens every leading nondependent arrow and
`declareArrowSort` declares one application symbol whose arguments are the
function value followed by the entire arrow telescope.  This module gives that
symbol family a total typed semantics.

The remaining executable refinement boundary is reification: Lean `Expr`
normalization and handler dispatch must be shown to select the `Ty` and symbol
key represented here.  The arity, result sort, eta policy, and symbol semantics
are no longer part of that boundary.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature}

/-- Apply a source value to all arguments in its leading arrow telescope and
coerce the final non-arrow result into the canonical target carrier.  Its type
is exactly the curried semantic type of production's flattened declaration. -/
@[reducible] def flattenedDenote (source : Model signature) :
    (ty : Ty) → ty.Denote source.Base →
      FO.SymbolDenote (canonicalCarriers source)
        ((FO.flattenArrow ty).1.map FO.FOSort.ofTy)
        (FO.FOSort.ofTy (FO.flattenArrow ty).2)
  | .bool, value => toCanonical source .bool value
  | .base sort, value => toCanonical source (.base sort) value
  | .arrow domain codomain, fn => fun argument =>
      flattenedDenote source codomain
        (fn (fromCanonical source domain argument))

@[simp] theorem flattenedDenote_bool (source : Model signature)
    (value : Prop) : flattenedDenote source .bool value = value := rfl

@[simp] theorem flattenedDenote_base (source : Model signature)
    (sort : BaseSort) (value : source.Base sort) :
    flattenedDenote source (.base sort) value = value := rfl

@[simp] theorem flattenedDenote_arrow (source : Model signature)
    (domain codomain : Ty)
    (fn : (Ty.arrow domain codomain).Denote source.Base)
    (argument : (FO.FOSort.ofTy domain).Denote (canonicalCarriers source)) :
    flattenedDenote source (.arrow domain codomain) fn argument =
      flattenedDenote source codomain
        (fn (fromCanonical source domain argument)) := rfl

/-- The three production symbol classes represented by the core model:
fully-flattened source declarations, n-ary application, and exact-capture
closure constructors. -/
inductive ProductionSymbol (signature : Signature) : FO.SymbolDecl → Type where
  | source {ty : Ty} : Const signature ty →
      ProductionSymbol signature (sourceDecl ty)
  | app (arrow : Arrow) :
      ProductionSymbol signature (FO.appDecl arrow.domain arrow.codomain)
  | closure (closure : Closure signature) :
      ProductionSymbol signature
        (FO.closureDecl closure.captureTypes closure.domain closure.codomain)

/-- Canonical semantics of the production-shaped symbol family.  In particular,
the n-ary `app` is genuine repeated source application, not an independent
uninterpreted operation in the model extension. -/
@[reducible] noncomputable def canonicalProductionModel
    (source : Model signature) : FO.FamilyModel (ProductionSymbol signature) where
  carriers := canonicalCarriers source
  symbol := fun symbol =>
    match symbol with
    | ProductionSymbol.source (ty := ty) constant =>
        flattenedDenote source ty (source.const constant)
    | ProductionSymbol.app arrow =>
        flattenedDenote source (.arrow arrow.domain arrow.codomain)
    | ProductionSymbol.closure closure => interpretClosure source closure

@[simp] theorem canonicalProductionModel_source (source : Model signature)
    {ty : Ty} (constant : Const signature ty) :
    (canonicalProductionModel source).symbol
      (ProductionSymbol.source constant) =
        flattenedDenote source ty (source.const constant) := rfl

@[simp] theorem canonicalProductionModel_app (source : Model signature)
    (arrow : Arrow) :
    (canonicalProductionModel source).symbol (ProductionSymbol.app arrow) =
      flattenedDenote source (.arrow arrow.domain arrow.codomain) := rfl

@[simp] theorem canonicalProductionModel_closure (source : Model signature)
    (closure : Closure signature) :
    (canonicalProductionModel source).symbol (ProductionSymbol.closure closure) =
      interpretClosure source closure := rfl

/-- Binary curried application is represented by one ternary production symbol,
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
the pure counterpart of production's `mkAppN`/`getAppArgs` fully-applied path. -/
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
      FO.FamilyTerm (ProductionSymbol signature) (targetContext context)
        (FO.FOSort.ofTy ty))
    (targetValuation : FO.FamilyValuation (canonicalProductionModel source)
      (targetContext context))
    (sourceValuation : Valuation source.Base context)
    (translateCorrect : ∀ {argTy : Ty}
      (term : Term signature context argTy),
      FO.FamilyTerm.denote (canonicalProductionModel source)
          (translate term) targetValuation =
        toCanonical source argTy (Term.denote source term sourceValuation)) :
    (ty : Ty) → (value : ty.Denote source.Base) →
    (arguments : SourceArgs signature context (FO.flattenArrow ty).1) →
    FO.FamilyArgs.apply (arguments.translate translate)
        (canonicalProductionModel source) targetValuation
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

/-- A production n-ary `app` term built from a function value and the complete
argument telescope of its arrow type. -/
def flattenedApplicationTerm {context : Context} (domain codomain : Ty)
    (fn : FO.FamilyTerm (ProductionSymbol signature) (targetContext context)
      (.fn domain codomain))
    (translate : {ty : Ty} → Term signature context ty →
      FO.FamilyTerm (ProductionSymbol signature) (targetContext context)
        (FO.FOSort.ofTy ty))
    (arguments : SourceArgs signature context
      (FO.flattenArrow (.arrow domain codomain)).1) :
    FO.FamilyTerm (ProductionSymbol signature) (targetContext context)
      (FO.FOSort.ofTy (FO.flattenArrow (.arrow domain codomain)).2) :=
  .symbol (ProductionSymbol.app { domain, codomain })
    (.cons fn (arguments.translate translate))

theorem flattenedApplicationTerm_correct
    (source : Model signature) {context : Context} (domain codomain : Ty)
    (sourceFn : (Ty.arrow domain codomain).Denote source.Base)
    (targetFn : FO.FamilyTerm (ProductionSymbol signature)
      (targetContext context) (FO.arrowSort domain codomain))
    (translate : {ty : Ty} → Term signature context ty →
      FO.FamilyTerm (ProductionSymbol signature) (targetContext context)
        (FO.FOSort.ofTy ty))
    (arguments : SourceArgs signature context
      (FO.flattenArrow (.arrow domain codomain)).1)
    (sourceValuation : Valuation source.Base context)
    (targetValuation : FO.FamilyValuation (canonicalProductionModel source)
      (targetContext context))
    (fnCorrect :
      FO.FamilyTerm.denote (canonicalProductionModel source) targetFn
          targetValuation =
        toCanonical source (.arrow domain codomain) sourceFn)
    (translateCorrect : ∀ {argTy : Ty}
      (term : Term signature context argTy),
      FO.FamilyTerm.denote (canonicalProductionModel source)
          (translate term) targetValuation =
        toCanonical source argTy (Term.denote source term sourceValuation)) :
    FO.FamilyTerm.denote (canonicalProductionModel source)
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
    (targetFn : FO.FamilyTerm (ProductionSymbol signature)
      (targetContext context) (FO.arrowSort domain codomain))
    (translate : {ty : Ty} → Term signature context ty →
      FO.FamilyTerm (ProductionSymbol signature) (targetContext context)
        (FO.FOSort.ofTy ty))
    (arguments : SourceArgs signature context
      (FO.flattenArrow (.arrow domain codomain)).1)
    (sourceValuation : Valuation source.Base context)
    (targetValuation : FO.FamilyValuation (canonicalProductionModel source)
      (targetContext context))
    (fnCorrect :
      FO.FamilyTerm.denote (canonicalProductionModel source) targetFn
          targetValuation =
        toCanonical source (.arrow domain codomain)
          (Term.denote source sourceFnTerm sourceValuation))
    (translateCorrect : ∀ {argTy : Ty}
      (term : Term signature context argTy),
      FO.FamilyTerm.denote (canonicalProductionModel source)
          (translate term) targetValuation =
        toCanonical source argTy (Term.denote source term sourceValuation)) :
    FO.FamilyTerm.denote (canonicalProductionModel source)
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

end Crush.Metatheory.Defunctionalization
