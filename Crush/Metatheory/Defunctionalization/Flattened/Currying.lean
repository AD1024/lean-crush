import Crush.Metatheory.Defunctionalization.Flattened.Lambda
import Crush.Metatheory.Defunctionalization.Flattened.ClosureCorrectness

/-!
# Currying and partial-spine refinement

The flattened application symbol consumes a complete leading arrow telescope in
one FO symbol application.  The unary reference semantics consumes the same
typed values one at a time.  This module identifies those two interpretations
without assuming correctness of a surrounding term translator.

For an incomplete source spine, the actual exact-capture closure selected by the
flattened transformation is related directly to the corresponding curried source
application prefix by eta correctness.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

open scoped Crush.Metatheory

variable {signature : Signature} {context : Context}
variable {start result domain codomain : Ty}

/-- Semantic values for a typed argument telescope, in source application
order.  Unlike `SourceArgs`, these arguments have already been denoted, so the
currying theorem needs no per-argument translation hypothesis. -/
inductive TypedArguments (base : BaseSort → Type) : List Ty → Type 1 where
  | nil : TypedArguments base []
  | cons {ty : Ty} {types : List Ty} :
      ty.Denote base → TypedArguments base types →
      TypedArguments base (ty :: types)

namespace TypedArguments

variable {base : BaseSort → Type}

/-- Concatenate two semantic telescopes without changing application order. -/
def append : {left right : List Ty} →
    TypedArguments base left → TypedArguments base right →
      TypedArguments base (left ++ right)
  | [], [], .nil, right => right
  | [], _ :: _, .nil, right => right
  | _ :: _, _, .cons argument rest, right =>
      .cons argument (rest.append right)

/-- Feed canonicalized semantic arguments to a curried target symbol
interpretation. -/
@[reducible] def applyFlattened (source : Model signature) :
    {types : List Ty} → TypedArguments source.Base types →
      {targetResult : FO.FOSort} →
      FO.SymbolDenote (canonicalCarriers source)
        (types.map FO.FOSort.ofTy) targetResult →
      targetResult.Denote (canonicalCarriers source)
  | [], .nil, _, function => function
  | _ :: _, .cons argument rest, _, function =>
      rest.applyFlattened source
        (function (toCanonical source _ argument))

/-- Repeated semantic source application over the complete leading telescope
of `ty`.  This is the denotation of the unary application spine. -/
@[reducible] def applyUnarySpine (source : Model signature) :
    (ty : Ty) → ty.Denote source.Base →
      TypedArguments source.Base (FO.flattenArrow ty).1 →
      (FO.flattenArrow ty).2.Denote source.Base
  | .bool, value, .nil => value
  | .base _, value, .nil => value
  | .arrow _ codomain, function, .cons argument rest =>
      applyUnarySpine source codomain (function argument) rest

/-- Generalized currying theorem: the single flattened interpretation and the
left-associated unary application spine agree for every typed complete
telescope. -/
theorem flatApp_eq_unarySpine
    (source : Model signature) :
    (ty : Ty) → (function : ty.Denote source.Base) →
    (arguments : TypedArguments source.Base (FO.flattenArrow ty).1) →
    arguments.applyFlattened source (flattenedDenote source ty function) =
      toCanonical source (FO.flattenArrow ty).2
        (arguments.applyUnarySpine source ty function) := by
  intro ty
  induction ty with
  | bool =>
      intro function arguments
      cases arguments
      rfl
  | base sort =>
      intro function arguments
      cases arguments
      rfl
  | arrow domain codomain domainIH codomainIH =>
      intro function arguments
      cases arguments with
      | cons argument rest =>
          change
            rest.applyFlattened source
                (flattenedDenote source codomain
                  (function (fromCanonical source domain
                    (toCanonical source domain argument)))) =
              toCanonical source (FO.flattenArrow codomain).2
                (rest.applyUnarySpine source codomain (function argument))
          rw [fromCanonical_toCanonical]
          exact codomainIH (function argument) rest

end TypedArguments

namespace FO.FamilyArgs

/-- Read the semantic source values of target arguments in canonical carriers. -/
noncomputable def sourceValues (source : Model signature)
    (targetValuation : TargetValuation source context) :
    (types : List Ty) →
      FO.FamilyArgs (Symbol signature) (targetContext context)
        (types.map FO.FOSort.ofTy) →
      TypedArguments source.Base types
  | [], .nil => .nil
  | _ :: _, .cons argument rest =>
      .cons
        (fromCanonical source _
          (FO.FamilyTerm.denote (canonicalModel source) argument targetValuation))
        (sourceValues source targetValuation _ rest)

/-- Applying target terms to a symbol interpretation is the same as first
reading their source values and then applying their canonical images. -/
theorem apply_eq_sourceValues
    (source : Model signature)
    (targetValuation : TargetValuation source context) :
    (types : List Ty) →
    (arguments : FO.FamilyArgs (Symbol signature) (targetContext context)
      (types.map FO.FOSort.ofTy)) →
    {targetResult : FO.FOSort} →
    (function : FO.SymbolDenote (canonicalCarriers source)
      (types.map FO.FOSort.ofTy) targetResult) →
    FO.FamilyArgs.apply arguments (canonicalModel source) targetValuation function =
      (sourceValues source targetValuation types arguments).applyFlattened
        source function := by
  intro types
  induction types with
  | nil =>
      intro arguments
      cases arguments
      intro targetResult function
      simp only [List.map]
      rw [FO.FamilyArgs.apply.eq_1]
      rw [sourceValues.eq_1]
  | cons argumentType argumentTypes inductionHypothesis =>
      intro arguments
      cases arguments with
      | cons argument rest =>
          intro targetResult function
          simp only [List.map]
          rw [FO.FamilyArgs.apply.eq_2]
          cases argumentType <;>
            simp only [sourceValues] <;>
            rw [TypedArguments.applyFlattened.eq_2] <;>
            rw [toCanonical_fromCanonical] <;>
            exact inductionHypothesis rest
              (function (FO.FamilyTerm.denote
                (canonicalModel source) argument targetValuation))

end FO.FamilyArgs

/-! ## Indexed semantic application prefixes -/

/-- Semantic arguments indexed by the source type before and after their
left-associated application.  The cons orientation exposes the first argument,
while `snoc` below matches the translator's incremental spine construction. -/
inductive AppliedValues (base : BaseSort → Type) : Ty → Ty → Type 1 where
  | nil (ty : Ty) : AppliedValues base ty ty
  | cons {domain codomain result : Ty} :
      domain.Denote base → AppliedValues base codomain result →
      AppliedValues base (.arrow domain codomain) result

namespace AppliedValues

variable {base : BaseSort → Type}

/-- Append one final semantic argument to an application prefix. -/
def snoc : {start domain codomain : Ty} →
    AppliedValues base start (.arrow domain codomain) →
      domain.Denote base → AppliedValues base start codomain
  | _, _, _, .nil _, argument => .cons argument (.nil _)
  | _, _, _, .cons first rest, argument => .cons first (rest.snoc argument)

/-- Source types consumed by the prefix, in application order. -/
def types : {start result : Ty} → AppliedValues base start result → List Ty
  | _, _, .nil _ => []
  | _, _, .cons (domain := domain) _ rest => domain :: rest.types

/-- Forget the before/after type indices while retaining the semantic
telescope. -/
def toTypedArguments : {start result : Ty} →
    (arguments : AppliedValues base start result) →
      TypedArguments base arguments.types
  | _, _, .nil _ => .nil
  | _, _, .cons argument rest => .cons argument rest.toTypedArguments

/-- Apply every value in the prefix using ordinary curried source
application. -/
@[reducible] def applyUnary : {start result : Ty} →
    AppliedValues base start result → start.Denote base → result.Denote base
  | _, _, .nil _, value => value
  | _, _, .cons argument rest, function => rest.applyUnary (function argument)

@[simp] theorem applyUnary_snoc
    (arguments : AppliedValues base start (.arrow domain codomain))
    (argument : domain.Denote base) (value : start.Denote base) :
    (arguments.snoc argument).applyUnary value =
      arguments.applyUnary value argument := by
  induction start generalizing domain codomain with
  | bool => cases arguments
  | base sort => cases arguments
  | arrow first remaining firstIH remainingIH =>
      cases arguments with
      | nil => rfl
      | cons firstArgument rest =>
          simp only [snoc, applyUnary]
          exact remainingIH rest argument (value firstArgument)

@[simp] theorem types_snoc
    (arguments : AppliedValues base start (.arrow domain codomain))
    (argument : domain.Denote base) :
    (arguments.snoc argument).types = arguments.types ++ [domain] := by
  induction start generalizing domain codomain with
  | bool => cases arguments
  | base sort => cases arguments
  | arrow first remaining firstIH remainingIH =>
      cases arguments with
      | nil => rfl
      | cons firstArgument rest =>
          simp only [snoc, types, List.cons_append, List.cons.injEq]
          exact ⟨True.intro, remainingIH rest argument⟩

end AppliedValues

namespace TargetArguments

/-- Evaluate a translated application prefix back into indexed semantic source
arguments in the canonical model. -/
noncomputable def values (source : Model signature)
    (targetValuation : TargetValuation source context) :
    {start result : Ty} → TargetArguments signature context start result →
      AppliedValues source.Base start result
  | _, _, .nil ty => .nil ty
  | _, _, .cons argument rest =>
      .cons
        (fromCanonical source _
          (FO.FamilyTerm.denote (canonicalModel source) argument targetValuation))
        (rest.values source targetValuation)

/-- Semantic denotation of a translated, possibly incomplete, application
prefix. -/
noncomputable def applyUnary (source : Model signature)
    (targetValuation : TargetValuation source context)
    {start result : Ty}
    (arguments : TargetArguments signature context start result)
    (value : start.Denote source.Base) : result.Denote source.Base :=
  match arguments with
  | .nil _ => value
  | .cons argument rest =>
      rest.applyUnary source targetValuation
        (value (fromCanonical source _
          (FO.FamilyTerm.denote (canonicalModel source) argument targetValuation)))

@[simp] theorem applyUnary_snoc (source : Model signature)
    (targetValuation : TargetValuation source context) :
    {start domain codomain : Ty} →
    (arguments : TargetArguments signature context start
      (.arrow domain codomain)) →
    (argument : TargetTerm signature context domain) →
    (value : start.Denote source.Base) →
    (arguments.snoc argument).applyUnary source targetValuation value =
      arguments.applyUnary source targetValuation value
        (fromCanonical source domain
          ⟦argument⟧[canonicalModel source, targetValuation])
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons first rest, argument, value => by
      simp only [TargetArguments.snoc, applyUnary]
      exact applyUnary_snoc source targetValuation rest argument
        (value (fromCanonical source _
          ⟦first⟧[canonicalModel source, targetValuation]))

@[simp] theorem values_types (source : Model signature)
    (targetValuation : TargetValuation source context)
    (arguments : TargetArguments signature context start result) :
    (arguments.values source targetValuation).types = arguments.types := by
  induction arguments with
  | nil =>
      rw [values.eq_1]
      rw [AppliedValues.types.eq_1]
      rw [TargetArguments.types.eq_1]
  | @cons domain codomain result argument rest inductionHypothesis =>
      cases domain <;> simp only [values, AppliedValues.types,
        TargetArguments.types, List.cons.injEq] <;>
        exact ⟨True.intro, inductionHypothesis⟩

end TargetArguments

/-- Evaluating the complete target argument telescope against the canonical
flattened symbol interpretation is ordinary repeated source application. -/
theorem TargetArguments.completeArgs_apply
    (source : Model signature)
    (targetValuation : TargetValuation source context)
    (arguments : TargetArguments signature context start result)
    (ground : GroundResult result)
    (value : start.Denote source.Base) :
    HEq (FO.FamilyArgs.apply (arguments.completeFamilyArgs ground)
        (canonicalModel source) targetValuation
        (flattenedDenote source start value))
      (toCanonical source result
        (arguments.applyUnary source targetValuation value)) := by
  induction arguments with
  | nil =>
      cases ground <;>
        simp only [TargetArguments.completeFamilyArgs,
          flattenedDenote, TargetArguments.applyUnary, toCanonical] <;>
        simp only [List.map] <;>
        rw [FO.FamilyArgs.apply.eq_1]
  | @cons domain codomain result argument rest inductionHypothesis =>
      simp only [TargetArguments.completeFamilyArgs,
        flattenedDenote, TargetArguments.applyUnary]
      simp only [List.map]
      rw [FO.FamilyArgs.apply.eq_2]
      exact inductionHypothesis ground
        (value (fromCanonical source domain
          (FO.FamilyTerm.denote (canonicalModel source) argument targetValuation)))

/-- Transporting a term's sort index does not change its denotation, up to the
corresponding heterogeneous equality of carrier types. -/
theorem FO.FamilyTerm.denote_castSort_heq
    {symbols : FO.SymbolFamily} (model : FO.FamilyModel symbols)
    {context : FO.Context} {sourceSort targetSort : FO.FOSort}
    (equality : sourceSort = targetSort)
    (term : FO.FamilyTerm symbols context sourceSort)
    (valuation : FO.FamilyValuation model context) :
    HEq (FO.FamilyTerm.denote model (term.castSort equality) valuation)
      (FO.FamilyTerm.denote model term valuation) := by
  cases equality
  rfl

/-- Denotation of a complete direct source-symbol application. -/
theorem TargetArguments.sourceApp_denote
    (source : Model signature)
    (targetValuation : TargetValuation source context)
    (constant : Const signature start)
    (arguments : TargetArguments signature context start result)
    (ground : GroundResult result) :
    FO.FamilyTerm.denote (canonicalModel source)
        (arguments.sourceApplication constant ground) targetValuation =
      toCanonical source result
        (arguments.applyUnary source targetValuation (source.const constant)) := by
  apply eq_of_heq
  let raw : TargetTerm signature context (FO.flattenArrow start).2 :=
    .symbol (Symbol.sourceConstant constant)
      (arguments.completeFamilyArgs ground)
  have resultSortEquality :
      FO.FOSort.ofTy (FO.flattenArrow start).2 = FO.FOSort.ofTy result :=
    congrArg FO.FOSort.ofTy
      (arguments.result_eq_flattenArrow ground).symm
  have denotationEquality := FO.FamilyTerm.denote_castSort_heq
    (canonicalModel source) resultSortEquality raw targetValuation
  change HEq
    (FO.FamilyTerm.denote (canonicalModel source)
      (raw.castSort resultSortEquality) targetValuation)
    (toCanonical source result
      (arguments.applyUnary source targetValuation (source.const constant)))
  exact denotationEquality.trans (by
    dsimp only [raw]
    simpa only [FO.FamilyTerm.denote.eq_2,
      canonicalModel_sourceConstant, sourceDecl] using
      arguments.completeArgs_apply
        source targetValuation ground (source.const constant))

/-- Denotation of the actual single-symbol flattened application emitted for a
complete target spine. -/
theorem TargetArguments.completeApp_denote
    (source : Model signature)
    (targetValuation : TargetValuation source context)
    (head : TargetTerm signature context (.arrow domain codomain))
    (arguments : TargetArguments signature context
      (.arrow domain codomain) result)
    (ground : GroundResult result) :
    FO.FamilyTerm.denote (canonicalModel source)
        (arguments.completeApplication head ground) targetValuation =
      toCanonical source result
        (arguments.applyUnary source targetValuation
          (fromCanonical source (.arrow domain codomain)
            (FO.FamilyTerm.denote (canonicalModel source) head targetValuation))) := by
  apply eq_of_heq
  change TargetTerm signature context (.arrow domain codomain) at head
  let completeArguments : FO.FamilyArgs (Symbol signature)
      (targetContext context)
      (FO.FOSort.ofTy domain ::
        (FO.flattenArrow codomain).1.map FO.FOSort.ofTy) :=
    arguments.completeFamilyArgs ground
  let applicationArguments : FO.FamilyArgs (Symbol signature)
      (targetContext context) (FO.appDecl domain codomain).args :=
    .cons head completeArguments
  let raw : TargetTerm signature context
      (FO.flattenArrow (.arrow domain codomain)).2 :=
    .symbol (Symbol.application { domain, codomain })
      applicationArguments
  have resultSortEquality :
      (FO.appDecl domain codomain).result = FO.FOSort.ofTy result := by
    simpa only [FO.appDecl, FO.flattenArrow_arrow] using
      congrArg FO.FOSort.ofTy
        (arguments.result_eq_flattenArrow ground).symm
  have denotationEquality := FO.FamilyTerm.denote_castSort_heq
    (canonicalModel source) resultSortEquality raw targetValuation
  change HEq
    (FO.FamilyTerm.denote (canonicalModel source)
      (raw.castSort resultSortEquality) targetValuation)
    (toCanonical source result
      (arguments.applyUnary source targetValuation
        (fromCanonical source (.arrow domain codomain)
          (FO.FamilyTerm.denote (canonicalModel source) head targetValuation))))
  exact denotationEquality.trans (by
    dsimp only [raw]
    have correctness :=
      arguments.completeArgs_apply source targetValuation
        ground
        (FO.FamilyTerm.denote (canonicalModel source) head targetValuation)
    rw [FO.FamilyTerm.denote.eq_2]
    rw [canonicalModel_application]
    dsimp only [applicationArguments]
    simp only [FO.appDecl, List.map]
    rw [FO.FamilyArgs.apply.eq_2]
    change HEq
      ((arguments.completeFamilyArgs ground).apply (canonicalModel source)
        targetValuation
        (flattenedDenote source (.arrow domain codomain)
          (FO.FamilyTerm.denote (canonicalModel source) head targetValuation)))
      (toCanonical source result
        (arguments.applyUnary source targetValuation
          (FO.FamilyTerm.denote (canonicalModel source) head targetValuation)))
    exact correctness)

namespace AppliedArguments

/-- Denotation of an arbitrary, possibly incomplete, source application
prefix. -/
@[reducible] def applyDenote (source : Model signature)
    (valuation : Valuation source.Base context) :
    {start result : Ty} → AppliedArguments signature context start result →
      start.Denote source.Base → result.Denote source.Base
  | _, _, .nil _, value => value
  | _, _, .snoc previous argument, value =>
      previous.applyDenote source valuation value
        (Term.denote source argument valuation)

/-- Rebuilding a source application prefix and then denoting it is the same as
repeated semantic unary application. -/
theorem denote_applyTerm (source : Model signature)
    (valuation : Valuation source.Base context) :
    {start result : Ty} →
    (arguments : AppliedArguments signature context start result) →
    (head : Term signature context start) →
    Term.denote source (arguments.applyTerm head) valuation =
      arguments.applyDenote source valuation
        (Term.denote source head valuation) := by
  intro start result arguments
  induction arguments with
  | nil =>
      intro head
      simp only [AppliedArguments.applyTerm]
      rw [AppliedArguments.applyDenote.eq_1]
  | snoc previous argument inductionHypothesis =>
      intro head
      simp only [AppliedArguments.applyTerm, Term.denote]
      rw [inductionHypothesis head]
      rw [AppliedArguments.applyDenote.eq_2]

end AppliedArguments

/-- The exact-capture closure used for an incomplete spine denotes precisely the
function value obtained by its unary application prefix.  This is the
partial-application complement of the complete currying theorem above. -/
theorem etaClosure_eq_partialSpine
    (source : Model signature)
    (head : Term signature context start)
    (arguments : AppliedArguments signature context start
      (.arrow domain codomain))
    (targetValuation : TargetValuation source context) :
    let applied := arguments.applyTerm head
    let closure : Closure signature :=
      Closure.ofBody (LambdaBody.etaBody applied)
    FO.FamilyTerm.denote (canonicalModel source)
        (.symbol (Symbol.closure closure) (captureArgs closure.captureRefs))
        targetValuation =
      toCanonical source (.arrow domain codomain)
        (arguments.applyDenote source
          (sourceValuation source targetValuation)
          (Term.denote source head
            (sourceValuation source targetValuation))) := by
  dsimp only
  rw [denote_closure]
  rw [LambdaBody.denote_etaBody]
  rw [AppliedArguments.denote_applyTerm]

end Crush.Metatheory.Defunctionalization.Flattened
