import Crush.Metatheory.Defunctionalization.Lambda
import Crush.Metatheory.Notation

/-!
# Flattened application denotation

The flattened application symbol consumes a complete leading arrow telescope
in one first-order symbol application. This module proves that direct source
symbols and flattened application symbols perform the corresponding sequence
of higher-order source applications.
-/

namespace Crush.Metatheory.Defunctionalization

open scoped Crush.Metatheory

variable {signature : Signature} {context : Context}
variable {start result domain codomain : Ty}

namespace TargetArguments

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

end Crush.Metatheory.Defunctionalization
