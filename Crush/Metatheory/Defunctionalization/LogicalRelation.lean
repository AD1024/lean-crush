import Crush.Metatheory.Defunctionalization.Core
import Crush.Metatheory.HO.Semantics
import Crush.Metatheory.FO.FamilySemantics

/-!
# Source/target logical relation

The relation is parameterized by a relation on opaque base carriers.  At arrows,
source functions are related to target function values when the target `app`
interpretation maps related arguments to related results.  Boolean values are
related by logical equivalence.

`ModelRelation` records the additional properties required by equality and
quantification: equality reflection/preservation and totality in both directions.
The canonical model extension will discharge these fields.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature}

abbrev BaseRelation (source : Model signature)
    (target : FO.FamilyModel (CoreSymbol signature)) :=
  (sort : BaseSort) → source.Base sort → target.carriers.Base sort → Prop

/-- Type-indexed logical relation between source and target values. -/
@[reducible] def ValueRel (source : Model signature)
    (target : FO.FamilyModel (CoreSymbol signature))
    (baseRel : BaseRelation source target) :
    (ty : Ty) → ty.Denote source.Base →
      (FO.FOSort.ofTy ty).Denote target.carriers → Prop
  | .bool, sourceValue, targetValue => sourceValue ↔ targetValue
  | .base sort, sourceValue, targetValue => baseRel sort sourceValue targetValue
  | .arrow domain codomain, sourceFn, targetFn =>
      ∀ sourceArg targetArg,
        ValueRel source target baseRel domain sourceArg targetArg →
        ValueRel source target baseRel codomain (sourceFn sourceArg)
          ((target.symbol (CoreSymbol.app { domain, codomain })) targetFn targetArg)

/-- Pointwise relation between source and target local valuations. -/
def ValuationRel (source : Model signature)
    (target : FO.FamilyModel (CoreSymbol signature))
    (baseRel : BaseRelation source target) {context : Context}
    (sourceValuation : Valuation source.Base context)
    (targetValuation : FO.FamilyValuation target (targetContext context)) : Prop :=
  ∀ {ty : Ty} (ref : Var context ty),
    ValueRel source target baseRel ty (sourceValuation ref)
      (targetValuation (targetVar ref))

theorem ValuationRel.extend
    {source : Model signature} {target : FO.FamilyModel (CoreSymbol signature)}
    {baseRel : BaseRelation source target} {context : Context}
    {sourceValuation : Valuation source.Base context}
    {targetValuation : FO.FamilyValuation target (targetContext context)}
    (related : ValuationRel source target baseRel sourceValuation targetValuation)
    {ty : Ty} {sourceValue : ty.Denote source.Base}
    {targetValue : (FO.FOSort.ofTy ty).Denote target.carriers}
    (valueRelated : ValueRel source target baseRel ty sourceValue targetValue) :
    ValuationRel source target baseRel
      (sourceValuation.extend sourceValue) (targetValuation.extend targetValue) := by
  intro refTy ref
  cases ref with
  | here => exact valueRelated
  | there ref => exact related ref

/-- Compatibility assumptions between a source model and a target core model. -/
structure ModelRelation (source : Model signature)
    (target : FO.FamilyModel (CoreSymbol signature)) where
  baseRel : BaseRelation source target
  constRelated : {ty : Ty} → (constant : Const signature ty) →
    ValueRel source target baseRel ty (source.const constant)
      (target.symbol (CoreSymbol.source constant))
  equalityIff : (ty : Ty) →
    (sourceLeft sourceRight : ty.Denote source.Base) →
    (targetLeft targetRight : (FO.FOSort.ofTy ty).Denote target.carriers) →
    ValueRel source target baseRel ty sourceLeft targetLeft →
    ValueRel source target baseRel ty sourceRight targetRight →
    (sourceLeft = sourceRight ↔ targetLeft = targetRight)
  leftTotal : (ty : Ty) → (sourceValue : ty.Denote source.Base) →
    ∃ targetValue, ValueRel source target baseRel ty sourceValue targetValue
  rightTotal : (ty : Ty) →
    (targetValue : (FO.FOSort.ofTy ty).Denote target.carriers) →
    ∃ sourceValue, ValueRel source target baseRel ty sourceValue targetValue
  closureRelated : {context : Context} → {domain codomain : Ty} →
    (body : Term signature (domain :: context) codomain) →
    (sourceValuation : Valuation source.Base context) →
    (targetValuation : FO.FamilyValuation target (targetContext context)) →
    ValuationRel source target baseRel sourceValuation targetValuation →
    ValueRel source target baseRel (.arrow domain codomain)
      (Term.denote source (.lam body) sourceValuation)
      (FO.FamilyTerm.denote target (defunctionalizeCore (.lam body)) targetValuation)

end Crush.Metatheory.Defunctionalization
