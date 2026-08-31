import Crush.Metatheory.FO.FamilySemantics
import Crush.Metatheory.Guarded.Encoding

/-!
# Guarded lifting of first-order models

This module separates carrier enlargement from raw SMT syntax. A relation is
supplied for every typed FO sort; source symbol interpretations are then
totalized canonically on target arguments and re-encoded at their result sort.
-/

namespace Crush.Metatheory.FO

open Crush.Metatheory.Guarded

/-- Guarded relations for all nonlogical FO carriers. Boolean propositions are
fixed to the identity relation, so logical truth is never re-encoded. -/
structure CarrierRel (source target : Carriers) where
  base : ∀ sort, SubsetRepresentation (source.Base sort) (target.Base sort)
  fn : ∀ domain codomain,
    SubsetRepresentation (source.Fn domain codomain) (target.Fn domain codomain)

/-- Relation selected by one typed FO sort. -/
def CarrierRel.get {source target : Carriers}
    (relation : CarrierRel source target) :
    (sort : FOSort) → SubsetRepresentation (sort.Denote source) (sort.Denote target)
  | .bool => SubsetRepresentation.refl Prop
  | .base sort => relation.base sort
  | .fn domain codomain => relation.fn domain codomain

instance {source target : Carriers} : CoeFun (CarrierRel source target)
    (fun _ => (sort : FOSort) →
      SubsetRepresentation (sort.Denote source) (sort.Denote target)) where
  coe := CarrierRel.get

/-- Assemble a full FO carrier relation from base and defunctionalized-function
relations. Boolean propositions use the identity relation. -/
def CarrierRel.ofBase {source target : Carriers}
    (base : ∀ sort, SubsetRepresentation (source.Base sort) (target.Base sort))
    (fn : ∀ domain codomain,
      SubsetRepresentation (source.Fn domain codomain) (target.Fn domain codomain)) :
    CarrierRel source target where
  base
  fn

/-- Identity relation on one complete FO carrier family. -/
def CarrierRel.refl (carriers : Carriers) : CarrierRel carriers carriers where
  base := fun sort => @SubsetRepresentation.refl (carriers.Base sort) (carriers.baseNonempty sort)
  fn := fun domain codomain =>
    @SubsetRepresentation.refl (carriers.Fn domain codomain) (carriers.fnNonempty domain codomain)

/-- Lift one curried typed symbol interpretation through pointwise guarded
carrier relations. Decoding is total outside the guarded image, while every
result is re-encoded and therefore guarded. -/
noncomputable def liftSymbol {source target : Carriers}
    (relation : CarrierRel source target) :
    {arguments : List FOSort} → {result : FOSort} →
      SymbolDenote source arguments result →
      SymbolDenote target arguments result
  | [], result, value => (relation result).encode value
  | argument :: arguments, result, function => fun value =>
      liftSymbol relation
        (function ((relation argument).decodeDefault value))

@[simp] theorem liftSymbol_nil {source target : Carriers}
    (relation : CarrierRel source target) {result : FOSort}
    (value : result.Denote source) :
    liftSymbol relation (arguments := []) value =
      (relation result).encode value := rfl

/-- At an encoded argument, lifted application agrees exactly with source
application followed by lifting the remaining telescope. -/
@[simp] theorem liftSymbol_encode {source target : Carriers}
    (relation : CarrierRel source target) {argument result : FOSort}
    {arguments : List FOSort}
    (function : SymbolDenote source (argument :: arguments) result)
    (value : argument.Denote source) :
    liftSymbol relation function ((relation argument).encode value) =
      liftSymbol relation (function value) := by
  simp [liftSymbol]

/-- Pointwise preservation relation for one curried symbol interpretation. -/
def SymbolRel {source target : Carriers}
    (relation : CarrierRel source target) :
    {arguments : List FOSort} → {result : FOSort} →
      SymbolDenote source arguments result →
      SymbolDenote target arguments result → Prop
  | [], result, sourceValue, targetValue =>
      targetValue = (relation result).encode sourceValue
  | argument :: arguments, result, sourceFn, targetFn =>
      ∀ value, SymbolRel relation (sourceFn value)
        (targetFn ((relation argument).encode value))

/-- Canonical lifting preserves every symbol interpretation. -/
theorem liftSymbol_rel {source target : Carriers}
    (relation : CarrierRel source target) {arguments : List FOSort}
    {result : FOSort} (function : SymbolDenote source arguments result) :
    SymbolRel relation function (liftSymbol relation function) := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih =>
      intro value
      simp only [liftSymbol]
      rw [SubsetRepresentation.decodeDefault_encode]
      exact ih (function value)

/-- Every symbol interpretation is related to itself by the identity carrier
relation. -/
theorem SymbolRel.refl (carriers : Carriers) {arguments : List FOSort}
    {result : FOSort} (value : SymbolDenote carriers arguments result) :
    SymbolRel (CarrierRel.refl carriers) value value := by
  induction arguments with
  | nil => cases result <;>
      simp [SymbolRel, CarrierRel.refl, CarrierRel.get, SubsetRepresentation.refl]
  | cons argument arguments ih =>
      intro input
      cases argument <;>
        simpa [CarrierRel.refl, CarrierRel.get, SubsetRepresentation.refl] using ih (value input)

/-- Canonical target model obtained by lifting every source symbol through one
shared carrier relation. -/
noncomputable def FamilyModel.lift {symbols : SymbolFamily}
    (source : FamilyModel symbols) (target : Carriers)
    (relation : CarrierRel source.carriers target) : FamilyModel symbols where
  carriers := target
  symbol := fun symbol => liftSymbol relation (source.symbol symbol)

@[simp] theorem FamilyModel.lift_symbol {symbols : SymbolFamily}
    (source : FamilyModel symbols) (target : Carriers)
    (relation : CarrierRel source.carriers target)
    {decl : SymbolDecl} (symbol : symbols decl) :
    (source.lift target relation).symbol symbol =
      liftSymbol relation (source.symbol symbol) := rfl

/-- Two family models agree on encoded arguments and results for every source
symbol. Native components can establish this relation with their genuine target
interpretation instead of being forced through generic totalized lifting. -/
structure ModelRel {symbols : SymbolFamily}
    (source target : FamilyModel symbols)
    (relation : CarrierRel source.carriers target.carriers) : Prop where
  symbol : ∀ {decl : SymbolDecl} (name : symbols decl),
    SymbolRel relation (source.symbol name) (target.symbol name)

/-- The generic lifted family model is related to its source model. -/
theorem FamilyModel.lift_rel {symbols : SymbolFamily}
    (source : FamilyModel symbols) (target : Carriers)
    (relation : CarrierRel source.carriers target) :
    ModelRel source (source.lift target relation) relation where
  symbol := fun name => liftSymbol_rel relation (source.symbol name)

/-- Every family model is related to itself by the identity carrier relation. -/
theorem ModelRel.refl {symbols : SymbolFamily}
    (model : FamilyModel symbols) :
    ModelRel model model (CarrierRel.refl model.carriers) where
  symbol := fun symbol => SymbolRel.refl model.carriers (model.symbol symbol)

/-- Lift a source valuation pointwise into the guarded target carriers. -/
def FamilyValuation.lift {symbols : SymbolFamily}
    {source : FamilyModel symbols} {target : Carriers}
    (relation : CarrierRel source.carriers target) {context : Context}
    (valuation : FamilyValuation source context) :
    Valuation target context :=
  fun {_} ref => (relation _).encode (valuation ref)

@[simp] theorem FamilyValuation.lift_apply {symbols : SymbolFamily}
    {source : FamilyModel symbols} {target : Carriers}
    (relation : CarrierRel source.carriers target) {context : Context}
    (valuation : FamilyValuation source context) {sort : FOSort}
    (ref : Var context sort) :
    valuation.lift relation ref = (relation sort).encode (valuation ref) := rfl

@[simp] theorem FamilyValuation.lift_extend {symbols : SymbolFamily}
    {source : FamilyModel symbols} {target : Carriers}
    (relation : CarrierRel source.carriers target) {context : Context}
    {sort : FOSort} (valuation : FamilyValuation source context)
    (value : sort.Denote source.carriers) :
    (FamilyValuation.lift relation (Valuation.extend valuation value) :
      Valuation target (sort :: context)) =
    (Valuation.extend (FamilyValuation.lift relation valuation)
      ((relation sort).encode value) : Valuation target (sort :: context)) := by
  funext result ref
  cases ref <;> rfl

mutual
  /-- Semantics of an FO term over target carriers, with quantifiers restricted
  to the guarded image of their source carrier. -/
  def FamilyTerm.guardDenote {symbols : SymbolFamily}
      (model : FamilyModel symbols)
      (guard : ∀ sort : FOSort, sort.Denote model.carriers → Prop) :
      {context : Context} → {sort : FOSort} →
        FamilyTerm symbols context sort → FamilyValuation model context →
          sort.Denote model.carriers
    | _, _, .var ref, valuation => valuation ref
    | _, _, .symbol symbol arguments, valuation =>
        arguments.guardApply model guard valuation (model.symbol symbol)
    | _, _, .boolLit true, _ => True
    | _, _, .boolLit false, _ => False
    | _, _, .not body, valuation => ¬body.guardDenote model guard valuation
    | _, _, .and left right, valuation =>
        left.guardDenote model guard valuation ∧
          right.guardDenote model guard valuation
    | _, _, .or left right, valuation =>
        left.guardDenote model guard valuation ∨
          right.guardDenote model guard valuation
    | _, _, .imp left right, valuation =>
        left.guardDenote model guard valuation →
          right.guardDenote model guard valuation
    | _, _, .iff left right, valuation =>
        left.guardDenote model guard valuation ↔
          right.guardDenote model guard valuation
    | _, _, .eq left right, valuation =>
        left.guardDenote model guard valuation =
          right.guardDenote model guard valuation
    | _, _, .forallE (domain := domain) body, valuation =>
        ∀ value, guard domain value →
          body.guardDenote model guard (valuation.extend value)
    | _, _, .existsE (domain := domain) body, valuation =>
        ∃ value, guard domain value ∧
          body.guardDenote model guard (valuation.extend value)

  /-- Apply a symbol to arguments interpreted with guarded quantifiers. -/
  def FamilyArgs.guardApply {symbols : SymbolFamily}
      (model : FamilyModel symbols)
      (guard : ∀ sort : FOSort, sort.Denote model.carriers → Prop) :
      {context : Context} → {sorts : List FOSort} →
        FamilyArgs symbols context sorts → FamilyValuation model context →
        {result : FOSort} → SymbolDenote model.carriers sorts result →
          result.Denote model.carriers
    | _, [], .nil, _, _, function => function
    | _, _ :: _, .cons argument rest, valuation, _, function =>
        rest.guardApply model guard valuation
          (function (argument.guardDenote model guard valuation))
end

attribute [simp]
  FamilyTerm.guardDenote.eq_1 FamilyTerm.guardDenote.eq_2
  FamilyTerm.guardDenote.eq_3 FamilyTerm.guardDenote.eq_4
  FamilyTerm.guardDenote.eq_5 FamilyTerm.guardDenote.eq_6
  FamilyTerm.guardDenote.eq_7 FamilyTerm.guardDenote.eq_8
  FamilyTerm.guardDenote.eq_9 FamilyTerm.guardDenote.eq_10
  FamilyTerm.guardDenote.eq_11 FamilyTerm.guardDenote.eq_12
  FamilyArgs.guardApply.eq_1 FamilyArgs.guardApply.eq_2

private def RelatesTerm {symbols : SymbolFamily}
    (source target : FamilyModel symbols)
    (relation : CarrierRel source.carriers target.carriers)
    {context : Context} {sort : FOSort}
    (term : FamilyTerm symbols context sort) : Prop :=
  ∀ valuation : FamilyValuation source context,
    term.guardDenote target
        (fun sort => (relation sort).guard) (valuation.lift relation) =
      (relation sort).encode (term.denote source valuation)

private def RelatesArgs {symbols : SymbolFamily}
    (source target : FamilyModel symbols)
    (relation : CarrierRel source.carriers target.carriers)
    {context : Context} {sorts : List FOSort}
    (args : FamilyArgs symbols context sorts) : Prop :=
  ∀ (valuation : FamilyValuation source context) {result : FOSort}
      (sourceFn : SymbolDenote source.carriers sorts result)
      (targetFn : SymbolDenote target.carriers sorts result),
    SymbolRel relation sourceFn targetFn →
    args.guardApply target
        (fun sort => (relation sort).guard) (valuation.lift relation)
        targetFn =
      (relation result).encode (args.apply source valuation sourceFn)

/-- Guard-restricted denotation in the lifted model is exactly source
denotation followed by the carrier encoding. This is one theorem for variables,
symbols, connectives, equality, and both quantifiers. -/
theorem FamilyTerm.guardDenote_rel {symbols : SymbolFamily}
    (source target : FamilyModel symbols)
    (relation : CarrierRel source.carriers target.carriers)
    (models : ModelRel source target relation)
    {context : Context} {sort : FOSort}
    (term : FamilyTerm symbols context sort) :
    RelatesTerm source target relation term := by
  classical
  exact FamilyTerm.rec
    (motive_1 := fun _ _ term => RelatesTerm source target relation term)
    (motive_2 := fun _ _ args => RelatesArgs source target relation args)
    (var := fun ref valuation => by
      simp [FamilyTerm.guardDenote, FamilyTerm.denote,
        FamilyValuation.lift])
    (symbol := fun symbol args argsIH valuation => by
      simpa only [FamilyTerm.guardDenote.eq_2, FamilyTerm.denote.eq_2] using
        argsIH valuation (source.symbol symbol) (target.symbol symbol)
          (models.symbol symbol))
    (boolLit := fun value valuation => by
      cases value <;> simp [CarrierRel.get, SubsetRepresentation.refl])
    (not := fun body bodyIH valuation => by
      simp only [FamilyTerm.guardDenote.eq_5, FamilyTerm.denote.eq_5]
      rw [bodyIH valuation]
      rfl)
    (and := fun left right leftIH rightIH valuation => by
      simp only [FamilyTerm.guardDenote.eq_6, FamilyTerm.denote.eq_6]
      rw [leftIH valuation, rightIH valuation]
      rfl)
    (or := fun left right leftIH rightIH valuation => by
      simp only [FamilyTerm.guardDenote.eq_7, FamilyTerm.denote.eq_7]
      rw [leftIH valuation, rightIH valuation]
      rfl)
    (imp := fun left right leftIH rightIH valuation => by
      simp only [FamilyTerm.guardDenote.eq_8, FamilyTerm.denote.eq_8]
      rw [leftIH valuation, rightIH valuation]
      rfl)
    (iff := fun left right leftIH rightIH valuation => by
      simp only [FamilyTerm.guardDenote.eq_9, FamilyTerm.denote.eq_9]
      rw [leftIH valuation, rightIH valuation]
      rfl)
    (eq := fun left right leftIH rightIH valuation => by
      simp only [FamilyTerm.guardDenote.eq_10, FamilyTerm.denote.eq_10]
      rw [leftIH valuation, rightIH valuation]
      exact propext ((relation _).encode_eq_iff _ _))
    (forallE := fun body bodyIH valuation => by
      simp only [FamilyTerm.guardDenote.eq_11, FamilyTerm.denote.eq_11,
        CarrierRel.get, SubsetRepresentation.refl, id_eq]
      change (∀ value,
          (relation _).guard value →
            body.guardDenote target
              (fun sort => (relation sort).guard)
              (Valuation.extend (valuation.lift relation) value)) =
        (∀ value,
          body.denote source (valuation.extend value))
      apply propext
      symm
      apply (relation _).forall_iff
      intro value
      rw [← FamilyValuation.lift_extend]
      exact Iff.of_eq (bodyIH (valuation.extend value)).symm)
    (existsE := fun body bodyIH valuation => by
      simp only [FamilyTerm.guardDenote.eq_12, FamilyTerm.denote.eq_12,
        CarrierRel.get, SubsetRepresentation.refl, id_eq]
      change (∃ value,
          (relation _).guard value ∧
            body.guardDenote target
              (fun sort => (relation sort).guard)
              (Valuation.extend (valuation.lift relation) value)) =
        (∃ value,
          body.denote source (valuation.extend value))
      apply propext
      symm
      apply (relation _).exists_iff
      intro value
      rw [← FamilyValuation.lift_extend]
      exact Iff.of_eq (bodyIH (valuation.extend value)).symm)
    (nil := fun {_} valuation result sourceFn targetFn related => by
      change targetFn = (relation result).encode sourceFn at related
      simpa [SymbolDenote, FamilyArgs.guardApply, FamilyArgs.apply] using related)
    (cons := fun argument rest argumentIH restIH valuation result sourceFn
        targetFn related => by
      simp only [FamilyArgs.guardApply.eq_2, FamilyArgs.apply.eq_2]
      rw [argumentIH valuation]
      exact restIH valuation (sourceFn (argument.denote source valuation))
        (targetFn ((relation _).encode (argument.denote source valuation)))
        (related (argument.denote source valuation)))
    term

/-- Generic symbol lifting is the ordinary specialization of model-relative
guarded preservation. -/
theorem FamilyTerm.guardDenote_lift {symbols : SymbolFamily}
    (source : FamilyModel symbols) (target : Carriers)
    (relation : CarrierRel source.carriers target)
    {context : Context} {sort : FOSort}
    (term : FamilyTerm symbols context sort) :
    RelatesTerm source (source.lift target relation) relation term :=
  term.guardDenote_rel source (source.lift target relation) relation
    (source.lift_rel target relation)

end Crush.Metatheory.FO
