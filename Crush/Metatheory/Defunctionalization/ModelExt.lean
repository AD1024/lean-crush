import Crush.Metatheory.Defunctionalization.Fundamental

/-!
# Canonical target-model extension for defunctionalization

The canonical model interprets every target function-value sort by the
corresponding source function space.  Exact closure captures are reconstructed
into a source valuation; semantic dependence on free variables proves that the
arbitrary values used for uncaptured variables are irrelevant.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature}

namespace SourceValuation

/-- In one intrinsically typed context, a numeric de Bruijn position determines
the existentially packaged reference, including its type. -/
theorem packedVar_eq_of_index_eq {context : Context}
    (left right : PackedVar context)
    (indicesEqual : left.index = right.index) : left = right := by
  induction context with
  | nil =>
      cases left with | pack ref => cases ref
  | cons head tail ih =>
      cases left with
      | pack leftRef =>
        cases right with
        | pack rightRef =>
          cases leftRef with
          | here =>
              cases rightRef with
              | here => rfl
              | there rightRef => simp [PackedVar.index, refToNat] at indicesEqual
          | there leftRef =>
              cases rightRef with
              | here => simp [PackedVar.index, refToNat] at indicesEqual
              | there rightRef =>
                  have tailEqual :
                      (PackedVar.pack leftRef : PackedVar tail) =
                        PackedVar.pack rightRef := by
                    apply ih
                    simpa [PackedVar.index, refToNat] using indicesEqual
                  cases tailEqual
                  rfl

/-- Replace one entry of an intrinsically typed source valuation. -/
def set {base : BaseSort → Type} {context : Context} {ty : Ty}
    (valuation : Valuation base context) (ref : Var context ty)
    (value : ty.Denote base) : Valuation base context :=
  fun {queryTy} query =>
    match ref, query with
    | .here, .here => value
    | .here, .there query => valuation (.there query)
    | .there _, .here => valuation .here
    | .there ref, .there query =>
        set (fun tailRef => valuation (.there tailRef)) ref value query
termination_by refToNat ref
decreasing_by simp [refToNat]

@[simp] theorem set_self {base : BaseSort → Type} {context : Context} {ty : Ty}
    (valuation : Valuation base context) (ref : Var context ty)
    (value : ty.Denote base) :
    set valuation ref value ref = value := by
  induction ref with
  | here => simp [set]
  | there ref ih =>
      simp only [set]
      exact ih (fun tailRef => valuation (.there tailRef)) value

theorem set_of_index_ne {base : BaseSort → Type} {context : Context}
    {boundTy queryTy : Ty} (valuation : Valuation base context)
    (bound : Var context boundTy) (value : boundTy.Denote base)
    (query : Var context queryTy)
    (indicesDifferent : refToNat bound ≠ refToNat query) :
    set valuation bound value query = valuation query := by
  induction bound generalizing queryTy with
  | here =>
      cases query with
      | here => exact (indicesDifferent rfl).elim
      | there query => simp [set]
  | there bound ih =>
      cases query with
      | here => simp [set]
      | there query =>
          simp only [set]
          apply ih
          simpa [refToNat] using indicesDifferent

/-- A canonical valuation, used only at variables that a closure does not
capture.  Source-type nonemptiness makes this total. -/
noncomputable def default (source : Model signature) (context : Context) :
    Valuation source.Base context :=
  fun {ty} _ => Classical.choice (Ty.denoteNonempty source.Base source.baseNonempty ty)

end SourceValuation

/-! ## Semantic dependence on collected free variables -/

/-- Two valuations agree on all typed references whose numeric positions occur
free in a term. -/
def AgreeOnTerm {source : Model signature} {context : Context} {ty : Ty}
    (term : Term signature context ty)
    (left right : Valuation source.Base context) : Prop :=
  ∀ {refTy : Ty} (ref : Var context refTy),
    refToNat ref ∈ freeVarIndices term → left ref = right ref

private theorem leaveBinder_nodup {indices : List Nat}
    (nodup : indices.Nodup) : (leaveBinder indices).Nodup := by
  induction indices with
  | nil => simp [leaveBinder]
  | cons index indices ih =>
      have tailNodup := nodup.tail
      cases index with
      | zero => simpa [leaveBinder] using ih tailNodup
      | succ index =>
          simp only [leaveBinder, List.filterMap_cons]
          have headNotMem : index + 1 ∉ indices := by
            intro membership
            exact (List.pairwise_cons.mp nodup).1 _ membership rfl
          constructor
          · intro item membership itemEqual
            apply headNotMem
            subst item
            simp only [List.mem_filterMap] at membership
            obtain ⟨sourceIndex, sourceMembership, mapped⟩ := membership
            cases sourceIndex with
            | zero => simp at mapped
            | succ sourceIndex =>
                simp only [Option.some.injEq] at mapped
                subst sourceIndex
                exact sourceMembership
          · exact ih tailNodup

private theorem eraseDups_nodup (indices : List Nat) :
    indices.eraseDups.Nodup := by
  cases indices with
  | nil => simp
  | cons index indices =>
      rw [List.eraseDups_cons]
      apply List.pairwise_cons.mpr
      constructor
      · intro item membership
        simp only [List.mem_eraseDups, List.mem_filter] at membership
        exact fun equality => by simp [equality] at membership
      · exact eraseDups_nodup (indices.filter fun item => !item == index)
termination_by indices.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_add_one_of_le (List.length_filter_le _ _)

theorem freeVarIndices_nodup {context : Context} {ty : Ty} :
    (term : Term signature context ty) → (freeVarIndices term).Nodup := by
  intro term
  induction term with
  | var => simp [freeVarIndices]
  | const | boolLit => simp [freeVarIndices]
  | not body ih => simpa [freeVarIndices] using ih
  | and => exact eraseDups_nodup _
  | or => exact eraseDups_nodup _
  | imp => exact eraseDups_nodup _
  | iff => exact eraseDups_nodup _
  | eq => exact eraseDups_nodup _
  | app => exact eraseDups_nodup _
  | lam => exact eraseDups_nodup _
  | forallE => exact eraseDups_nodup _
  | existsE => exact eraseDups_nodup _

theorem Closure.captures_nodup (closure : Closure signature) :
    closure.captures.Nodup := by
  exact leaveBinder_nodup (freeVarIndices_nodup closure.body)

theorem PackedVar.at?_index {context : Context} {index : Nat}
    {packed : PackedVar context}
    (lookup : PackedVar.at? context index = some packed) :
    packed.index = index := by
  induction context generalizing index with
  | nil => simp [PackedVar.at?] at lookup
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [PackedVar.at?] at lookup
          cases lookup
          rfl
      | succ index =>
          simp only [PackedVar.at?] at lookup
          cases tailLookup : PackedVar.at? tail index with
          | none => simp [tailLookup] at lookup
          | some tailPacked =>
              cases tailPacked with
              | pack tailRef =>
                  simp only [tailLookup, Option.map_some, Option.some.injEq] at lookup
                  cases lookup
                  simpa [PackedVar.index, refToNat] using
                    ih tailLookup

private theorem map_index_filterMap_at? (context : Context) (indices : List Nat)
    (bounded : ∀ index ∈ indices, index < context.length) :
    (indices.filterMap (PackedVar.at? context)).map PackedVar.index = indices := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      have indexBound := bounded index (by simp)
      have tailBound : ∀ item ∈ indices, item < context.length := by
        intro item membership
        exact bounded item (by simp [membership])
      cases lookup : PackedVar.at? context index with
      | none =>
          have present := (PackedVar.at?_isSome_iff context index).2 indexBound
          simp [lookup] at present
      | some packed =>
          simp only [List.filterMap_cons, lookup, List.map_cons, List.cons.injEq]
          exact ⟨PackedVar.at?_index lookup, ih tailBound⟩

theorem Closure.captureRefs_indices (closure : Closure signature) :
    closure.captureRefs.map PackedVar.index = closure.captures := by
  apply map_index_filterMap_at?
  exact fun index membership => closure.capture_lt index membership

theorem Closure.captureRefs_indices_nodup (closure : Closure signature) :
    (closure.captureRefs.map PackedVar.index).Nodup := by
  rw [closure.captureRefs_indices]
  exact closure.captures_nodup

private theorem mem_leaveBinder_of_succ_mem {index : Nat} {indices : List Nat}
    (membership : index + 1 ∈ indices) : index ∈ leaveBinder indices := by
  simp only [leaveBinder, List.mem_filterMap]
  exact ⟨index + 1, membership, rfl⟩

/-- Source denotation depends only on the variables reported by the executable
free-variable collector. -/
theorem Term.denote_eq_of_agreeOnTerm {source : Model signature} :
    {context : Context} → {ty : Ty} →
    (term : Term signature context ty) →
    (left right : Valuation source.Base context) →
    AgreeOnTerm term left right →
    Term.denote source term left = Term.denote source term right := by
  intro context ty term
  induction term with
  | var ref =>
      intro left right agreement
      exact agreement ref (by simp [freeVarIndices])
  | const => intros; rfl
  | boolLit value =>
      intros
      cases value <;> rfl
  | not body ih =>
      intro left right agreement
      simp only [Term.denote]
      rw [ih left right agreement]
  | and leftTerm rightTerm leftIH rightIH =>
      intro left right agreement
      simp only [Term.denote]
      rw [leftIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
      rw [rightIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
  | or leftTerm rightTerm leftIH rightIH =>
      intro left right agreement
      simp only [Term.denote]
      rw [leftIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
      rw [rightIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
  | imp leftTerm rightTerm leftIH rightIH =>
      intro left right agreement
      simp only [Term.denote]
      rw [leftIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
      rw [rightIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
  | iff leftTerm rightTerm leftIH rightIH =>
      intro left right agreement
      simp only [Term.denote]
      rw [leftIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
      rw [rightIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
  | eq leftTerm rightTerm leftIH rightIH =>
      intro left right agreement
      simp only [Term.denote]
      rw [leftIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
      rw [rightIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
  | app fn argument fnIH argumentIH =>
      intro left right agreement
      simp only [Term.denote]
      rw [fnIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
      rw [argumentIH left right (by
        intro refTy ref membership
        exact agreement ref (by simp [freeVarIndices, membership]))]
  | lam body bodyIH =>
      intro left right agreement
      simp only [Term.denote]
      funext value
      apply bodyIH
      intro refTy ref membership
      cases ref with
      | here => rfl
      | there ref =>
          exact agreement ref (by
            simp only [freeVarIndices, List.mem_eraseDups]
            exact mem_leaveBinder_of_succ_mem membership)
  | forallE body bodyIH =>
      intro left right agreement
      simp only [Term.denote]
      apply propext
      apply forall_congr'
      intro value
      have denotationEq := bodyIH
        (left.extend value) (right.extend value) (by
          intro refTy ref membership
          cases ref with
          | here => rfl
          | there ref =>
              exact agreement ref (by
                simp only [freeVarIndices, List.mem_eraseDups]
                exact mem_leaveBinder_of_succ_mem membership))
      exact denotationEq.to_iff
  | existsE body bodyIH =>
      intro left right agreement
      simp only [Term.denote]
      apply propext
      apply exists_congr
      intro value
      have denotationEq := bodyIH
        (left.extend value) (right.extend value) (by
          intro refTy ref membership
          cases ref with
          | here => rfl
          | there ref =>
              exact agreement ref (by
                simp only [freeVarIndices, List.mem_eraseDups]
                exact mem_leaveBinder_of_succ_mem membership))
      exact denotationEq.to_iff

/-! ## The canonical extension -/

/-- Function-value sorts are realized by the corresponding genuine source
function spaces. -/
@[reducible] def canonicalCarriers (source : Model signature) : FO.Carriers where
  Base := source.Base
  Fn domain codomain := (Ty.arrow domain codomain).Denote source.Base
  baseNonempty := source.baseNonempty
  fnNonempty domain codomain :=
    Ty.denoteNonempty source.Base source.baseNonempty (.arrow domain codomain)

/-- The type-directed coercions below are extensionally identities.  Naming
them lets Lean normalize the two recursive type interpretations without relying
on reduction through an unknown source type. -/
@[reducible] def toCanonical (source : Model signature) :
    (ty : Ty) → ty.Denote source.Base →
      (FO.FOSort.ofTy ty).Denote (canonicalCarriers source)
  | .bool, value => value
  | .base _, value => value
  | .arrow _ _, value => value

@[reducible] def fromCanonical (source : Model signature) :
    (ty : Ty) → (FO.FOSort.ofTy ty).Denote (canonicalCarriers source) →
      ty.Denote source.Base
  | .bool, value => value
  | .base _, value => value
  | .arrow _ _, value => value

/-- Reconstruct a valuation by installing the source values of the exact
captured references. -/
def installCaptured (source : Model signature) {context : Context}
    (captures : List (PackedVar context))
    (sourceValuation reconstructed : Valuation source.Base context) :
    Valuation source.Base context :=
  match captures with
  | [] => reconstructed
  | .pack ref :: captures =>
      installCaptured source captures sourceValuation
        (SourceValuation.set reconstructed ref (sourceValuation ref))

theorem installCaptured_of_not_mem (source : Model signature)
    {context : Context} (captures : List (PackedVar context))
    (sourceValuation reconstructed : Valuation source.Base context)
    {ty : Ty} (query : Var context ty)
    (absent : refToNat query ∉ captures.map PackedVar.index) :
    installCaptured source captures sourceValuation reconstructed query =
      reconstructed query := by
  induction captures generalizing reconstructed with
  | nil => rfl
  | cons capture captures ih =>
      cases capture with
      | pack ref =>
          simp only [List.map_cons, List.mem_cons, not_or] at absent
          rw [installCaptured, ih _ absent.2]
          exact SourceValuation.set_of_index_ne reconstructed ref _ query
            (Ne.symm absent.1)

theorem installCaptured_agrees (source : Model signature)
    {context : Context} (captures : List (PackedVar context))
    (nodup : (captures.map PackedVar.index).Nodup)
    (sourceValuation reconstructed : Valuation source.Base context)
    {ty : Ty} (query : Var context ty)
    (present : refToNat query ∈ captures.map PackedVar.index) :
    installCaptured source captures sourceValuation reconstructed query =
      sourceValuation query := by
  induction captures generalizing reconstructed with
  | nil => simp at present
  | cons capture captures ih =>
      cases capture with
      | pack ref =>
          simp only [List.map_cons, List.mem_cons] at present
          have tailNodup := (List.pairwise_cons.mp nodup).2
          rcases present with headEqual | tailPresent
          · have packedEqual :
                (PackedVar.pack ref : PackedVar context) = PackedVar.pack query :=
              SourceValuation.packedVar_eq_of_index_eq _ _ headEqual.symm
            cases packedEqual
            rw [installCaptured]
            rw [installCaptured_of_not_mem source captures sourceValuation
              (SourceValuation.set reconstructed query (sourceValuation query)) query]
            · exact SourceValuation.set_self reconstructed query _
            · intro membership
              exact (List.pairwise_cons.mp nodup).1 _ membership rfl
          · exact ih tailNodup
              (SourceValuation.set reconstructed ref (sourceValuation ref))
              tailPresent

/-- Install the concrete values of a list of captured references into a source
valuation.  Its curried type is definitionally the argument telescope of the
corresponding closure constructor. -/
@[reducible] noncomputable def interpretClosureCaptures (source : Model signature)
    (closure : Closure signature) :
    (captures : List (PackedVar closure.context)) →
    Valuation source.Base closure.context →
    FO.SymbolDenote (canonicalCarriers source)
      ((captures.map PackedVar.type).map FO.FOSort.ofTy)
      (.fn closure.domain closure.codomain)
  | [], valuation => Term.denote source (.lam closure.body) valuation
  | .pack ref :: captures, valuation => fun value =>
      interpretClosureCaptures source closure captures
        (SourceValuation.set valuation ref
          (fromCanonical source _ value))

/-- Interpretation of an exact-capture closure constructor. -/
@[reducible] noncomputable def interpretClosure (source : Model signature)
    (closure : Closure signature) :
    FO.SymbolDenote (canonicalCarriers source)
      (FO.closureDecl closure.captureTypes closure.domain closure.codomain).args
      (FO.closureDecl closure.captureTypes closure.domain closure.codomain).result :=
  interpretClosureCaptures source closure closure.captureRefs
    (SourceValuation.default source closure.context)

/-- Extend a source model to all symbols generated by the unary reference
defunctionalization. -/
@[reducible] noncomputable def canonicalModel (source : Model signature) :
    FO.FamilyModel (CoreSymbol signature) where
  carriers := canonicalCarriers source
  symbol := fun symbol =>
    match symbol with
    | CoreSymbol.source (ty := ty) constant =>
        toCanonical source ty (source.const constant)
    | CoreSymbol.app arrow => fun fn argument =>
        toCanonical source arrow.codomain
          (fn (fromCanonical source arrow.domain argument))
    | CoreSymbol.closure closure => interpretClosure source closure

@[simp] theorem canonicalModel_source (source : Model signature)
    {ty : Ty} (constant : Const signature ty) :
    (canonicalModel source).symbol (CoreSymbol.source constant) =
      toCanonical source ty (source.const constant) := rfl

@[simp] theorem canonicalModel_app (source : Model signature)
    (arrow : Arrow) :
    (canonicalModel source).symbol (CoreSymbol.app arrow) =
      (fun fn argument =>
        toCanonical source arrow.codomain
          (fn (fromCanonical source arrow.domain argument))) := rfl

@[simp] theorem fromCanonical_toCanonical (source : Model signature)
    (ty : Ty) (value : ty.Denote source.Base) :
    fromCanonical source ty (toCanonical source ty value) = value := by
  cases ty <;> rfl

@[simp] theorem toCanonical_fromCanonical (source : Model signature)
    (ty : Ty)
    (value : (FO.FOSort.ofTy ty).Denote (canonicalCarriers source)) :
    toCanonical source ty (fromCanonical source ty value) = value := by
  cases ty <;> rfl

/-- In the canonical extension the logical relation is graph equality under the
type-directed identity coercion. -/
theorem canonical_valueRel_iff (source : Model signature) :
    (ty : Ty) → (sourceValue : ty.Denote source.Base) →
    (targetValue :
      (FO.FOSort.ofTy ty).Denote (canonicalModel source).carriers) →
    ValueRel source (canonicalModel source)
        (fun _ sourceValue targetValue => sourceValue = targetValue)
        ty sourceValue targetValue ↔
      sourceValue = fromCanonical source ty targetValue
  | .bool, sourceValue, targetValue => by
      constructor
      · exact propext
      · intro equality
        exact equality.to_iff
  | .base _, _, _ => Iff.rfl
  | .arrow domain codomain, sourceFn, targetFn => by
      constructor
      · intro related
        funext sourceArg
        have argumentRelated :
            ValueRel source (canonicalModel source)
              (fun _ sourceValue targetValue => sourceValue = targetValue)
              domain sourceArg (toCanonical source domain sourceArg) :=
          (canonical_valueRel_iff source domain _ _).2 (by simp)
        have resultRelated := related sourceArg
          (toCanonical source domain sourceArg) argumentRelated
        exact (canonical_valueRel_iff source codomain _ _).1 resultRelated
          |>.trans (by simp)
      · intro equality sourceArg targetArg argumentRelated
        have argumentEq :=
          (canonical_valueRel_iff source domain _ _).1 argumentRelated
        apply (canonical_valueRel_iff source codomain _ _).2
        rw [equality, argumentEq]
        simp

/-- Feeding translated capture variables to a canonical closure constructor is
exactly source-valuation reconstruction. -/
theorem apply_translateCaptureRefs_interpretClosure
    (source : Model signature) (closure : Closure signature)
    (captures : List (PackedVar closure.context))
    (sourceValuation : Valuation source.Base closure.context)
    (targetValuation :
      FO.FamilyValuation (canonicalModel source) (targetContext closure.context))
    (related : ValuationRel source (canonicalModel source)
      (fun _ sourceValue targetValue => sourceValue = targetValue)
      sourceValuation targetValuation)
    (reconstructed : Valuation source.Base closure.context) :
    FO.FamilyArgs.apply (translateCaptureRefs captures)
      (canonicalModel source) targetValuation
      (interpretClosureCaptures source closure captures reconstructed) =
    Term.denote source (.lam closure.body)
      (installCaptured source captures sourceValuation reconstructed) := by
  induction captures generalizing reconstructed with
  | nil =>
      simp [translateCaptureRefs, FO.FamilyArgs.apply,
        interpretClosureCaptures, installCaptured]
  | cons capture captures ih =>
      cases capture with
      | pack ref =>
          unfold translateCaptureRefs
          simp only [List.map_cons]
          rw [FO.FamilyArgs.apply.eq_2, FO.FamilyTerm.denote.eq_1]
          unfold interpretClosureCaptures installCaptured
          have capturedEq :=
            (canonical_valueRel_iff source _ _ _).1 (related ref)
          have capturedEq' :
              fromCanonical source _ (targetValuation (targetVar ref)) =
                sourceValuation ref := capturedEq.symm
          rw [capturedEq']
          exact ih _

theorem apply_translateCaptureRefs_interpretClosure_full
    (source : Model signature) (closure : Closure signature)
    (sourceValuation : Valuation source.Base closure.context)
    (targetValuation :
      FO.FamilyValuation (canonicalModel source) (targetContext closure.context))
    (related : ValuationRel source (canonicalModel source)
      (fun _ sourceValue targetValue => sourceValue = targetValue)
      sourceValuation targetValuation) :
    FO.FamilyArgs.apply (translateCaptureRefs closure.captureRefs)
      (canonicalModel source) targetValuation
      (interpretClosure source closure) =
    Term.denote source (.lam closure.body)
      (installCaptured source closure.captureRefs sourceValuation
        (SourceValuation.default source closure.context)) := by
  unfold interpretClosure
  exact apply_translateCaptureRefs_interpretClosure source closure _
    sourceValuation targetValuation related _

/-- Reconstructing a closure's exact captures preserves the denotation of its
lambda body; uncaptured entries of the seed valuation are irrelevant. -/
theorem closure_denote_installCaptured (source : Model signature)
    (closure : Closure signature)
    (sourceValuation seed : Valuation source.Base closure.context) :
    Term.denote source (.lam closure.body) sourceValuation =
      Term.denote source (.lam closure.body)
        (installCaptured source closure.captureRefs sourceValuation seed) := by
  simp only [Term.denote]
  funext argument
  apply Term.denote_eq_of_agreeOnTerm
  intro refTy ref membership
  cases ref with
  | here => rfl
  | there ref =>
      apply Eq.symm
      apply installCaptured_agrees source closure.captureRefs
        closure.captureRefs_indices_nodup sourceValuation seed ref
      rw [closure.captureRefs_indices]
      exact mem_leaveBinder_of_succ_mem membership

theorem fromCanonical_injective_iff (source : Model signature) (ty : Ty)
    (left right :
      (FO.FOSort.ofTy ty).Denote (canonicalModel source).carriers) :
    fromCanonical source ty left = fromCanonical source ty right ↔
      left = right := by
  constructor
  · intro equality
    have := congrArg (toCanonical source ty) equality
    simpa using this
  · exact congrArg (fromCanonical source ty)

theorem canonical_denote_lambda (source : Model signature)
    {context : Context} {domain codomain : Ty}
    (body : Term signature (domain :: context) codomain)
    (sourceValuation : Valuation source.Base context)
    (targetValuation :
      FO.FamilyValuation (canonicalModel source) (targetContext context))
    (related : ValuationRel source (canonicalModel source)
      (fun _ sourceValue targetValue => sourceValue = targetValue)
      sourceValuation targetValuation) :
    FO.FamilyTerm.denote (canonicalModel source)
        (defunctionalizeCore (.lam body)) targetValuation =
      toCanonical source (.arrow domain codomain)
        (Term.denote source (.lam body) sourceValuation) := by
  simp only [defunctionalizeCore]
  unfold FO.FamilyTerm.denote
  change
    FO.FamilyArgs.apply
        (translateCaptureRefs (Closure.ofBody body).captureRefs)
        (canonicalModel source) targetValuation
        (interpretClosure source (Closure.ofBody body)) =
      Term.denote source (.lam body) sourceValuation
  rw [apply_translateCaptureRefs_interpretClosure_full source
    (Closure.ofBody body) sourceValuation targetValuation related]
  exact (closure_denote_installCaptured source (Closure.ofBody body)
    sourceValuation (SourceValuation.default source context)).symm

/-- Every source model has a canonical target extension satisfying all
compatibility obligations of the fundamental lemma. -/
noncomputable def canonicalModelRelation (source : Model signature) :
    ModelRelation source (canonicalModel source) where
  baseRel := fun _ sourceValue targetValue => sourceValue = targetValue
  constRelated := by
    intro ty constant
    apply (canonical_valueRel_iff source ty _ _).2
    simp
  equalityIff := by
    intro ty sourceLeft sourceRight targetLeft targetRight leftRelated rightRelated
    have leftEq := (canonical_valueRel_iff source ty _ _).1 leftRelated
    have rightEq := (canonical_valueRel_iff source ty _ _).1 rightRelated
    rw [leftEq, rightEq]
    exact fromCanonical_injective_iff source ty targetLeft targetRight
  leftTotal := by
    intro ty sourceValue
    refine ⟨toCanonical source ty sourceValue, ?_⟩
    apply (canonical_valueRel_iff source ty _ _).2
    simp
  rightTotal := by
    intro ty targetValue
    refine ⟨fromCanonical source ty targetValue, ?_⟩
    exact (canonical_valueRel_iff source ty _ _).2 rfl
  closureRelated := by
    intro context domain codomain body sourceValuation targetValuation related
    apply (canonical_valueRel_iff source (.arrow domain codomain) _ _).2
    rw [canonical_denote_lambda source body sourceValuation targetValuation related]

/-- Read a source valuation back from a canonical target valuation. -/
def sourceValuationOfTarget (source : Model signature) {context : Context}
    (targetValuation :
      FO.FamilyValuation (canonicalModel source) (targetContext context))
    {ty : Ty} (ref : Var context ty) : ty.Denote source.Base :=
  fromCanonical source ty (targetValuation (targetVar ref))

theorem sourceValuationOfTarget_related (source : Model signature)
    {context : Context}
    (targetValuation :
      FO.FamilyValuation (canonicalModel source) (targetContext context)) :
    ValuationRel source (canonicalModel source)
      (fun _ sourceValue targetValue => sourceValue = targetValue)
      (sourceValuationOfTarget source targetValuation) targetValuation := by
  unfold ValuationRel
  intro ty ref
  apply (canonical_valueRel_iff source ty _ _).2
  rfl

theorem apply_translateCaptureRefsUnder_extend
    (source : Model signature) {context : Context} {domain : Ty}
    (captures : List (PackedVar context))
    (targetValuation :
      FO.FamilyValuation (canonicalModel source) (targetContext context))
    (argument :
      (FO.FOSort.ofTy domain).Denote (canonicalModel source).carriers)
    {result : FO.FOSort}
    (function : FO.SymbolDenote (canonicalModel source).carriers
      ((captures.map PackedVar.type).map FO.FOSort.ofTy) result) :
    FO.FamilyArgs.apply (translateCaptureRefsUnder captures)
        (canonicalModel source) (targetValuation.extend argument) function =
      FO.FamilyArgs.apply (translateCaptureRefs captures)
        (canonicalModel source) targetValuation function := by
  induction captures with
  | nil =>
      simp [translateCaptureRefsUnder, translateCaptureRefs,
        FO.FamilyArgs.apply]
  | cons capture captures ih =>
      cases capture with
      | pack ref =>
          unfold translateCaptureRefsUnder translateCaptureRefs
          simp only [List.map_cons]
          rw [FO.FamilyArgs.apply.eq_2, FO.FamilyArgs.apply.eq_2,
            FO.FamilyTerm.denote.eq_1, FO.FamilyTerm.denote.eq_1]
          exact ih _

theorem canonical_denote_closure (source : Model signature)
    (closure : Closure signature)
    (sourceValuation : Valuation source.Base closure.context)
    (targetValuation : FO.FamilyValuation (canonicalModel source)
      (targetContext closure.context))
    (related : ValuationRel source (canonicalModel source)
      (fun _ sourceValue targetValue => sourceValue = targetValue)
      sourceValuation targetValuation) :
    FO.FamilyTerm.denote (canonicalModel source)
        (.symbol (CoreSymbol.closure closure)
          (translateCaptureRefs closure.captureRefs)) targetValuation =
      toCanonical source (.arrow closure.domain closure.codomain)
        (Term.denote source (.lam closure.body) sourceValuation) := by
  unfold FO.FamilyTerm.denote
  rw [apply_translateCaptureRefs_interpretClosure_full source closure
    sourceValuation targetValuation related]
  exact (closure_denote_installCaptured source closure sourceValuation
    (SourceValuation.default source closure.context)).symm

theorem canonical_denote_closure_under (source : Model signature)
    (closure : Closure signature)
    (sourceValuation : Valuation source.Base closure.context)
    (targetValuation : FO.FamilyValuation (canonicalModel source)
      (targetContext closure.context))
    (related : ValuationRel source (canonicalModel source)
      (fun _ sourceValue targetValue => sourceValue = targetValue)
      sourceValuation targetValuation)
    (argument : (FO.FOSort.ofTy closure.domain).Denote
      (canonicalModel source).carriers) :
    FO.FamilyTerm.denote (canonicalModel source)
        (.symbol (CoreSymbol.closure closure)
          (translateCaptureRefsUnder closure.captureRefs))
        (targetValuation.extend argument) =
      toCanonical source (.arrow closure.domain closure.codomain)
        (Term.denote source (.lam closure.body) sourceValuation) := by
  unfold FO.FamilyTerm.denote
  rw [apply_translateCaptureRefsUnder_extend source closure.captureRefs
    targetValuation argument]
  have closureEq := canonical_denote_closure source closure sourceValuation
    targetValuation related
  unfold FO.FamilyTerm.denote at closureEq
  exact closureEq

theorem canonical_denote_applied_closure (source : Model signature)
    (closure : Closure signature)
    (sourceValuation : Valuation source.Base closure.context)
    (targetValuation : FO.FamilyValuation (canonicalModel source)
      (targetContext closure.context))
    (related : ValuationRel source (canonicalModel source)
      (fun _ sourceValue targetValue => sourceValue = targetValue)
      sourceValuation targetValuation)
    (targetArgument : (FO.FOSort.ofTy closure.domain).Denote
      (canonicalModel source).carriers) :
    let closureValue : FO.FamilyTerm (CoreSymbol signature)
        (FO.FOSort.ofTy closure.domain :: targetContext closure.context)
        (.fn closure.domain closure.codomain) :=
      .symbol (CoreSymbol.closure closure)
        (translateCaptureRefsUnder closure.captureRefs)
    let applied : FO.FamilyTerm (CoreSymbol signature)
        (FO.FOSort.ofTy closure.domain :: targetContext closure.context)
        (FO.FOSort.ofTy closure.codomain) :=
      .symbol (CoreSymbol.app
        { domain := closure.domain, codomain := closure.codomain })
        (.cons closureValue (.cons (.var .here) .nil))
    FO.FamilyTerm.denote (canonicalModel source) applied
        (targetValuation.extend targetArgument) =
      toCanonical source closure.codomain
      (Term.denote source closure.body
          (sourceValuation.extend
            (fromCanonical source closure.domain targetArgument))) := by
  dsimp only
  have closureEq := canonical_denote_closure_under source closure
    sourceValuation targetValuation related targetArgument
  simp only [FO.FamilyTerm.denote.eq_2, FO.FamilyArgs.apply.eq_2,
    FO.FamilyArgs.apply.eq_1, FO.FamilyTerm.denote.eq_1]
  change
    toCanonical source closure.codomain
      ((fromCanonical source (.arrow closure.domain closure.codomain)
        (FO.FamilyTerm.denote (canonicalModel source)
          (.symbol (CoreSymbol.closure closure)
            (translateCaptureRefsUnder closure.captureRefs))
          (targetValuation.extend targetArgument)))
        (fromCanonical source closure.domain targetArgument)) = _
  have appliedClosureEq := congrArg
    (fun targetFn =>
      toCanonical source closure.codomain
        ((fromCanonical source (.arrow closure.domain closure.codomain) targetFn)
          (fromCanonical source closure.domain targetArgument))) closureEq
  unfold FO.FamilyTerm.denote
  simpa [Term.denote] using appliedClosureEq

/-- The canonical extension validates every generated closure equation. -/
theorem canonical_closure_valid (source : Model signature)
    (closure : Closure signature) :
    (canonicalModel source).Satisfies (closureEquation closure) := by
  unfold closureEquation
  apply FO.FamilyModel.satisfies_closeForall_of_forall_denote
  intro valuation
  let targetValuation : FO.FamilyValuation (canonicalModel source)
      (targetContext closure.context) :=
    fun {_} ref => valuation (.there ref)
  let targetArgument : (FO.FOSort.ofTy closure.domain).Denote
      (canonicalModel source).carriers := valuation .here
  have valuationEq :
      (@FO.Valuation.extend (canonicalModel source).carriers
        (targetContext closure.context) (FO.FOSort.ofTy closure.domain)
        targetValuation targetArgument) =
      (fun {sort : FO.FOSort}
        (ref : FO.Var
          (FO.FOSort.ofTy closure.domain :: targetContext closure.context) sort) =>
        valuation ref) := by
    apply @funext FO.FOSort
      (fun sort => FO.Var
        (FO.FOSort.ofTy closure.domain :: targetContext closure.context) sort →
          sort.Denote (canonicalModel source).carriers)
    intro sort
    apply funext
    intro ref
    cases ref <;> rfl
  rw [← valuationEq]
  simp only [FO.FamilyTerm.denote.eq_10]
  let sourceValuation : Valuation source.Base closure.context :=
    sourceValuationOfTarget source targetValuation
  have valuationsRelated :
      ValuationRel source (canonicalModel source)
        (fun _ sourceValue targetValue => sourceValue = targetValue)
        sourceValuation targetValuation :=
    sourceValuationOfTarget_related source targetValuation
  have argumentRelated :
      ValueRel source (canonicalModel source)
        (fun _ sourceValue targetValue => sourceValue = targetValue)
        closure.domain
        (fromCanonical source closure.domain targetArgument) targetArgument :=
    (canonical_valueRel_iff source closure.domain _ _).2 rfl
  have bodyRelated := fundamental (canonicalModelRelation source) closure.body
    (sourceValuation.extend
      (fromCanonical source closure.domain targetArgument))
    (targetValuation.extend targetArgument)
    (valuationsRelated.extend argumentRelated)
  have bodyEq := (canonical_valueRel_iff source closure.codomain _ _).1 bodyRelated
  apply (fromCanonical_injective_iff source closure.codomain _ _).1
  rw [canonical_denote_applied_closure source closure sourceValuation
    targetValuation valuationsRelated targetArgument]
  simpa using bodyEq

theorem canonical_closures_valid (source : Model signature)
    {context : Context} {ty : Ty} (term : Term signature context ty) :
    (canonicalModel source).SatisfiesTheory (closureEquations term) := by
  change ∀ formula ∈ (closures term).map closureEquation,
    (canonicalModel source).Satisfies formula
  intro targetFormula membership
  obtain ⟨closure, _, rfl⟩ := List.mem_map.mp membership
  exact canonical_closure_valid source closure

/-- The complete target theory for a source sentence: generated closure
equations followed by the translated formula. -/
def defunctionalizedSentence (formula : Sentence signature) :
    FO.FamilySentence (CoreSymbol signature) :=
  defunctionalizeCore formula

def defunctionalizationTheory (formula : Sentence signature) :
    FO.FamilyTheory (CoreSymbol signature) :=
  closureEquations formula ++ [defunctionalizedSentence formula]

/-- A satisfying source model extends to a target model of the complete
defunctionalization theory. -/
theorem modelExtension (source : Model signature) (formula : Sentence signature)
    (sourceSatisfies : source.Satisfies formula) :
    (canonicalModel source).SatisfiesTheory
      (defunctionalizationTheory formula) := by
  intro targetFormula membership
  simp only [defunctionalizationTheory, List.mem_append, List.mem_singleton]
    at membership
  rcases membership with equationMembership | rfl
  · exact canonical_closures_valid source formula
      targetFormula equationMembership
  · exact (fundamental_sentence (canonicalModelRelation source) formula).mp
      sourceSatisfies

/-- Semantic soundness of unary reference defunctionalization: if the generated target
theory is unsatisfiable, then the original higher-order sentence is
unsatisfiable. -/
theorem target_unsat_implies_source_unsat (formula : Sentence signature)
    (targetUnsat :
      FO.FamilyTheoryUnsatisfiable (defunctionalizationTheory formula)) :
    Unsatisfiable formula := by
  intro source sourceSatisfies
  exact targetUnsat (canonicalModel source)
    (modelExtension source formula sourceSatisfies)

end Crush.Metatheory.Defunctionalization
