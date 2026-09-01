import Crush.Metatheory.Datatype.Guarded
import Crush.Metatheory.Datatype.Model
import Crush.Metatheory.FO.Guarded

/-!
# Extending a base-carrier family by one datatype block

Dependency-ordered datatype blocks are interpreted one at a time. A sort declared by
the new block becomes the complete free algebra over the prior carriers;
every other sort keeps its prior carrier. The indexed constructors make the two
cases disjoint without a cast-heavy type-level lookup.
-/

namespace Crush.Metatheory.Datatype

open Crush.Metatheory.Guarded

/-- Extend a prior base-carrier family by the complete free values of one
datatype block. `external` carries an explicit proof that its sort is not declared by
the block, so a declared sort contains only datatype values. -/
inductive BaseLift {arity : Nat} (block : Block arity)
    (Prior : BaseSort → Type) (sort : BaseSort) : Type where
  | data (dataRef : DataRef block) (same : dataRef.decl.sort = sort)
      (value : Val block Prior dataRef) : BaseLift block Prior sort
  | external
      (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort)
      (value : Prior sort) : BaseLift block Prior sort

namespace BaseLift

/-- A sort declared by the block exposes its unique free-datatype value. -/
def asData {arity : Nat} {block : Block arity} (wf : block.WF)
    {Prior : BaseSort → Type} (dataRef : DataRef block) :
    BaseLift block Prior dataRef.decl.sort → Val block Prior dataRef
  | .data other same value => by
      have equal : other = dataRef := wf.data_eq same
      subst other
      exact value
  | .external fresh _ => False.elim (fresh dataRef rfl)

@[simp] theorem asData_data {arity : Nat} {block : Block arity}
    (wf : block.WF) {Prior : BaseSort → Type} (dataRef : DataRef block)
    {same : dataRef.decl.sort = dataRef.decl.sort}
    (value : Val block Prior dataRef) :
    asData wf dataRef (.data dataRef same value) = value := by
  rw [Subsingleton.elim same rfl]
  simp [asData]

/-- Re-embedding the unique datatype value recovers the original carrier value. -/
theorem data_asData {arity : Nat} {block : Block arity}
    (wf : block.WF) {Prior : BaseSort → Type} (dataRef : DataRef block)
    (value : BaseLift block Prior dataRef.decl.sort) :
    .data dataRef rfl (asData wf dataRef value) = value := by
  cases value with
  | data other same value =>
      have equal : other = dataRef := wf.data_eq same
      subst other
      simp [asData]
  | external fresh value => exact False.elim (fresh dataRef rfl)

/-- A sort known to be external exposes its unchanged prior value. -/
def asExternal {arity : Nat} {block : Block arity}
    {Prior : BaseSort → Type} (sort : BaseSort)
    (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort) :
    BaseLift block Prior sort → Prior sort
  | .data dataRef same _ => False.elim (fresh dataRef same)
  | .external _ value => value

@[simp] theorem asExternal_external {arity : Nat} {block : Block arity}
    {Prior : BaseSort → Type} (sort : BaseSort)
    (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort)
    (value : Prior sort) :
    asExternal sort fresh (.external fresh value) = value := rfl

/-- Re-embedding a known external value recovers the original carrier value. -/
theorem external_asExternal {arity : Nat} {block : Block arity}
    {Prior : BaseSort → Type} (sort : BaseSort)
    (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort)
    (value : BaseLift block Prior sort) :
    .external fresh (asExternal sort fresh value) = value := by
  cases value with
  | data dataRef same value => exact False.elim (fresh dataRef same)
  | external otherFresh value => rfl

/-- A declared-sort carrier is isomorphic to the corresponding complete free
datatype carrier. -/
def dataIso {arity : Nat} {block : Block arity} (wf : block.WF)
    {Prior : BaseSort → Type} (dataRef : DataRef block) :
    Iso (BaseLift block Prior dataRef.decl.sort) (Val block Prior dataRef) where
  to := asData wf dataRef
  «from» := .data dataRef rfl
  left_inv := data_asData wf dataRef
  right_inv := asData_data wf dataRef

/-- A sort external to the block is isomorphic to its unchanged prior
carrier. -/
def externalIso {arity : Nat} {block : Block arity}
    {Prior : BaseSort → Type} (sort : BaseSort)
    (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort) :
    Iso (BaseLift block Prior sort) (Prior sort) where
  to := asExternal sort fresh
  «from» := .external fresh
  left_inv := external_asExternal sort fresh
  right_inv := asExternal_external sort fresh

/-- Every extended carrier is inhabited when the prior carriers are inhabited
and the datatype block is productive. -/
theorem nonempty {arity : Nat} {block : Block arity}
    (productive : Productive block) {Prior : BaseSort → Type}
    (prior : ∀ sort, Nonempty (Prior sort)) :
    ∀ sort, Nonempty (BaseLift block Prior sort) := by
  classical
  intro sort
  by_cases dataAtSort : ∃ dataRef : DataRef block, dataRef.decl.sort = sort
  · let dataRef := Classical.choose dataAtSort
    have equal := Classical.choose_spec dataAtSort
    let ⟨value⟩ := val_nonempty productive prior dataRef
    exact equal ▸ ⟨.data dataRef rfl value⟩
  · let fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort := by
      intro dataRef equal
      exact dataAtSort ⟨dataRef, equal⟩
    exact ⟨.external fresh (Classical.choice (prior sort))⟩

/-- Representation at a sort declared by the new block: cross the source carrier
isomorphism, then lift the complete constructor tree pointwise. -/
def datatypeRepr {arity : Nat} {block : Block arity} (wf : block.WF)
    (productive : Productive block)
    {Source : BaseSort → Type} {Prior : BaseSort → Type}
    (base : BaseReprs Source Prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (Source dataRef.decl.sort) (Val block Source dataRef))
    (dataRef : DataRef block) :
    SubsetRepr (Source dataRef.decl.sort) (BaseLift block Prior dataRef.decl.sort) :=
  let lifted := Datatype.lift base productive dataRef
  { sourceNonempty := base dataRef.decl.sort |>.sourceNonempty
    encode := fun value =>
      .data dataRef rfl (lifted.encode (carrier dataRef |>.to value))
    guard := fun value => lifted.guard (asData wf dataRef value)
    encode_guard := fun value => by
      simp only [asData_data]
      exact lifted.encode_guard _
    decode := fun value guarded =>
      carrier dataRef |>.«from» (lifted.decode (asData wf dataRef value) guarded)
    decode_encode := fun value => by
      simp only [asData_data, lifted.decode_encode]
      exact (carrier dataRef).left_inv value
    encode_decode := fun value guarded => by
      rw [(carrier dataRef).right_inv]
      simp only [lifted.encode_decode]
      exact data_asData wf dataRef value }

/-- Representation at a sort not declared by the new block: wrap the existing guarded
relation without changing its semantic carrier. -/
def externalRepr {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type} {Prior : BaseSort → Type}
    (base : BaseReprs Source Prior) (sort : BaseSort)
    (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort) :
    SubsetRepr (Source sort) (BaseLift block Prior sort) where
  sourceNonempty := (base sort).sourceNonempty
  encode := fun value => .external fresh ((base sort).encode value)
  guard := fun value => (base sort).guard (asExternal sort fresh value)
  encode_guard := fun value => by
    simp only [asExternal_external]
    exact (base sort).encode_guard value
  decode := fun value guarded =>
    (base sort).decode (asExternal sort fresh value) guarded
  decode_encode := fun value => by
    simp only [asExternal_external]
    exact (base sort).decode_encode value
  encode_decode := fun value guarded => by
    rw [(base sort).encode_decode]
    exact external_asExternal sort fresh value

/-- A datatype declaration at the selected base sort. -/
abbrev DataAtSort {arity : Nat} (block : Block arity) (sort : BaseSort) :=
  { dataRef : DataRef block // dataRef.decl.sort = sort }

/-- A total lookup deciding which base sorts are declared by one datatype block. -/
structure BlockSortLookup {arity : Nat} (block : Block arity) where
  decide : ∀ sort, DataAtSort block sort ⊕
    PLift (∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort)
  complete : ∀ dataRef,
    decide dataRef.decl.sort = Sum.inl ⟨dataRef, rfl⟩

/-- The canonical lookup induced by distinct datatype sort names. -/
noncomputable def BlockSortLookup.ofWF {arity : Nat} {block : Block arity}
    (wf : block.WF) : BlockSortLookup block where
  decide := fun sort => if dataAtSort : ∃ dataRef : DataRef block,
      dataRef.decl.sort = sort then
    Sum.inl ⟨Classical.choose dataAtSort, Classical.choose_spec dataAtSort⟩
  else
    Sum.inr ⟨fun dataRef equal => dataAtSort ⟨dataRef, equal⟩⟩
  complete := by
    intro dataRef
    split
    next dataAtSort =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact wf.data_eq (Classical.choose_spec dataAtSort)
    next absent => exact False.elim (absent ⟨dataRef, rfl⟩)

theorem BlockSortLookup.external {arity : Nat} {block : Block arity}
    (sortLookup : BlockSortLookup block) (sort : BaseSort)
    (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort) :
    sortLookup.decide sort = .inr ⟨fresh⟩ := by
  cases equal : sortLookup.decide sort with
  | inl dataAtSort => exact False.elim (fresh dataAtSort.1 dataAtSort.2)
  | inr absent =>
      exact congrArg Sum.inr (Subsingleton.elim absent ⟨fresh⟩)

/-- Extend every source-to-prior base relation through an explicit block-sort
lookup for one productive datatype block. -/
def representationsWith {arity : Nat} {block : Block arity}
    (sortLookup : BlockSortLookup block) (wf : block.WF) (productive : Productive block)
    {Source : BaseSort → Type} {Prior : BaseSort → Type}
    (base : BaseReprs Source Prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (Source dataRef.decl.sort) (Val block Source dataRef)) :
    (sort : BaseSort) → SubsetRepr (Source sort) (BaseLift block Prior sort) :=
  fun sort => match sortLookup.decide sort with
    | .inl ⟨dataRef, same⟩ => same ▸ datatypeRepr wf productive base carrier dataRef
    | .inr fresh => externalRepr base sort fresh.down

/-- Canonical relation extension selected by block well-formedness. -/
noncomputable def subsetRepr {arity : Nat} {block : Block arity} (wf : block.WF)
    (productive : Productive block)
    {Source : BaseSort → Type} {Prior : BaseSort → Type}
    (base : BaseReprs Source Prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (Source dataRef.decl.sort) (Val block Source dataRef)) :
    ∀ sort, SubsetRepr (Source sort) (BaseLift block Prior sort) :=
  representationsWith (BlockSortLookup.ofWF wf) wf productive base carrier

@[simp] theorem representationsWith_datatype {arity : Nat} {block : Block arity}
    (sortLookup : BlockSortLookup block) (wf : block.WF) (productive : Productive block)
    {Source Prior : BaseSort → Type} (base : BaseReprs Source Prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (Source dataRef.decl.sort) (Val block Source dataRef))
    (dataRef : DataRef block) :
    representationsWith sortLookup wf productive base carrier dataRef.decl.sort =
      datatypeRepr wf productive base carrier dataRef := by
  unfold representationsWith
  simp [sortLookup.complete dataRef]

@[simp] theorem representationsWith_external {arity : Nat} {block : Block arity}
    (sortLookup : BlockSortLookup block) (wf : block.WF) (productive : Productive block)
    {Source Prior : BaseSort → Type} (base : BaseReprs Source Prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (Source dataRef.decl.sort) (Val block Source dataRef))
    (sort : BaseSort)
    (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort) :
    representationsWith sortLookup wf productive base carrier sort =
      externalRepr base sort fresh := by
  unfold representationsWith
  simp [sortLookup.external sort fresh]

@[simp] theorem subsetRepr_datatype {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {Source Prior : BaseSort → Type} (base : BaseReprs Source Prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (Source dataRef.decl.sort) (Val block Source dataRef))
    (dataRef : DataRef block) :
    subsetRepr wf productive base carrier dataRef.decl.sort =
      datatypeRepr wf productive base carrier dataRef := by
  simp [subsetRepr, representationsWith_datatype]

@[simp] theorem subsetRepr_external {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {Source Prior : BaseSort → Type} (base : BaseReprs Source Prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (Source dataRef.decl.sort) (Val block Source dataRef))
    (sort : BaseSort)
    (fresh : ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort) :
    subsetRepr wf productive base carrier sort = externalRepr base sort fresh := by
  exact representationsWith_external (BlockSortLookup.ofWF wf) wf productive base carrier
    sort fresh

/-- Extend the base component of an FO carrier family by one full datatype
block. Opaque defunctionalized-function carriers are unchanged. -/
def carriers {arity : Nat} {block : Block arity}
    (productive : Productive block) (prior : FO.Carriers) : FO.Carriers where
  Base := BaseLift block prior.Base
  Fn := prior.Fn
  baseNonempty := nonempty productive prior.baseNonempty
  fnNonempty := prior.fnNonempty

/-- Lift an existing source-to-target FO carrier relation through one free-datatype
block. This is the dependency-order step used to assemble the complete
target carrier family. -/
noncomputable def carrierRel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers} (relation : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef)) :
    FO.CarrierRel source (carriers productive prior) where
  base := subsetRepr wf productive relation.base carrier
  fn := relation.fn

/-! ## Transport through a later disjoint block -/

/-- An FO sort is unchanged by a block when it is logical, an opaque function
sort, or a base sort not declared by that block. -/
def External {arity : Nat} (block : Block arity) : FO.FOSort → Prop
  | .bool => True
  | .fn _ _ => True
  | .base sort => ∀ dataRef : DataRef block, dataRef.decl.sort ≠ sort

/-- Every argument and the result of a symbol declaration remain unchanged by
this datatype block. -/
def ExternalDecl {arity : Nat} (block : Block arity)
    (decl : FO.SymbolDecl) : Prop :=
  (∀ sort ∈ decl.args, External block sort) ∧ External block decl.result

/-- Embed a value of an external sort into the carrier extended by one later
datatype block. -/
def wrapWith {arity : Nat} {block : Block arity}
    (productive : Productive block) {prior : FO.Carriers}
    {sort : FO.FOSort} (external : External block sort) :
    sort.Denote prior → sort.Denote (carriers productive prior) := by
  cases sort with
  | bool => exact id
  | fn domain codomain => exact id
  | base sort => exact BaseLift.external external

/-- Read an external value back through the later carrier wrapper. -/
def unwrap {arity : Nat} {block : Block arity}
    (productive : Productive block) {prior : FO.Carriers}
    {sort : FO.FOSort} (external : External block sort) :
    sort.Denote (carriers productive prior) → sort.Denote prior := by
  cases sort with
  | bool => exact id
  | fn domain codomain => exact id
  | base sort => exact asExternal sort external

@[simp] theorem unwrap_wrap {arity : Nat} {block : Block arity}
    (productive : Productive block) {prior : FO.Carriers}
    {sort : FO.FOSort} (external : External block sort)
    (value : sort.Denote prior) :
    unwrap productive external (wrapWith productive external value) = value := by
  cases sort <;> rfl

/-- Transport a curried symbol interpretation through a later block when every
argument and its result remain external to that block. -/
def transportSymbol {arity : Nat} {block : Block arity}
    (productive : Productive block) {prior : FO.Carriers} :
    {arguments : List FO.FOSort} → {result : FO.FOSort} →
    (∀ sort ∈ arguments, External block sort) → External block result →
    FO.SymbolDenote prior arguments result →
      FO.SymbolDenote (carriers productive prior) arguments result
  | [], _, _, resultExternal, value =>
      wrapWith productive resultExternal value
  | argument :: arguments, _, argumentsExternal, resultExternal, function =>
      fun value => transportSymbol productive
        (fun sort member => argumentsExternal sort (by simp [member]))
        resultExternal
        (function (unwrap productive (argumentsExternal argument (by simp)) value))

/-- At an encoded source value, direct relation extension is exactly external
wrapping of the prior encoded value. -/
theorem wrap_encode {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers}
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {sort : FO.FOSort} (external : External block sort)
    (value : sort.Denote source) :
    wrapWith productive external ((priorRel sort).encode value) =
      ((carrierRel wf productive priorRel carrier) sort).encode value := by
  cases sort with
  | bool => rfl
  | fn domain codomain => rfl
  | base sort =>
      simp only [wrapWith, FO.CarrierRel.get, carrierRel]
      rw [subsetRepr_external wf productive priorRel.base carrier sort external]
      rfl

/-- Transporting a previously related symbol through a disjoint later block
preserves its relation to the original source interpretation. -/
theorem transportSymbol_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers}
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef)) :
    {arguments : List FO.FOSort} → {result : FO.FOSort} →
    (argumentsExternal : ∀ sort ∈ arguments, External block sort) →
    (resultExternal : External block result) →
    (sourceValue : FO.SymbolDenote source arguments result) →
    (priorValue : FO.SymbolDenote prior arguments result) →
    FO.SymbolRel priorRel sourceValue priorValue →
      FO.SymbolRel (carrierRel wf productive priorRel carrier) sourceValue
        (transportSymbol productive argumentsExternal resultExternal priorValue)
  | [], result, _, resultExternal, sourceValue, priorValue, related => by
      change wrapWith productive resultExternal priorValue =
        ((carrierRel wf productive priorRel carrier) result).encode sourceValue
      rw [related, wrap_encode wf productive priorRel carrier resultExternal]
  | argument :: arguments, result, argumentsExternal,
      resultExternal, sourceValue, priorValue, related => by
      intro value
      simp only [transportSymbol]
      rw [← wrap_encode wf productive priorRel carrier
          (argumentsExternal argument (by simp)) value,
        unwrap_wrap]
      exact transportSymbol_rel wf productive priorRel carrier
        (fun sort member => argumentsExternal sort (by simp [member]))
        resultExternal (sourceValue value) (priorValue ((priorRel argument).encode value))
        (related value)

/-- Curry a constructor telescope over the original source carriers. Recursive
arguments cross the source carrier isomorphism into free constructor payloads. -/
def sourceCurry {arity : Nat} {block : Block arity}
    (source : FO.Carriers)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef)) :
    (fields : List (FieldDecl arity)) → (result : BaseSort) →
    (Args block source.Base fields → source.Base result) →
      FO.SymbolDenote source (fields.map fun field => field.fo block) (.base result)
  | [], _, build => build .nil
  | { name, sort := .base sort } :: rest, result, build =>
      fun value => sourceCurry source carrier rest result fun tail =>
        build (.base value tail)
  | { name, sort := .data child } :: rest, result, build =>
      fun value => sourceCurry source carrier rest result fun tail =>
        build (.data ((carrier child).to value) tail)

/-- Source interpretation of one constructor at its flattened FO declaration. -/
def sourceCtor {arity : Nat} {block : Block arity}
    (source : FO.Carriers)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) :
    FO.SymbolDenote source
      (ctor.fields.map fun field => field.fo block) (.base dataRef.decl.sort) :=
  sourceCurry source carrier ctor.fields dataRef.decl.sort fun args =>
    (carrier dataRef).«from» (.ctor ctorRef args)

/-- Curry a constructor telescope over the enlarged target carriers. External
fields are unwrapped to their prior payload and recursive fields to their free
datatype payload; the result is re-embedded at its dataAtSort sort. -/
def targetCurry {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block) (prior : FO.Carriers)
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) :
    (fields : List (FieldDecl arity)) →
    (refs : ∀ {field}, Ref fields field → FieldRef ctor field) →
    (Args block prior.Base fields → BaseLift block prior.Base dataRef.decl.sort) →
    FO.SymbolDenote (carriers productive prior)
      (fields.map fun field => field.fo block) (.base dataRef.decl.sort)
  | [], _, build => build .nil
  | field :: rest, refs, build =>
      match field with
      | ⟨name, .base sort⟩ =>
          let fresh : ∀ child : DataRef block,
              child.decl.sort ≠ sort := fun child =>
            (wf.base_ne_data ctorRef (refs .here) rfl child).symm
          fun value => targetCurry wf productive prior ctorRef rest
            (fun ref => refs (.there ref)) fun tail =>
              build (.base (asExternal sort fresh value) tail)
      | ⟨name, .data child⟩ =>
          fun value => targetCurry wf productive prior ctorRef rest
            (fun ref => refs (.there ref)) fun tail =>
              build (.data (asData wf child value) tail)

/-- Full free-algebra interpretation of one native constructor in the enlarged
FO carriers. -/
def targetCtor {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block) (prior : FO.Carriers)
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) :
    FO.SymbolDenote (carriers productive prior)
      (ctor.fields.map fun field => field.fo block) (.base dataRef.decl.sort) :=
  targetCurry wf productive prior ctorRef ctor.fields (fun ref => ref) fun args =>
    .data dataRef rfl (.ctor ctorRef args)

/-- Source and full target constructor currying are related whenever their
result builders agree on pointwise encoded argument telescopes. -/
theorem curry_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) :
    (fields : List (FieldDecl arity)) →
    (refs : ∀ {field}, Ref fields field → FieldRef ctor field) →
    (sourceBuild : Args block source.Base fields → source.Base dataRef.decl.sort) →
    (targetBuild : Args block prior.Base fields →
      BaseLift block prior.Base dataRef.decl.sort) →
    (∀ args, targetBuild (args.encode priorRel.base) =
      ((carrierRel wf productive priorRel carrier) (.base dataRef.decl.sort)).encode
        (sourceBuild args)) →
    FO.SymbolRel (carrierRel wf productive priorRel carrier)
      (sourceCurry source carrier fields dataRef.decl.sort sourceBuild)
      (targetCurry wf productive prior ctorRef fields refs targetBuild)
  | [], refs, sourceBuild, targetBuild, builders => by
      change targetBuild .nil =
        ((carrierRel wf productive priorRel carrier)
          (.base dataRef.decl.sort)).encode (sourceBuild .nil)
      simpa [Args.encode] using builders .nil
  | field :: rest, refs, sourceBuild, targetBuild, builders => by
      cases field with
      | mk name sort =>
          cases sort with
          | base sort =>
              intro value
              let fresh : ∀ child : DataRef block,
                  child.decl.sort ≠ sort := fun child =>
                (wf.base_ne_data ctorRef (refs .here) rfl child).symm
              simp only [sourceCurry, targetCurry, FO.CarrierRel.get,
                FieldDecl.fo, FieldSort.fo, carrierRel,
                subsetRepr_external wf productive priorRel.base carrier
                  sort fresh,
                externalRepr, asExternal_external]
              apply curry_rel wf productive source prior priorRel carrier ctorRef
                rest (fun ref => refs (.there ref))
              intro args
              simpa [Args.encode] using builders (.base value args)
          | data child =>
              intro value
              change source.Base
                (DataRef.decl (block := block) child).sort at value
              have encoded :
                  ((carrierRel wf productive priorRel carrier)
                      (FieldDecl.fo block
                        { name := name, sort := .data child })).encode value =
                    .data child rfl
                      (((carrier child).to value).encode priorRel.base) := by
                simp only [FieldDecl.fo, FieldSort.fo, FO.CarrierRel.get,
                  carrierRel]
                change
                  (subsetRepr wf productive priorRel.base carrier
                      (DataRef.decl (block := block) child).sort).encode value = _
                rw [subsetRepr_datatype wf productive priorRel.base carrier child]
                rfl
              have decoded :
                  asData wf child
                      (((carrierRel wf productive priorRel carrier)
                        (FieldDecl.fo block
                          { name := name, sort := .data child })).encode value) =
                    ((carrier child).to value).encode priorRel.base := by
                rw [encoded]
                simpa only [DataRef.decl] using
                  (asData_data wf child
                    (((carrier child).to value).encode priorRel.base))
              simp only [sourceCurry, targetCurry]
              rw [decoded]
              apply curry_rel wf productive source prior priorRel carrier ctorRef
                rest (fun ref => refs (.there ref))
              intro args
              simpa [Args.encode] using
                builders (.data ((carrier child).to value) args)

/-- Every full target constructor preserves the source constructor on encoded
arguments. This is the `ModelRel` obligation for native constructors. -/
theorem ctor_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) :
    FO.SymbolRel (carrierRel wf productive priorRel carrier)
      (sourceCtor source carrier ctorRef)
      (targetCtor wf productive prior ctorRef) := by
  apply curry_rel wf productive source prior priorRel carrier ctorRef
    ctor.fields (fun ref => ref)
  intro args
  simp only [FO.CarrierRel.get, carrierRel]
  rw [subsetRepr_datatype wf productive priorRel.base carrier dataRef]
  change BaseLift.data dataRef rfl (.ctor ctorRef (args.encode priorRel.base)) =
    BaseLift.data dataRef rfl
      (((carrier dataRef).to
        ((carrier dataRef).«from» (.ctor ctorRef args))).encode priorRel.base)
  rw [(carrier dataRef).right_inv]
  rfl

/-- Canonical fallback payload for a total native selector. -/
noncomputable def fieldDefault {arity : Nat} {block : Block arity}
    (productive : Productive block) (prior : FO.Carriers)
    (field : FieldDecl arity) : field.Denote block prior.Base := by
  classical
  cases field with
  | mk name sort =>
      cases sort with
      | base sort => exact Classical.choice (prior.baseNonempty sort)
      | data child =>
          exact Classical.choice (val_nonempty productive prior.baseNonempty child)

/-- Embed a free constructor payload into the enlarged FO carrier selected by
its field declaration. -/
def putField {arity : Nat} {block : Block arity} (wf : block.WF)
    (productive : Productive block) (prior : FO.Carriers)
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) (field : FieldDecl arity)
    (fieldRef : FieldRef ctor field) :
    field.Denote block prior.Base →
      (field.fo block).Denote (carriers productive prior)
  := match field with
    | ⟨name, .base sort⟩ => fun value =>
        let fresh : ∀ child : DataRef block,
            child.decl.sort ≠ sort := fun child =>
          (wf.base_ne_data ctorRef fieldRef rfl child).symm
        .external fresh value
    | ⟨name, .data child⟩ => fun value => .data child rfl value

/-- Convert a canonical source field payload to its flattened FO carrier. -/
def sourceField {arity : Nat} {block : Block arity}
    {source : FO.Carriers}
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    (field : FieldDecl arity) :
    field.Denote block source.Base → (field.fo block).Denote source :=
  match field with
  | ⟨_, .base _⟩ => id
  | ⟨_, .data child⟩ => (carrier child).«from»

/-- Embedding a native field into its enlarged carrier turns the structural
field guard into exactly the shared carrier guard. -/
theorem putField_guard {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers} (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) (field : FieldDecl arity)
    (fieldRef : FieldRef ctor field)
    (value : field.Denote block prior.Base) :
    ((carrierRel wf productive priorRel carrier)
      (field.fo block)).guard
        (putField wf productive prior ctorRef field fieldRef value) ↔
      field.WF (fun sort => (priorRel.base sort).guard) value := by
  cases field with
  | mk name sort =>
      cases sort with
      | base sort =>
          let fresh : ∀ child : DataRef block,
              child.decl.sort ≠ sort := fun child =>
            (wf.base_ne_data ctorRef fieldRef rfl child).symm
          simp only [FieldDecl.fo, FieldSort.fo, putField,
            FO.CarrierRel.get, carrierRel]
          rw [subsetRepr_external wf productive priorRel.base carrier sort fresh]
          rfl
      | data child =>
          simp only [FieldDecl.fo, FieldSort.fo, putField,
            FO.CarrierRel.get, carrierRel]
          change
            (subsetRepr wf productive priorRel.base carrier
              (DataRef.decl (block := block) child).sort).guard
                (.data child rfl value) ↔ _
          rw [subsetRepr_datatype wf productive priorRel.base carrier child]
          rfl

/-- Decoding an embedded target field agrees with structural field decoding
followed by conversion back to the source carrier. -/
theorem decode_putField {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers} (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) (field : FieldDecl arity)
    (fieldRef : FieldRef ctor field)
    (value : field.Denote block prior.Base)
    (wellFormed : field.WF (fun sort => (priorRel.base sort).guard) value) :
    let guarded := (putField_guard wf productive priorRel carrier ctorRef
      field fieldRef value).2 wellFormed
    ((carrierRel wf productive priorRel carrier)
      (field.fo block)).decode
        (putField wf productive prior ctorRef field fieldRef value) guarded =
      sourceField carrier field
        (field.decode priorRel.base value wellFormed) := by
  cases field with
  | mk name sort =>
      cases sort with
      | base base =>
          simp only [FieldDecl.fo, FieldSort.fo, putField,
            FO.CarrierRel.get, carrierRel]
          let fresh : ∀ child : DataRef block,
              child.decl.sort ≠ base := fun child =>
            (wf.base_ne_data ctorRef fieldRef rfl child).symm
          simp [subsetRepr_external wf productive priorRel.base carrier base fresh,
            externalRepr, sourceField, FieldDecl.decode]
      | data child =>
          simp only [FieldDecl.fo, FieldSort.fo, putField,
            FO.CarrierRel.get, carrierRel]
          change
            (subsetRepr wf productive priorRel.base carrier
              (DataRef.decl (block := block) child).sort).decode
                (.data child rfl value) _ = _
          simp [
            subsetRepr_datatype wf productive priorRel.base carrier child,
            datatypeRepr, sourceField, FieldDecl.decode]
          congr

/-- Full target interpretation of one native selector. On guarded values it
preserves the source model's (possibly arbitrary) interpretation. On values
outside the guarded image it uses the free-algebra selector, which is the
behavior required by the native datatype declaration on matching constructors. -/
noncomputable def targetSel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers} (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (sourceSel : source.Base dataRef.decl.sort →
      (field.fo block).Denote source) :
    FO.SymbolDenote (carriers productive prior)
      [(.base dataRef.decl.sort)] (field.fo block) := by
  classical
  exact fun value =>
    let relation := carrierRel wf productive priorRel carrier
    if guarded : (relation (.base dataRef.decl.sort)).guard value then
      (relation (field.fo block)).encode
        (sourceSel ((relation (.base dataRef.decl.sort)).decode value guarded))
    else
      putField wf productive prior ctorRef field fieldRef
        (sel ctorRef fieldRef (fieldDefault productive prior field)
          (asData wf dataRef value))

/-- The guarded target selector agrees with the source selector on every
encoded source value, including its unspecified behavior on nonmatching
constructors. -/
theorem sel_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (sourceSel : source.Base dataRef.decl.sort →
      (field.fo block).Denote source) :
    FO.SymbolRel (arguments := [.base dataRef.decl.sort])
      (result := field.fo block)
      (carrierRel wf productive priorRel carrier)
      sourceSel
      (targetSel wf productive priorRel carrier ctorRef fieldRef sourceSel) := by
  intro value
  simp only [targetSel]
  have guarded := ((carrierRel wf productive priorRel carrier)
    (.base dataRef.decl.sort)).encode_guard value
  rw [dif_pos guarded]
  rw [((carrierRel wf productive priorRel carrier)
    (.base dataRef.decl.sort)).decode_encode value]
  rfl

/-- On its own constructor, the guarded target selector satisfies the native
free-datatype selector equation, whether or not the constructor payload is in
the source image. -/
theorem targetSel_ctor {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (sourceSel : source.Base dataRef.decl.sort →
      (field.fo block).Denote source)
    (matching : ∀ args : Args block source.Base ctor.fields,
      sourceSel ((carrier dataRef).«from» (.ctor ctorRef args)) =
        sourceField carrier field (args.get fieldRef))
    (args : Args block prior.Base ctor.fields) :
    targetSel wf productive priorRel carrier ctorRef fieldRef sourceSel
        (.data dataRef rfl (.ctor ctorRef args)) =
      putField wf productive prior ctorRef field fieldRef
        (args.get fieldRef) := by
  classical
  let relation := carrierRel wf productive priorRel carrier
  unfold targetSel
  dsimp only
  by_cases guarded :
      (relation (.base dataRef.decl.sort)).guard
        (.data dataRef rfl (.ctor ctorRef args))
  · rw [dif_pos guarded]
    have wellFormed :
        args.WF (fun sort => (priorRel.base sort).guard) := by
      change
        (subsetRepr wf productive priorRel.base carrier dataRef.decl.sort).guard
          (.data dataRef rfl (.ctor ctorRef args)) at guarded
      rw [subsetRepr_datatype wf productive priorRel.base carrier dataRef] at guarded
      exact guarded
    let decodedArgs := args.decode priorRel.base wellFormed
    have decoded :
        (relation (.base dataRef.decl.sort)).decode
            (.data dataRef rfl (.ctor ctorRef args)) guarded =
          (carrier dataRef).«from» (.ctor ctorRef decodedArgs) := by
      change
        (subsetRepr wf productive priorRel.base carrier dataRef.decl.sort).decode
            (.data dataRef rfl (.ctor ctorRef args)) guarded = _
      simp [subsetRepr_datatype wf productive priorRel.base carrier dataRef,
        datatypeRepr, decodedArgs]
      congr
    rw [decoded, matching decodedArgs]
    let fieldWF := args.get_wf
      (fun sort => (priorRel.base sort).guard) fieldRef wellFormed
    have decodedField := decode_putField wf productive priorRel carrier
      ctorRef field fieldRef (args.get fieldRef) fieldWF
    have targetGuard := (putField_guard wf productive priorRel carrier
      ctorRef field fieldRef (args.get fieldRef)).2 fieldWF
    calc
      (relation (field.fo block)).encode
          (sourceField carrier field (decodedArgs.get fieldRef)) =
          (relation (field.fo block)).encode
            (sourceField carrier field
              (field.decode priorRel.base (args.get fieldRef) fieldWF)) := by
            rw [Args.get_decode]
      _ = (relation (field.fo block)).encode
          ((relation (field.fo block)).decode
            (putField wf productive prior ctorRef field fieldRef
              (args.get fieldRef)) targetGuard) := by
            rw [decodedField]
      _ = putField wf productive prior ctorRef field fieldRef
          (args.get fieldRef) :=
        (relation (field.fo block)).encode_decode _ targetGuard
  · rw [dif_neg guarded]
    simp only [asData_data, sel_ctor]

/-- Full target interpretation of one native constructor tester. -/
def targetTest {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block) (prior : FO.Carriers)
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor) :
    FO.SymbolDenote (carriers productive prior)
      [(.base dataRef.decl.sort)] .bool :=
  fun value => IsCtor ctorRef (asData wf dataRef value)

/-- A native tester preserves the source tester on encoded datatype values. -/
theorem test_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ dataRef : DataRef block,
      Iso (source.Base dataRef.decl.sort) (Val block source.Base dataRef))
    {dataRef : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block dataRef ctor)
    (sourceTest : source.Base dataRef.decl.sort → Prop)
    (meaning : ∀ value, sourceTest value ↔
      IsCtor ctorRef ((carrier dataRef).to value)) :
    FO.SymbolRel (arguments := [.base dataRef.decl.sort]) (result := .bool)
      (carrierRel wf productive priorRel carrier)
      sourceTest (targetTest wf productive prior ctorRef) := by
  intro value
  apply propext
  have encoded :
      ((carrierRel wf productive priorRel carrier)
        (.base dataRef.decl.sort)).encode value =
      .data dataRef rfl (((carrier dataRef).to value).encode priorRel.base) := by
    change
      (subsetRepr wf productive priorRel.base carrier dataRef.decl.sort).encode value = _
    rw [subsetRepr_datatype wf productive priorRel.base carrier dataRef]
    rfl
  change IsCtor ctorRef
      (asData wf dataRef
        (((carrierRel wf productive priorRel carrier)
          (.base dataRef.decl.sort)).encode value)) ↔ sourceTest value
  rw [encoded, asData_data, meaning]
  exact Val.isCtor_encode_iff priorRel.base ctorRef ((carrier dataRef).to value)

end BaseLift

end Crush.Metatheory.Datatype
