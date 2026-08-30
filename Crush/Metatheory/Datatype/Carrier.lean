import Crush.Metatheory.Datatype.Guarded
import Crush.Metatheory.Datatype.Model
import Crush.Metatheory.FO.Guarded

/-!
# Extending a base-carrier family by one datatype block

Dependency-ordered datatype blocks are interpreted one at a time. A sort owned
by the new block becomes the complete free algebra over the prior carriers;
every other sort keeps its prior carrier. The indexed constructors make the two
cases disjoint without a cast-heavy type-level lookup.
-/

namespace Crush.Metatheory.Datatype

open Crush.Metatheory.Guarded

/-- Extend a prior base-carrier family by the complete free values of one
datatype block. `external` carries an explicit non-ownership proof, so an owned
sort contains only datatype values. -/
inductive BaseLift {arity : Nat} (block : Block arity)
    (Prior : BaseSort → Type) (sort : BaseSort) : Type where
  | data (owner : DataRef block) (same : owner.decl.sort = sort)
      (value : Val block Prior owner) : BaseLift block Prior sort
  | external
      (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort)
      (value : Prior sort) : BaseLift block Prior sort

namespace BaseLift

/-- An owned sort exposes its unique free-datatype value. -/
def asData {arity : Nat} {block : Block arity} (wf : block.WF)
    {Prior : BaseSort → Type} (owner : DataRef block) :
    BaseLift block Prior owner.decl.sort → Val block Prior owner
  | .data other same value => by
      have equal : other = owner := wf.data_eq same
      subst other
      exact value
  | .external fresh _ => False.elim (fresh owner rfl)

@[simp] theorem asData_data {arity : Nat} {block : Block arity}
    (wf : block.WF) {Prior : BaseSort → Type} (owner : DataRef block)
    {same : owner.decl.sort = owner.decl.sort}
    (value : Val block Prior owner) :
    asData wf owner (.data owner same value) = value := by
  rw [Subsingleton.elim same rfl]
  simp [asData]

/-- Re-embedding the unique owned value recovers the original carrier value. -/
theorem data_asData {arity : Nat} {block : Block arity}
    (wf : block.WF) {Prior : BaseSort → Type} (owner : DataRef block)
    (value : BaseLift block Prior owner.decl.sort) :
    .data owner rfl (asData wf owner value) = value := by
  cases value with
  | data other same value =>
      have equal : other = owner := wf.data_eq same
      subst other
      simp [asData]
  | external fresh value => exact False.elim (fresh owner rfl)

/-- A sort known to be external exposes its unchanged prior value. -/
def asExternal {arity : Nat} {block : Block arity}
    {Prior : BaseSort → Type} (sort : BaseSort)
    (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort) :
    BaseLift block Prior sort → Prior sort
  | .data owner same _ => False.elim (fresh owner same)
  | .external _ value => value

@[simp] theorem asExternal_external {arity : Nat} {block : Block arity}
    {Prior : BaseSort → Type} (sort : BaseSort)
    (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort)
    (value : Prior sort) :
    asExternal sort fresh (.external fresh value) = value := rfl

/-- Re-embedding a known external value recovers the original carrier value. -/
theorem external_asExternal {arity : Nat} {block : Block arity}
    {Prior : BaseSort → Type} (sort : BaseSort)
    (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort)
    (value : BaseLift block Prior sort) :
    .external fresh (asExternal sort fresh value) = value := by
  cases value with
  | data owner same value => exact False.elim (fresh owner same)
  | external otherFresh value => rfl

/-- An owned extended carrier is isomorphic to the corresponding complete free
datatype carrier. -/
def dataIso {arity : Nat} {block : Block arity} (wf : block.WF)
    {Prior : BaseSort → Type} (owner : DataRef block) :
    Iso (BaseLift block Prior owner.decl.sort) (Val block Prior owner) where
  to := asData wf owner
  «from» := .data owner rfl
  left_inv := data_asData wf owner
  right_inv := asData_data wf owner

/-- A sort external to the block is isomorphic to its unchanged prior
carrier. -/
def externalIso {arity : Nat} {block : Block arity}
    {Prior : BaseSort → Type} (sort : BaseSort)
    (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort) :
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
  by_cases owned : ∃ owner : DataRef block, owner.decl.sort = sort
  · let owner := Classical.choose owned
    have equal := Classical.choose_spec owned
    let ⟨value⟩ := val_nonempty productive prior owner
    exact equal ▸ ⟨.data owner rfl value⟩
  · let fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort := by
      intro owner equal
      exact owned ⟨owner, equal⟩
    exact ⟨.external fresh (Classical.choice (prior sort))⟩

/-- Relation at a sort owned by the new block: cross the source carrier
isomorphism, then lift the complete constructor tree pointwise. -/
def datatypeRepresentation {arity : Nat} {block : Block arity} (wf : block.WF)
    (productive : Productive block)
    {Source : BaseSort → Type} {Prior : BaseSort → Type}
    (base : BaseRepresentations Source Prior)
    (carrier : ∀ owner : DataRef block,
      Iso (Source owner.decl.sort) (Val block Source owner))
    (owner : DataRef block) :
    SubsetRepresentation (Source owner.decl.sort) (BaseLift block Prior owner.decl.sort) :=
  let lifted := Datatype.lift base productive owner
  { sourceNonempty := base owner.decl.sort |>.sourceNonempty
    encode := fun value =>
      .data owner rfl (lifted.encode (carrier owner |>.to value))
    guard := fun value => lifted.guard (asData wf owner value)
    encode_guard := fun value => by
      simp only [asData_data]
      exact lifted.encode_guard _
    decode := fun value guarded =>
      carrier owner |>.«from» (lifted.decode (asData wf owner value) guarded)
    decode_encode := fun value => by
      simp only [asData_data, lifted.decode_encode]
      exact (carrier owner).left_inv value
    encode_decode := fun value guarded => by
      rw [(carrier owner).right_inv]
      simp only [lifted.encode_decode]
      exact data_asData wf owner value }

/-- Relation at a sort not owned by the new block: wrap the existing guarded
relation without changing its semantic carrier. -/
def externalRepresentation {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type} {Prior : BaseSort → Type}
    (base : BaseRepresentations Source Prior) (sort : BaseSort)
    (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort) :
    SubsetRepresentation (Source sort) (BaseLift block Prior sort) where
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

/-- A datatype reference whose declaration owns the selected base sort. -/
abbrev OwnerAt {arity : Nat} (block : Block arity) (sort : BaseSort) :=
  { owner : DataRef block // owner.decl.sort = sort }

/-- A total lookup deciding which base sorts are owned by one datatype block. -/
structure Ownership {arity : Nat} (block : Block arity) where
  decide : ∀ sort, OwnerAt block sort ⊕
    PLift (∀ owner : DataRef block, owner.decl.sort ≠ sort)
  complete : ∀ owner,
    decide owner.decl.sort = Sum.inl ⟨owner, rfl⟩

/-- The canonical lookup induced by distinct datatype sort names. -/
noncomputable def Ownership.ofWF {arity : Nat} {block : Block arity}
    (wf : block.WF) : Ownership block where
  decide := fun sort => if owned : ∃ owner : DataRef block,
      owner.decl.sort = sort then
    Sum.inl ⟨Classical.choose owned, Classical.choose_spec owned⟩
  else
    Sum.inr ⟨fun owner equal => owned ⟨owner, equal⟩⟩
  complete := by
    intro owner
    split
    next owned =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact wf.data_eq (Classical.choose_spec owned)
    next notOwned => exact False.elim (notOwned ⟨owner, rfl⟩)

theorem Ownership.external {arity : Nat} {block : Block arity}
    (ownership : Ownership block) (sort : BaseSort)
    (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort) :
    ownership.decide sort = .inr ⟨fresh⟩ := by
  cases equal : ownership.decide sort with
  | inl owned => exact False.elim (fresh owned.1 owned.2)
  | inr absent =>
      exact congrArg Sum.inr (Subsingleton.elim absent ⟨fresh⟩)

/-- Extend every source-to-prior base relation through an explicit ownership
lookup for one productive datatype block. -/
def representationsWith {arity : Nat} {block : Block arity}
    (ownership : Ownership block) (wf : block.WF) (productive : Productive block)
    {Source : BaseSort → Type} {Prior : BaseSort → Type}
    (base : BaseRepresentations Source Prior)
    (carrier : ∀ owner : DataRef block,
      Iso (Source owner.decl.sort) (Val block Source owner)) :
    (sort : BaseSort) → SubsetRepresentation (Source sort) (BaseLift block Prior sort) :=
  fun sort => match ownership.decide sort with
    | .inl ⟨owner, same⟩ => same ▸ datatypeRepresentation wf productive base carrier owner
    | .inr fresh => externalRepresentation base sort fresh.down

/-- Canonical relation extension selected by block well-formedness. -/
noncomputable def subsetRepresentation {arity : Nat} {block : Block arity} (wf : block.WF)
    (productive : Productive block)
    {Source : BaseSort → Type} {Prior : BaseSort → Type}
    (base : BaseRepresentations Source Prior)
    (carrier : ∀ owner : DataRef block,
      Iso (Source owner.decl.sort) (Val block Source owner)) :
    ∀ sort, SubsetRepresentation (Source sort) (BaseLift block Prior sort) :=
  representationsWith (Ownership.ofWF wf) wf productive base carrier

@[simp] theorem representationsWith_datatype {arity : Nat} {block : Block arity}
    (ownership : Ownership block) (wf : block.WF) (productive : Productive block)
    {Source Prior : BaseSort → Type} (base : BaseRepresentations Source Prior)
    (carrier : ∀ owner : DataRef block,
      Iso (Source owner.decl.sort) (Val block Source owner))
    (owner : DataRef block) :
    representationsWith ownership wf productive base carrier owner.decl.sort =
      datatypeRepresentation wf productive base carrier owner := by
  unfold representationsWith
  simp [ownership.complete owner]

@[simp] theorem representationsWith_external {arity : Nat} {block : Block arity}
    (ownership : Ownership block) (wf : block.WF) (productive : Productive block)
    {Source Prior : BaseSort → Type} (base : BaseRepresentations Source Prior)
    (carrier : ∀ owner : DataRef block,
      Iso (Source owner.decl.sort) (Val block Source owner))
    (sort : BaseSort)
    (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort) :
    representationsWith ownership wf productive base carrier sort =
      externalRepresentation base sort fresh := by
  unfold representationsWith
  simp [ownership.external sort fresh]

@[simp] theorem subsetRepresentation_datatype {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {Source Prior : BaseSort → Type} (base : BaseRepresentations Source Prior)
    (carrier : ∀ owner : DataRef block,
      Iso (Source owner.decl.sort) (Val block Source owner))
    (owner : DataRef block) :
    subsetRepresentation wf productive base carrier owner.decl.sort =
      datatypeRepresentation wf productive base carrier owner := by
  simp [subsetRepresentation, representationsWith_datatype]

@[simp] theorem subsetRepresentation_external {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {Source Prior : BaseSort → Type} (base : BaseRepresentations Source Prior)
    (carrier : ∀ owner : DataRef block,
      Iso (Source owner.decl.sort) (Val block Source owner))
    (sort : BaseSort)
    (fresh : ∀ owner : DataRef block, owner.decl.sort ≠ sort) :
    subsetRepresentation wf productive base carrier sort = externalRepresentation base sort fresh := by
  exact representationsWith_external (Ownership.ofWF wf) wf productive base carrier
    sort fresh

/-- Extend the base component of an FO carrier family by one full datatype
block. Opaque defunctionalized-function carriers are unchanged. -/
def carriers {arity : Nat} {block : Block arity}
    (productive : Productive block) (prior : FO.Carriers) : FO.Carriers where
  Base := BaseLift block prior.Base
  Fn := prior.Fn
  baseNonempty := nonempty productive prior.baseNonempty
  fnNonempty := prior.fnNonempty

/-- Lift an existing source-to-target FO carrier relation through one lawful
datatype block. This is the dependency-order step used to assemble the complete
target carrier family. -/
noncomputable def carrierRel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers} (relation : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner)) :
    FO.CarrierRel source (carriers productive prior) where
  base := subsetRepresentation wf productive relation.base carrier
  fn := relation.fn

/-! ## Transport through a later disjoint block -/

/-- An FO sort is unchanged by a block when it is logical, an opaque function
sort, or a base sort not owned by that block. -/
def External {arity : Nat} (block : Block arity) : FO.FOSort → Prop
  | .bool => True
  | .fn _ _ => True
  | .base sort => ∀ owner : DataRef block, owner.decl.sort ≠ sort

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

/-- Carry a curried symbol interpretation through a later block when every
argument and its result remain external to that block. -/
def carry {arity : Nat} {block : Block arity}
    (productive : Productive block) {prior : FO.Carriers} :
    {arguments : List FO.FOSort} → {result : FO.FOSort} →
    (∀ sort ∈ arguments, External block sort) → External block result →
    FO.SymbolDenote prior arguments result →
      FO.SymbolDenote (carriers productive prior) arguments result
  | [], _, _, resultExternal, value =>
      wrapWith productive resultExternal value
  | argument :: arguments, _, argumentsExternal, resultExternal, function =>
      fun value => carry productive
        (fun sort member => argumentsExternal sort (by simp [member]))
        resultExternal
        (function (unwrap productive (argumentsExternal argument (by simp)) value))

/-- At an encoded source value, direct relation extension is exactly external
wrapping of the prior encoded value. -/
theorem wrap_encode {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers}
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {sort : FO.FOSort} (external : External block sort)
    (value : sort.Denote source) :
    wrapWith productive external ((priorRel sort).encode value) =
      ((carrierRel wf productive priorRel carrier) sort).encode value := by
  cases sort with
  | bool => rfl
  | fn domain codomain => rfl
  | base sort =>
      simp only [wrapWith, FO.CarrierRel.get, carrierRel]
      rw [subsetRepresentation_external wf productive priorRel.base carrier sort external]
      rfl

/-- Carrying a previously related symbol through a disjoint later block
preserves its relation to the original source interpretation. -/
theorem carry_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers}
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner)) :
    {arguments : List FO.FOSort} → {result : FO.FOSort} →
    (argumentsExternal : ∀ sort ∈ arguments, External block sort) →
    (resultExternal : External block result) →
    (sourceValue : FO.SymbolDenote source arguments result) →
    (priorValue : FO.SymbolDenote prior arguments result) →
    FO.SymbolRel priorRel sourceValue priorValue →
      FO.SymbolRel (carrierRel wf productive priorRel carrier) sourceValue
        (carry productive argumentsExternal resultExternal priorValue)
  | [], result, _, resultExternal, sourceValue, priorValue, related => by
      change wrapWith productive resultExternal priorValue =
        ((carrierRel wf productive priorRel carrier) result).encode sourceValue
      rw [related, wrap_encode wf productive priorRel carrier resultExternal]
  | argument :: arguments, result, argumentsExternal,
      resultExternal, sourceValue, priorValue, related => by
      intro value
      simp only [carry]
      rw [← wrap_encode wf productive priorRel carrier
          (argumentsExternal argument (by simp)) value,
        unwrap_wrap]
      exact carry_rel wf productive priorRel carrier
        (fun sort member => argumentsExternal sort (by simp [member]))
        resultExternal (sourceValue value) (priorValue ((priorRel argument).encode value))
        (related value)

/-- Curry a constructor telescope over the original source carriers. Recursive
arguments cross the source carrier isomorphism into free constructor payloads. -/
def sourceCurry {arity : Nat} {block : Block arity}
    (source : FO.Carriers)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner)) :
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
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    FO.SymbolDenote source
      (ctor.fields.map fun field => field.fo block) (.base data.decl.sort) :=
  sourceCurry source carrier ctor.fields data.decl.sort fun args =>
    (carrier data).«from» (.ctor ctorRef args)

/-- Curry a constructor telescope over the enlarged target carriers. External
fields are unwrapped to their prior payload and recursive fields to their free
datatype payload; the result is re-embedded at its owned sort. -/
def targetCurry {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block) (prior : FO.Carriers)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    (fields : List (FieldDecl arity)) →
    (refs : ∀ {field}, Ref fields field → FieldRef ctor field) →
    (Args block prior.Base fields → BaseLift block prior.Base data.decl.sort) →
    FO.SymbolDenote (carriers productive prior)
      (fields.map fun field => field.fo block) (.base data.decl.sort)
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
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    FO.SymbolDenote (carriers productive prior)
      (ctor.fields.map fun field => field.fo block) (.base data.decl.sort) :=
  targetCurry wf productive prior ctorRef ctor.fields (fun ref => ref) fun args =>
    .data data rfl (.ctor ctorRef args)

/-- Source and full target constructor currying are related whenever their
result builders agree on pointwise encoded argument telescopes. -/
theorem curry_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    (fields : List (FieldDecl arity)) →
    (refs : ∀ {field}, Ref fields field → FieldRef ctor field) →
    (sourceBuild : Args block source.Base fields → source.Base data.decl.sort) →
    (targetBuild : Args block prior.Base fields →
      BaseLift block prior.Base data.decl.sort) →
    (∀ args, targetBuild (args.encode priorRel.base) =
      ((carrierRel wf productive priorRel carrier) (.base data.decl.sort)).encode
        (sourceBuild args)) →
    FO.SymbolRel (carrierRel wf productive priorRel carrier)
      (sourceCurry source carrier fields data.decl.sort sourceBuild)
      (targetCurry wf productive prior ctorRef fields refs targetBuild)
  | [], refs, sourceBuild, targetBuild, builders => by
      change targetBuild .nil =
        ((carrierRel wf productive priorRel carrier)
          (.base data.decl.sort)).encode (sourceBuild .nil)
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
                subsetRepresentation_external wf productive priorRel.base carrier
                  sort fresh,
                externalRepresentation, asExternal_external]
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
                  (subsetRepresentation wf productive priorRel.base carrier
                      (DataRef.decl (block := block) child).sort).encode value = _
                rw [subsetRepresentation_datatype wf productive priorRel.base carrier child]
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
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    FO.SymbolRel (carrierRel wf productive priorRel carrier)
      (sourceCtor source carrier ctorRef)
      (targetCtor wf productive prior ctorRef) := by
  apply curry_rel wf productive source prior priorRel carrier ctorRef
    ctor.fields (fun ref => ref)
  intro args
  simp only [FO.CarrierRel.get, carrierRel]
  rw [subsetRepresentation_datatype wf productive priorRel.base carrier data]
  change BaseLift.data data rfl (.ctor ctorRef (args.encode priorRel.base)) =
    BaseLift.data data rfl
      (((carrier data).to
        ((carrier data).«from» (.ctor ctorRef args))).encode priorRel.base)
  rw [(carrier data).right_inv]
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
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (field : FieldDecl arity)
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
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
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
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (field : FieldDecl arity)
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
          rw [subsetRepresentation_external wf productive priorRel.base carrier sort fresh]
          rfl
      | data child =>
          simp only [FieldDecl.fo, FieldSort.fo, putField,
            FO.CarrierRel.get, carrierRel]
          change
            (subsetRepresentation wf productive priorRel.base carrier
              (DataRef.decl (block := block) child).sort).guard
                (.data child rfl value) ↔ _
          rw [subsetRepresentation_datatype wf productive priorRel.base carrier child]
          rfl

/-- Decoding an embedded target field agrees with structural field decoding
followed by conversion back to the source carrier. -/
theorem decode_putField {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers} (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (field : FieldDecl arity)
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
          simp [subsetRepresentation_external wf productive priorRel.base carrier base fresh,
            externalRepresentation, sourceField, FieldDecl.decode]
      | data child =>
          simp only [FieldDecl.fo, FieldSort.fo, putField,
            FO.CarrierRel.get, carrierRel]
          change
            (subsetRepresentation wf productive priorRel.base carrier
              (DataRef.decl (block := block) child).sort).decode
                (.data child rfl value) _ = _
          simp [
            subsetRepresentation_datatype wf productive priorRel.base carrier child,
            datatypeRepresentation, sourceField, FieldDecl.decode]
          congr

/-- Full target interpretation of one native selector. On guarded values it
preserves the source model's (possibly arbitrary) interpretation. On values
outside the guarded image it uses the free-algebra selector, which is the
behavior required by the native datatype declaration on matching constructors. -/
noncomputable def targetSel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    {source prior : FO.Carriers} (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (sourceSel : source.Base data.decl.sort →
      (field.fo block).Denote source) :
    FO.SymbolDenote (carriers productive prior)
      [(.base data.decl.sort)] (field.fo block) := by
  classical
  exact fun value =>
    let relation := carrierRel wf productive priorRel carrier
    if guarded : (relation (.base data.decl.sort)).guard value then
      (relation (field.fo block)).encode
        (sourceSel ((relation (.base data.decl.sort)).decode value guarded))
    else
      putField wf productive prior ctorRef field fieldRef
        (sel ctorRef fieldRef (fieldDefault productive prior field)
          (asData wf data value))

/-- The guarded target selector agrees with the source selector on every
encoded source value, including its unspecified behavior on nonmatching
constructors. -/
theorem sel_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (sourceSel : source.Base data.decl.sort →
      (field.fo block).Denote source) :
    FO.SymbolRel (arguments := [.base data.decl.sort])
      (result := field.fo block)
      (carrierRel wf productive priorRel carrier)
      sourceSel
      (targetSel wf productive priorRel carrier ctorRef fieldRef sourceSel) := by
  intro value
  simp only [targetSel]
  have guarded := ((carrierRel wf productive priorRel carrier)
    (.base data.decl.sort)).encode_guard value
  rw [dif_pos guarded]
  rw [((carrierRel wf productive priorRel carrier)
    (.base data.decl.sort)).decode_encode value]
  rfl

/-- On its own constructor, the guarded target selector satisfies the native
free-datatype selector equation, whether or not the constructor payload is in
the source image. -/
theorem targetSel_ctor {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (sourceSel : source.Base data.decl.sort →
      (field.fo block).Denote source)
    (matching : ∀ args : Args block source.Base ctor.fields,
      sourceSel ((carrier data).«from» (.ctor ctorRef args)) =
        sourceField carrier field (args.get fieldRef))
    (args : Args block prior.Base ctor.fields) :
    targetSel wf productive priorRel carrier ctorRef fieldRef sourceSel
        (.data data rfl (.ctor ctorRef args)) =
      putField wf productive prior ctorRef field fieldRef
        (args.get fieldRef) := by
  classical
  let relation := carrierRel wf productive priorRel carrier
  unfold targetSel
  dsimp only
  by_cases guarded :
      (relation (.base data.decl.sort)).guard
        (.data data rfl (.ctor ctorRef args))
  · rw [dif_pos guarded]
    have wellFormed :
        args.WF (fun sort => (priorRel.base sort).guard) := by
      change
        (subsetRepresentation wf productive priorRel.base carrier data.decl.sort).guard
          (.data data rfl (.ctor ctorRef args)) at guarded
      rw [subsetRepresentation_datatype wf productive priorRel.base carrier data] at guarded
      exact guarded
    let decodedArgs := args.decode priorRel.base wellFormed
    have decoded :
        (relation (.base data.decl.sort)).decode
            (.data data rfl (.ctor ctorRef args)) guarded =
          (carrier data).«from» (.ctor ctorRef decodedArgs) := by
      change
        (subsetRepresentation wf productive priorRel.base carrier data.decl.sort).decode
            (.data data rfl (.ctor ctorRef args)) guarded = _
      simp [subsetRepresentation_datatype wf productive priorRel.base carrier data,
        datatypeRepresentation, decodedArgs]
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
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    FO.SymbolDenote (carriers productive prior)
      [(.base data.decl.sort)] .bool :=
  fun value => IsCtor ctorRef (asData wf data value)

/-- A native tester preserves the source tester on encoded datatype values. -/
theorem test_rel {arity : Nat} {block : Block arity}
    (wf : block.WF) (productive : Productive block)
    (source prior : FO.Carriers)
    (priorRel : FO.CarrierRel source prior)
    (carrier : ∀ owner : DataRef block,
      Iso (source.Base owner.decl.sort) (Val block source.Base owner))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    (sourceTest : source.Base data.decl.sort → Prop)
    (meaning : ∀ value, sourceTest value ↔
      IsCtor ctorRef ((carrier data).to value)) :
    FO.SymbolRel (arguments := [.base data.decl.sort]) (result := .bool)
      (carrierRel wf productive priorRel carrier)
      sourceTest (targetTest wf productive prior ctorRef) := by
  intro value
  apply propext
  have encoded :
      ((carrierRel wf productive priorRel carrier)
        (.base data.decl.sort)).encode value =
      .data data rfl (((carrier data).to value).encode priorRel.base) := by
    change
      (subsetRepresentation wf productive priorRel.base carrier data.decl.sort).encode value = _
    rw [subsetRepresentation_datatype wf productive priorRel.base carrier data]
    rfl
  change IsCtor ctorRef
      (asData wf data
        (((carrierRel wf productive priorRel carrier)
          (.base data.decl.sort)).encode value)) ↔ sourceTest value
  rw [encoded, asData_data, meaning]
  exact Val.isCtor_encode_iff priorRel.base ctorRef ((carrier data).to value)

end BaseLift

end Crush.Metatheory.Datatype
