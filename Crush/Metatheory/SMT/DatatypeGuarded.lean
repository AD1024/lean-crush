import Crush.Metatheory.Datatype.Flattened
import Crush.Metatheory.SMT.DatatypeRepresentation
import Crush.Metatheory.SMT.GuardedSoundness

/-!
# Guarded native datatype bodies

This file assembles the exact tester/selector syntax of a native datatype
well-formedness body from typed flattened symbols. The generic guard evaluator
then proves its semantic tester-implies-field meaning.
-/

namespace Crush.Metatheory.SMT.Datatype

open Crush.Metatheory.Datatype
open Crush.Metatheory.Defunctionalization.Flattened

variable {signature : Signature} {arity : Nat} {block : Block arity}
variable {native : NativeSymbols (Symbol signature) block}

/-- Typed selector applications belonging to one constructor, in field order. -/
def fieldInputs {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    List (SMT.GuardInput guarding target extra environment) :=
  (Ref.all ctor.fields).map fun found =>
    SMT.GuardInput.ofUnary (native.sel ctorRef found.ref)
      valueTerm value valueEval

/-- Quantifying over the emitted selector inputs is exactly quantifying over
the constructor's typed fields. -/
theorem fieldInputs_iff {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    (∀ input ∈ fieldInputs (native := native) ctorRef valueTerm value valueEval,
        guard input.sort input.value) ↔
      ∀ field (fieldRef : FieldRef ctor field),
        guard (field.fo block)
          (target.symbol (native.sel ctorRef fieldRef) value) := by
  constructor
  · intro every field fieldRef
    have member : GuardInput.ofUnary (native.sel ctorRef fieldRef)
          valueTerm value valueEval ∈
        fieldInputs (native := native) ctorRef valueTerm value valueEval := by
      simp only [fieldInputs, List.mem_map]
      exact ⟨⟨field, fieldRef⟩, Ref.mem_all fieldRef, rfl⟩
    exact every _ member
  · intro every input member
    simp only [fieldInputs, List.mem_map] at member
    rcases member with ⟨found, _, rfl⟩
    exact every found.value found.ref

/-- One constructor clause with its indexed tester and typed selector inputs. -/
def ctorPart {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (ctorName : String)
    (testIdent : guarding.encoding.ident (native.test ctorRef) =
      .indexed "is" #[.inl ctorName])
    (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    SMT.GuardPart guarding target extra environment valueTerm where
  name := ctorName
  tester := target.symbol (native.test ctorRef) value
  testerEval := by
    have evaluated := (SMT.GuardInput.ofUnary (native.test ctorRef)
      valueTerm value valueEval).evaluated
    change Crush.SMT.Eval (SMT.modelWith guarding.encoding target extra) environment
      (.app (guarding.encoding.ident (native.test ctorRef)) #[valueTerm])
      (SMT.Value.typed .bool (target.symbol (native.test ctorRef) value)) at evaluated
    rw [testIdent] at evaluated
    exact evaluated
  fields := fieldInputs (native := native) ctorRef valueTerm value valueEval

/-- Every constructor clause of one datatype declaration, in declaration order. -/
def dataParts {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    (data : DataRef block)
    (ctorName : ∀ {ctor : CtorDecl arity},
      CtorRef block data ctor → String)
    (testIdent : ∀ {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor),
      guarding.encoding.ident (native.test ref) =
        .indexed "is" #[.inl (ctorName ref)])
    (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    List (SMT.GuardPart guarding target extra environment valueTerm) :=
  (Ref.all data.decl.ctors).map fun found =>
    ctorPart (native := native) found.ref (ctorName found.ref) (testIdent found.ref)
      valueTerm value valueEval

/-- Exact guard terms for the fields of one constructor, without semantic
evidence. This is the proof-facing form of production's inner `wfParts`. -/
def wfFields (guarding : SMT.Guarding (Symbol signature))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (valueTerm : Crush.SMT.Term) :
    Array Crush.SMT.Term :=
  (Ref.all ctor.fields).filterMap (fun found =>
    guarding.guard (found.value.fo block)
      (.app (guarding.encoding.ident (native.sel ctorRef found.ref))
        #[valueTerm])) |>.toArray

/-- Exact constructor names and selector guards used by one generated `wf_T`
body. Unlike `dataParts`, this syntax has no model-dependent evidence. -/
def wfParts (guarding : SMT.Guarding (Symbol signature))
    (data : DataRef block)
    (ctorName : ∀ {ctor : CtorDecl arity},
      CtorRef block data ctor → String)
    (valueTerm : Crush.SMT.Term := .bvar 0) :
    Array (String × Array Crush.SMT.Term) :=
  (Ref.all data.decl.ctors).map (fun found =>
    (ctorName found.ref,
      wfFields (native := native) guarding found.ref valueTerm)) |>.toArray

/-- One simultaneous recursive-definition array for every member of a mutual
datatype block, in declaration order. -/
def wfDefs (guarding : SMT.Guarding (Symbol signature))
    (encoding : BlockEncoding arity) (guardName binder : DataRef block → String) :
    Array Crush.SMT.FunDef :=
  ((List.finRange arity).map fun data : DataRef block =>
    wfDef (guardName data) (binder data)
      (guarding.encoding.sort (.base data.decl.sort))
      (wfParts (native := native) guarding data
        (fun ref => encoding.name (.ctor data ref.index)))).toArray

/-- Erasing semantic evidence from typed constructor clauses recovers the pure
`wf_T` syntax exactly. -/
theorem dataParts_parts {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    (data : DataRef block)
    (ctorName : ∀ {ctor : CtorDecl arity},
      CtorRef block data ctor → String)
    (testIdent : ∀ {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor),
      guarding.encoding.ident (native.test ref) =
        .indexed "is" #[.inl (ctorName ref)])
    (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    SMT.GuardPart.parts
        (dataParts data ctorName testIdent valueTerm value valueEval) =
      wfParts (native := native) guarding data ctorName valueTerm := by
  simp [SMT.GuardPart.parts, dataParts, ctorPart, fieldInputs, wfParts,
    wfFields, SMT.GuardInput.terms, SMT.GuardInput.ofUnary,
    List.filterMap_map, Function.comp_def]
  intros
  rfl

/-- The generated clause contract is exactly the typed tester/selector
condition for every constructor and every field. -/
theorem dataParts_iff {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (data : DataRef block)
    (ctorName : ∀ {ctor : CtorDecl arity},
      CtorRef block data ctor → String)
    (testIdent : ∀ {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor),
      guarding.encoding.ident (native.test ref) =
        .indexed "is" #[.inl (ctorName ref)])
    (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    SMT.GuardPart.Holds guard
        (dataParts data ctorName testIdent valueTerm value valueEval) ↔
      ∀ ctor (ctorRef : CtorRef block data ctor),
        target.symbol (native.test ctorRef) value →
          ∀ field (fieldRef : FieldRef ctor field),
            guard (field.fo block)
              (target.symbol (native.sel ctorRef fieldRef) value) := by
  constructor
  · intro every ctor ctorRef tested
    have member : ctorPart (native := native) ctorRef (ctorName ctorRef)
          (testIdent ctorRef) valueTerm value valueEval ∈
        dataParts data ctorName testIdent valueTerm value valueEval := by
      simp only [dataParts, List.mem_map]
      exact ⟨⟨ctor, ctorRef⟩, Ref.mem_all ctorRef, rfl⟩
    have fields := every _ member
    have held : ∀ input ∈
        fieldInputs (native := native) ctorRef valueTerm value valueEval,
          guard input.sort input.value := by
      exact fields (by simpa [ctorPart] using tested)
    exact (fieldInputs_iff (guard := guard) (native := native)
      ctorRef valueTerm value valueEval).mp held
  · intro every part member tested
    simp only [dataParts, List.mem_map] at member
    rcases member with ⟨found, _, rfl⟩
    have held := (fieldInputs_iff (guard := guard) (native := native)
      found.ref valueTerm value valueEval).mpr
        (every found.value found.ref (by simpa [ctorPart] using tested))
    simpa [ctorPart] using held

/-- On a value accepted by a native tester, the corresponding target selector
is guarded exactly when the selected free-datatype field is well formed. -/
theorem targetSel_guard
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful native source) (exclusive : native.Exclusive)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (value : (law.extend wf productive prior priorRel priorModels).carriers.Base
      data.decl.sort)
    (tested : (law.extend wf productive prior priorRel priorModels).symbol
      (native.test ctorRef) value)
    (fallback : field.Denote block prior.carriers.Base) :
    ((BaseLift.carrierRel wf productive priorRel law.carrier)
        (field.fo block)).guard
        ((law.extend wf productive prior priorRel priorModels).symbol
          (native.sel ctorRef fieldRef) value) ↔
      field.WF (fun sort => (priorRel.base sort).guard)
        (sel ctorRef fieldRef fallback (BaseLift.asData wf data value)) := by
  rw [law.extend_test exclusive wf productive prior priorRel priorModels ctorRef] at tested
  change IsCtor ctorRef (BaseLift.asData wf data value) at tested
  rcases tested with ⟨args, equal⟩
  have valueEq : value = .data data rfl (.ctor ctorRef args) := by
    rw [← BaseLift.data_asData wf data value, ← equal]
  rw [valueEq, law.extend_sel exclusive wf productive prior priorRel priorModels]
  rw [BaseLift.targetSel_ctor wf productive source.carriers prior.carriers
    priorRel law.carrier ctorRef fieldRef _ (law.sel_ctor ctorRef fieldRef) args]
  rw [BaseLift.putField_guard, BaseLift.asData_data, sel_ctor]

/-- In the canonical lifted native model, the generated tester/selector
contract is precisely the intrinsic selector-form datatype guard. -/
theorem parts_iff_selWF
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful native source) (exclusive : native.Exclusive)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding
      (law.extend wf productive prior priorRel priorModels)}
    {environment : List
      (SMT.Value (law.extend wf productive prior priorRel priorModels))}
    (data : DataRef block)
    (ctorName : ∀ {ctor : CtorDecl arity},
      CtorRef block data ctor → String)
    (testIdent : ∀ {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor),
      guarding.encoding.ident (native.test ref) =
        .indexed "is" #[.inl (ctorName ref)])
    (valueTerm : Crush.SMT.Term)
    (value : (law.extend wf productive prior priorRel priorModels).carriers.Base
      data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding
        (law.extend wf productive prior priorRel priorModels) extra)
      environment valueTerm (.typed (.base data.decl.sort) value)) :
    SMT.GuardPart.Holds
        (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
          sort).guard)
        (dataParts data ctorName testIdent valueTerm value valueEval) ↔
      (BaseLift.asData wf data value).SelWF
        (fun sort => (priorRel.base sort).guard) := by
  rw [dataParts_iff]
  constructor
  · intro every ctor ctorRef field fieldRef fallback tested
    have targetTest : (law.extend wf productive prior priorRel priorModels).symbol
        (native.test ctorRef) value := by
      rw [law.extend_test exclusive wf productive prior priorRel priorModels]
      exact tested
    exact (targetSel_guard law exclusive wf productive priorRel priorModels ctorRef
      fieldRef value targetTest fallback).mp
        (every ctor ctorRef targetTest field fieldRef)
  · intro every ctor ctorRef tested field fieldRef
    let fallback := field.fallback priorRel.base productive
    have coreTest : IsCtor ctorRef (BaseLift.asData wf data value) := by
      rw [law.extend_test exclusive wf productive prior priorRel priorModels] at tested
      exact tested
    exact (targetSel_guard law exclusive wf productive priorRel priorModels ctorRef
      fieldRef value tested fallback).mpr
        (every ctor ctorRef field fieldRef fallback coreTest)

/-- The exact generated body denotes the carrier guard of the lifted datatype
sort. This closes the semantic gap between production's `wf_T` syntax and the
single relation used by guarded term preservation. -/
theorem dataParts_eval_wf
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful native source) (exclusive : native.Exclusive)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding
      (law.extend wf productive prior priorRel priorModels)}
    {environment : List
      (SMT.Value (law.extend wf productive prior priorRel priorModels))}
    (semantics : guarding.TermSemantics
      (law.extend wf productive prior priorRel priorModels) extra
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard))
    (data : DataRef block)
    (ctorName : ∀ {ctor : CtorDecl arity},
      CtorRef block data ctor → String)
    (testIdent : ∀ {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor),
      guarding.encoding.ident (native.test ref) =
        .indexed "is" #[.inl (ctorName ref)])
    (valueTerm : Crush.SMT.Term)
    (value : (law.extend wf productive prior priorRel priorModels).carriers.Base
      data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding
        (law.extend wf productive prior priorRel priorModels) extra)
      environment valueTerm (.typed (.base data.decl.sort) value)) :
    Crush.SMT.Eval
      (SMT.modelWith guarding.encoding
        (law.extend wf productive prior priorRel priorModels) extra)
      environment
      (wfBody (SMT.GuardPart.parts
        (dataParts data ctorName testIdent valueTerm value valueEval)) valueTerm)
      (.typed .bool ((BaseLift.carrierRel wf productive priorRel law.carrier
        (.base data.decl.sort)).guard value)) := by
  have evaluated := SMT.GuardPart.eval semantics
    (dataParts data ctorName testIdent valueTerm value valueEval)
  have clauses := parts_iff_selWF law exclusive wf productive priorRel priorModels data
    ctorName testIdent valueTerm value valueEval
  have structural := Val.wf_iff_selWF priorRel.base productive
    (BaseLift.asData wf data value)
  have nativeGuard :
      (BaseLift.carrierRel wf productive priorRel law.carrier
          (.base data.decl.sort)).guard value ↔
        (BaseLift.asData wf data value).WF
          (fun sort => (priorRel.base sort).guard) := by
    change (BaseLift.rel wf productive priorRel.base law.carrier
      data.decl.sort).guard value ↔ _
    rw [BaseLift.rel_data]
    rfl
  have equal : SMT.GuardPart.Holds
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard)
      (dataParts data ctorName testIdent valueTerm value valueEval) =
      (BaseLift.carrierRel wf productive priorRel law.carrier
        (.base data.decl.sort)).guard value :=
    propext (clauses.trans (structural.symm.trans nativeGuard.symm))
  rw [equal] at evaluated
  exact evaluated

/-- Pure production-shaped parts have the same carrier-guard denotation as
their evidence-carrying clause form. -/
theorem wfParts_eval_wf
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful native source) (exclusive : native.Exclusive)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding
      (law.extend wf productive prior priorRel priorModels)}
    {environment : List
      (SMT.Value (law.extend wf productive prior priorRel priorModels))}
    (semantics : guarding.TermSemantics
      (law.extend wf productive prior priorRel priorModels) extra
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard))
    (data : DataRef block)
    (ctorName : ∀ {ctor : CtorDecl arity},
      CtorRef block data ctor → String)
    (testIdent : ∀ {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor),
      guarding.encoding.ident (native.test ref) =
        .indexed "is" #[.inl (ctorName ref)])
    (valueTerm : Crush.SMT.Term)
    (value : (law.extend wf productive prior priorRel priorModels).carriers.Base
      data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding
        (law.extend wf productive prior priorRel priorModels) extra)
      environment valueTerm (.typed (.base data.decl.sort) value)) :
    Crush.SMT.Eval
      (SMT.modelWith guarding.encoding
        (law.extend wf productive prior priorRel priorModels) extra)
      environment (wfBody
        (wfParts (native := native) guarding data ctorName valueTerm) valueTerm)
      (.typed .bool ((BaseLift.carrierRel wf productive priorRel law.carrier
        (.base data.decl.sort)).guard value)) := by
  rw [← dataParts_parts data ctorName testIdent valueTerm value valueEval]
  exact dataParts_eval_wf law exclusive wf productive priorRel priorModels semantics data
    ctorName testIdent valueTerm value valueEval

/-- The exact body assembled from typed native symbols evaluates to its
tester-implies-field contract. -/
theorem dataParts_eval {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard)
    (data : DataRef block)
    (ctorName : ∀ {ctor : CtorDecl arity},
      CtorRef block data ctor → String)
    (testIdent : ∀ {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor),
      guarding.encoding.ident (native.test ref) =
        .indexed "is" #[.inl (ctorName ref)])
    (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    Crush.SMT.Eval (SMT.modelWith guarding.encoding target extra) environment
      (wfBody (SMT.GuardPart.parts
        (dataParts data ctorName testIdent valueTerm value valueEval)) valueTerm)
      (.typed .bool (SMT.GuardPart.Holds guard
        (dataParts data ctorName testIdent valueTerm value valueEval))) :=
  SMT.GuardPart.eval semantics _

/-- The flattened native tester uses the indexed identifier fixed by the exact
datatype representation. -/
theorem Representation.native_test_ident
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) :
    fo.ident (symbols.native.test ref) =
      .indexed "is" #[.inl (encoding.name (.ctor data ref.index))] := by
  exact represented.test_ident ref

/-- Exact represented constructor clauses for one datatype member. -/
def Representation.guardParts
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    (encodingEq : guarding.encoding = fo)
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    (data : DataRef block) (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    List (SMT.GuardPart guarding target extra environment valueTerm) := by
  subst fo
  exact dataParts (native := symbols.native) data
    (fun ref => encoding.name (.ctor data ref.index))
    (fun ref => represented.native_test_ident ref)
    valueTerm value valueEval

/-- Semantic fixed-point equation characterized by one block's tester and
selector symbols. It is independent of raw syntax and is therefore the compact
invariant transported through later dependency blocks. -/
def Representation.GuardLaw
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (_represented : Representation block symbols fo encoding)
    (target : FO.FamilyModel (Symbol signature))
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop) : Prop :=
  ∀ (data : DataRef block) (value : target.carriers.Base data.decl.sort),
    (∀ ctor (ctorRef : CtorRef block data ctor),
      target.symbol (symbols.native.test ctorRef) value →
        ∀ field (fieldRef : FieldRef ctor field),
          guard (field.fo block)
            (target.symbol (symbols.native.sel ctorRef fieldRef) value)) ↔
      guard (.base data.decl.sort) value

/-- Pointwise-equivalent predicates satisfy the same datatype guard equation. -/
theorem Representation.GuardLaw.congr
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    {represented : Representation block symbols fo encoding}
    {target : FO.FamilyModel (Symbol signature)}
    {left right : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (law : represented.GuardLaw target left)
    (same : ∀ sort value, left sort value ↔ right sort value) :
    represented.GuardLaw target right := by
  intro data value
  constructor
  · intro every
    apply (same (.base data.decl.sort) value).mp
    apply (law data value).mp
    intro ctor ctorRef tested field fieldRef
    exact (same (field.fo block)
      (target.symbol (symbols.native.sel ctorRef fieldRef) value)).mpr
        (every ctor ctorRef tested field fieldRef)
  · intro guarded
    have old := (law data value).mpr
      ((same (.base data.decl.sort) value).mpr guarded)
    intro ctor ctorRef tested field fieldRef
    exact (same (field.fo block)
      (target.symbol (symbols.native.sel ctorRef fieldRef) value)).mp
        (old ctor ctorRef tested field fieldRef)

/-- The canonical extension satisfies its datatype guard equation. This is
derived from the free-datatype tester and selector laws, rather than supplied
as an assumption to the final soundness theorem. -/
theorem Representation.guardLaw_extend
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful symbols.native source)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel) :
    represented.GuardLaw
      (law.extend wf productive prior priorRel priorModels)
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard) := by
  intro data value
  have selectors :
      (∀ ctor (ctorRef : CtorRef block data ctor),
          (law.extend wf productive prior priorRel priorModels).symbol
              (symbols.native.test ctorRef) value →
            ∀ field (fieldRef : FieldRef ctor field),
              (BaseLift.carrierRel wf productive priorRel law.carrier
                (field.fo block)).guard
                ((law.extend wf productive prior priorRel priorModels).symbol
                  (symbols.native.sel ctorRef fieldRef) value)) ↔
        (BaseLift.asData wf data value).SelWF
          (fun sort => (priorRel.base sort).guard) := by
    constructor
    · intro every ctor ctorRef field fieldRef fallback tested
      have targetTest :
          (law.extend wf productive prior priorRel priorModels).symbol
            (symbols.native.test ctorRef) value := by
        rw [law.extend_test represented.exclusive wf productive prior priorRel
          priorModels]
        exact tested
      exact (targetSel_guard law represented.exclusive wf productive priorRel
        priorModels ctorRef fieldRef value targetTest fallback).mp
          (every ctor ctorRef targetTest field fieldRef)
    · intro every ctor ctorRef tested field fieldRef
      let fallback := field.fallback priorRel.base productive
      have coreTest : IsCtor ctorRef (BaseLift.asData wf data value) := by
        rw [law.extend_test represented.exclusive wf productive prior priorRel
          priorModels] at tested
        exact tested
      exact (targetSel_guard law represented.exclusive wf productive priorRel
        priorModels ctorRef fieldRef value tested fallback).mpr
          (every ctor ctorRef field fieldRef fallback coreTest)
  have structural := Val.wf_iff_selWF priorRel.base productive
    (BaseLift.asData wf data value)
  have nativeGuard :
      (BaseLift.carrierRel wf productive priorRel law.carrier
          (.base data.decl.sort)).guard value ↔
        (BaseLift.asData wf data value).WF
          (fun sort => (priorRel.base sort).guard) := by
    change (BaseLift.rel wf productive priorRel.base law.carrier
      data.decl.sort).guard value ↔ _
    rw [BaseLift.rel_data]
    rfl
  exact selectors.trans (structural.symm.trans nativeGuard.symm)

/-- A `GuardLaw` is exactly the denotation of the evidence-carrying clause list
used to build the raw `wf_T` body. -/
theorem Representation.guardParts_iff_guard
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    (encodingEq : guarding.encoding = fo)
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (law : represented.GuardLaw target guard)
    (data : DataRef block) (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    SMT.GuardPart.Holds guard
        (represented.guardParts encodingEq data valueTerm value valueEval) ↔
      guard (.base data.decl.sort) value := by
  subst fo
  exact (dataParts_iff (native := symbols.native) data
    (fun ref => encoding.name (.ctor data ref.index))
    (fun ref => represented.native_test_ident ref)
    valueTerm value valueEval).trans (law data value)

/-- The represented clause body has the generic tester-implies-field
denotation. -/
theorem Representation.guardParts_eval
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {target : FO.FamilyModel (Symbol signature)}
    {guarding : SMT.Guarding (Symbol signature)}
    (encodingEq : guarding.encoding = fo)
    {extra : SMT.ExtraGraph guarding.encoding target}
    {environment : List (SMT.Value target)}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard)
    (data : DataRef block) (valueTerm : Crush.SMT.Term)
    (value : target.carriers.Base data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith guarding.encoding target extra) environment valueTerm
      (.typed (.base data.decl.sort) value)) :
    Crush.SMT.Eval (SMT.modelWith guarding.encoding target extra) environment
      (wfBody (SMT.GuardPart.parts
        (represented.guardParts encodingEq data valueTerm value valueEval)) valueTerm)
      (.typed .bool (SMT.GuardPart.Holds guard
        (represented.guardParts encodingEq data valueTerm value valueEval))) := by
  subst fo
  exact dataParts_eval semantics data
    (fun ref => encoding.name (.ctor data ref.index))
    (fun ref => represented.native_test_ident ref)
    valueTerm value valueEval

/-- For the canonical lifted native model, the exact represented body evaluates
to the owned datatype sort's shared carrier guard. -/
theorem Representation.guardParts_eval_wf
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful symbols.native source)
    (exclusive : symbols.native.Exclusive)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (guards : SMT.UnaryGuards fo
      (law.extend wf productive prior priorRel priorModels)
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard))
    (omitted : ∀ sort, guards.ident sort = none → ∀ value,
      (BaseLift.carrierRel wf productive priorRel law.carrier sort).guard value)
    {environment : List
      (SMT.Value (law.extend wf productive prior priorRel priorModels))}
    (data : DataRef block) (valueTerm : Crush.SMT.Term)
    (value : (law.extend wf productive prior priorRel priorModels).carriers.Base
      data.decl.sort)
    (valueEval : Crush.SMT.Eval
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels) guards.extra)
      environment valueTerm (.typed (.base data.decl.sort) value)) :
    Crush.SMT.Eval
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels) guards.extra)
      environment
      (wfBody (SMT.GuardPart.parts
        (represented.guardParts (guarding := guards.guarding)
          (extra := guards.extra) rfl data valueTerm value valueEval)) valueTerm)
      (.typed .bool ((BaseLift.carrierRel wf productive priorRel law.carrier
        (.base data.decl.sort)).guard value)) := by
  change Crush.SMT.Eval
    (SMT.modelWith guards.guarding.encoding
      (law.extend wf productive prior priorRel priorModels) guards.extra)
    environment _ _
  simpa [Representation.guardParts] using
    (dataParts_eval_wf law exclusive wf productive priorRel priorModels
      (guards.termSemantics omitted) data
      (fun ref => encoding.name (.ctor data ref.index))
      (fun ref => represented.native_test_ident ref)
      valueTerm value valueEval)

/-- One exact production-shaped `wf_T` definition satisfies its simultaneous
graph equation in the guarded native model. -/
theorem wfDef_valid
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful symbols.native source)
    (exclusive : symbols.native.Exclusive)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {guarding : SMT.Guarding (Symbol signature)}
    {extra : SMT.ExtraGraph fo
      (law.extend wf productive prior priorRel priorModels)}
    (encodingEq : guarding.encoding = fo)
    (semantics : guarding.TermSemantics
      (law.extend wf productive prior priorRel priorModels)
      (encodingEq ▸ extra)
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard))
    (functional : Crush.SMT.ApplyUnique
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels) extra))
    (data : DataRef block) (name binder : String)
    (hasType : Crush.SMT.SymbolHasType
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels) extra)
      (.symb name) [fo.sort (.base data.decl.sort)] (fo.sort .bool))
    (applies : ∀ value output,
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels) extra).apply
          (.symb name) [.typed (.base data.decl.sort) value] output ↔
        output = .typed .bool
          ((BaseLift.carrierRel wf productive priorRel law.carrier
            (.base data.decl.sort)).guard value)) :
    (wfDef name binder (fo.sort (.base data.decl.sort))
      (wfParts (native := symbols.native) guarding data
        (fun ref => encoding.name (.ctor data ref.index)))).Holds
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels)
        extra) := by
  subst fo
  apply SMT.wfDef_holds_core extra functional hasType applies
  intro value
  change Crush.SMT.Eval
    (SMT.modelWith guarding.encoding
      (law.extend wf productive prior priorRel priorModels) extra) _ _ _
  exact wfParts_eval_wf law exclusive wf productive priorRel priorModels
    semantics data
    (fun ref => encoding.name (.ctor data ref.index))
    (fun ref => represented.native_test_ident ref)
    (.bvar 0) value (Crush.SMT.Eval.bvar rfl)

/-- Validate the exact mutual `wf_T` command in an arbitrary target model once
the represented tester/selector clauses characterize the chosen guard. This is
the suffix-stable interface; the canonical one-step theorem below discharges
`correct` from free-datatype semantics. -/
theorem wfDefs_valid_of_guard
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {target : FO.FamilyModel (Symbol signature)}
    (guarding : SMT.Guarding (Symbol signature))
    (encodingEq : guarding.encoding = fo)
    (extra : SMT.ExtraGraph guarding.encoding target)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    (semantics : guarding.TermSemantics target extra guard)
    (functional : Crush.SMT.ApplyUnique
      (SMT.modelWith guarding.encoding target extra))
    (guardName binder : DataRef block → String)
    (nameInj : Function.Injective guardName)
    (notBuiltin : ∀ data, Crush.SMT.NotBuiltin (.symb (guardName data)))
    (hasType : ∀ data, Crush.SMT.SymbolHasType
      (SMT.modelWith guarding.encoding target extra) (.symb (guardName data))
      [guarding.encoding.sort (.base data.decl.sort)]
      (guarding.encoding.sort .bool))
    (applies : ∀ data value output,
      (SMT.modelWith guarding.encoding target extra).apply
          (.symb (guardName data))
          [.typed (.base data.decl.sort) value] output ↔
        output = .typed .bool (guard (.base data.decl.sort) value))
    (correct : represented.GuardLaw target guard) :
    (SMT.modelWith guarding.encoding target extra).SatisfiesCommand
      (.defFunsRec (wfDefs (native := symbols.native) guarding
        encoding guardName binder)) := by
  subst fo
  let definitions := wfDefs (native := symbols.native) guarding
    encoding guardName binder
  change Crush.SMT.FunsRecSupported definitions ∧
    Crush.SMT.FunsRecHold (SMT.modelWith guarding.encoding target extra)
      definitions
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro empty
      dsimp [definitions, wfDefs] at empty
      have zero : arity = 0 := by
        simpa using congrArg List.length empty
      exact (Nat.ne_of_gt represented.wf.blockWF.nonempty) zero
    · dsimp [definitions, wfDefs]
      simp only [List.map_map, Function.comp_def, wfDef]
      exact nodup_map (finRange_nodup arity) nameInj
    · intro definition member
      dsimp [definitions, wfDefs] at member
      rw [List.mem_map] at member
      rcases member with ⟨data, _, rfl⟩
      exact notBuiltin data
  · intro definition member
    dsimp [definitions, wfDefs] at member
    rw [List.mem_map] at member
    rcases member with ⟨data, _, rfl⟩
    apply SMT.wfDef_holds_core extra functional (hasType data) (applies data)
    intro value
    let valueEval : Crush.SMT.Eval (SMT.modelWith guarding.encoding target extra)
        [.typed (.base data.decl.sort) value] (.bvar 0)
        (.typed (.base data.decl.sort) value) := .bvar rfl
    have evaluated := represented.guardParts_eval rfl semantics data (.bvar 0)
      value valueEval
    have equal := propext (represented.guardParts_iff_guard rfl correct data
      (.bvar 0) value valueEval)
    rw [equal] at evaluated
    have partsEq := dataParts_parts (native := symbols.native) data
      (fun ref => encoding.name (.ctor data ref.index))
      (fun ref => represented.native_test_ident ref)
      (.bvar 0) value valueEval
    simpa [Representation.guardParts, partsEq] using evaluated

/-- The complete mutual `define-funs-rec` command for one represented block is
valid in the same guarded model as its native datatype declaration. -/
theorem wfDefs_valid
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {encoding : BlockEncoding arity}
    (represented : Representation block symbols fo encoding)
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful symbols.native source)
    (exclusive : symbols.native.Exclusive)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (guarding : SMT.Guarding (Symbol signature))
    (encodingEq : guarding.encoding = fo)
    (extra : SMT.ExtraGraph fo
      (law.extend wf productive prior priorRel priorModels))
    (semantics : guarding.TermSemantics
      (law.extend wf productive prior priorRel priorModels)
      (encodingEq ▸ extra)
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard))
    (functional : Crush.SMT.ApplyUnique
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels) extra))
    (guardName binder : DataRef block → String)
    (nameInj : Function.Injective guardName)
    (notBuiltin : ∀ data, Crush.SMT.NotBuiltin (.symb (guardName data)))
    (hasType : ∀ data, Crush.SMT.SymbolHasType
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels) extra)
      (.symb (guardName data)) [fo.sort (.base data.decl.sort)] (fo.sort .bool))
    (applies : ∀ data value output,
      (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels) extra).apply
          (.symb (guardName data))
          [.typed (.base data.decl.sort) value] output ↔
        output = .typed .bool
          ((BaseLift.carrierRel wf productive priorRel law.carrier
            (.base data.decl.sort)).guard value)) :
    (SMT.modelWith fo (law.extend wf productive prior priorRel priorModels)
      extra).SatisfiesCommand
      (.defFunsRec (wfDefs (native := symbols.native) guarding
        encoding guardName binder)) := by
  subst fo
  let definitions := wfDefs (native := symbols.native) guarding
    encoding guardName binder
  change Crush.SMT.FunsRecSupported definitions ∧
    Crush.SMT.FunsRecHold
      (SMT.modelWith guarding.encoding
        (law.extend wf productive prior priorRel priorModels) extra)
      definitions
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro empty
      dsimp [definitions, wfDefs] at empty
      have zero : arity = 0 := by
        simpa using congrArg List.length empty
      exact (Nat.ne_of_gt wf.nonempty) zero
    · dsimp [definitions, wfDefs]
      simp only [List.map_map, Function.comp_def, wfDef]
      exact nodup_map (finRange_nodup arity) nameInj
    · intro definition member
      dsimp [definitions, wfDefs] at member
      rw [List.mem_map] at member
      rcases member with ⟨data, _, rfl⟩
      exact notBuiltin data
  · intro definition member
    dsimp [definitions, wfDefs] at member
    rw [List.mem_map] at member
    rcases member with ⟨data, _, rfl⟩
    exact wfDef_valid represented law exclusive wf productive priorRel priorModels
      rfl semantics functional data (guardName data) (binder data)
      (hasType data) (applies data)

end Crush.Metatheory.SMT.Datatype
