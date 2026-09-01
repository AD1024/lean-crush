import Crush.Metatheory.SMT.DatatypeCanonical
import Crush.Metatheory.SMT.DatatypeGuarded

/-!
# SMT datatype declarations in enlarged models

The original canonical command proof interprets a datatype through the source
carrier isomorphism. Guarded lowering instead uses the complete free algebra
over an already-lifted base model. This file proves the same SMT datatype laws
for that target directly; no datatype axioms or source-carrier cast is used.
-/

namespace Crush.Metatheory.SMT.Datatype.Native

open Crush.Metatheory.Datatype
open Crush.Metatheory.Defunctionalization.Flattened
open scoped Crush.Metatheory Crush.SMT

variable {signature : Signature} {arity : Nat} {block : Block arity}
variable {native : DatatypeSymbols (Symbol signature) block}

/-- Constructor payloads embedded in the shared raw universe of the enlarged
free-algebra model. -/
def argValues {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    (fields : List (FieldDecl arity)) →
    (refs : ∀ {field}, Datatype.Ref fields field → FieldRef ctor field) →
    Args block prior.carriers.Base fields →
      List (SMT.Value (law.extend wf productive prior priorRel priorModels))
  | [], _, .nil => []
  | field :: rest, refs, args =>
      match field, args with
      | ⟨name, .base sort⟩, .base value tail =>
          .typed (.base sort)
            (BaseLift.putField wf productive prior.carriers ctorRef
              { name := name, sort := .base sort } (refs .here) value) ::
          argValues law wf productive priorRel priorModels ctorRef rest
            (fun ref => refs (.there ref)) tail
      | ⟨name, .data child⟩, .data value tail =>
          .typed (.base (block.decl child).sort)
            (BaseLift.putField wf productive prior.carriers ctorRef
              { name := name, sort := .data child } (refs .here) value) ::
          argValues law wf productive priorRel priorModels ctorRef rest
            (fun ref => refs (.there ref)) tail

/-- The complete constructor telescope specialization. -/
abbrev ctorArgs {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    (args : Args block prior.carriers.Base ctor.fields) :=
  argValues law wf productive priorRel priorModels ctorRef ctor.fields (fun ref => ref) args

/-- Embedded constructor payloads have exactly their represented field sorts. -/
theorem argValues_typed {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (fo : SMT.Encoding (Symbol signature))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    ∀ (fields : List (FieldDecl arity))
      (refs : ∀ {field}, Datatype.Ref fields field → FieldRef ctor field)
      (args : Args block prior.carriers.Base fields),
      Crush.SMT.ValuesTyped
        (SMT.model fo (law.extend wf productive prior priorRel priorModels))
        (fields.map fun field => fo.sort (field.fo block))
        (argValues law wf productive priorRel priorModels ctorRef fields refs args)
  | [], _, .nil => Crush.SMT.ValuesTyped.nil
  | field :: rest, refs, args => by
      cases field with
      | mk name sort =>
          cases sort with
          | base base =>
              cases args with
              | base value tail =>
                  let embedded : (FO.FOSort.base base).Denote
                      (law.extend wf productive prior priorRel priorModels).carriers := by
                    change BaseLift block prior.carriers.Base base
                    exact BaseLift.putField wf productive prior.carriers ctorRef
                      { name := name, sort := .base base } (refs .here) value
                  exact .cons (Value.inSort_typed (target :=
                    law.extend wf productive prior priorRel priorModels) fo (.base base)
                      embedded)
                    (argValues_typed law wf productive priorRel priorModels fo ctorRef rest
                      (fun ref => refs (.there ref)) tail)
          | data child =>
              cases args with
              | data value tail =>
                  let embedded : (FO.FOSort.base (block.decl child).sort).Denote
                      (law.extend wf productive prior priorRel priorModels).carriers := by
                    change BaseLift block prior.carriers.Base
                      (block.decl child).sort
                    exact BaseLift.putField wf productive prior.carriers ctorRef
                      { name := name, sort := .data child } (refs .here) value
                  exact .cons (Value.inSort_typed (target :=
                    law.extend wf productive prior priorRel priorModels) fo
                      (.base (block.decl child).sort) embedded)
                    (argValues_typed law wf productive priorRel priorModels fo ctorRef rest
                      (fun ref => refs (.there ref)) tail)

/-- Every raw list typed by a constructor telescope in the enlarged model is
the embedding of one typed payload telescope. -/
theorem typed_args {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (fo : SMT.Encoding (Symbol signature))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    ∀ (fields : List (FieldDecl arity))
      (refs : ∀ {field}, Datatype.Ref fields field → FieldRef ctor field)
      {values : List (SMT.Value (law.extend wf productive prior priorRel priorModels))},
      Crush.SMT.ValuesTyped
        (SMT.model fo (law.extend wf productive prior priorRel priorModels))
        (fields.map fun field => fo.sort (field.fo block)) values →
      ∃ args : Args block prior.carriers.Base fields,
        values = argValues law wf productive priorRel priorModels ctorRef fields refs args
  | [], _, values, typed => by
      have equal := typed.eq_nil
      subst values
      exact ⟨.nil, rfl⟩
  | field :: rest, refs, values, typed => by
      obtain ⟨headValue, tailValues, rfl, headTyped, tailTyped⟩ :=
        typed.exists_cons
      cases field with
      | mk name sort =>
          cases sort with
          | base base =>
              obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
                fo (.base base) _ headTyped
              let fresh : ∀ child : DataRef block,
                  child.decl.sort ≠ base := fun child =>
                (wf.base_ne_data ctorRef (refs .here) rfl child).symm
              obtain ⟨tail, tailEq⟩ := typed_args law wf productive priorRel priorModels fo
                ctorRef rest (fun ref => refs (.there ref)) tailTyped
              refine ⟨.base (BaseLift.asExternal base fresh value) tail, ?_⟩
              simp only [argValues, BaseLift.putField]
              rw [tailEq]
              apply congrArg (fun head => head ::
                argValues law wf productive priorRel priorModels ctorRef rest
                  (fun ref => refs (.there ref)) tail)
              exact congrArg (Value.typed (.base base))
                (BaseLift.external_asExternal base fresh value).symm
          | data child =>
              obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
                fo (.base (block.decl child).sort) _ headTyped
              obtain ⟨tail, tailEq⟩ := typed_args law wf productive priorRel priorModels fo
                ctorRef rest (fun ref => refs (.there ref)) tailTyped
              refine ⟨.data (BaseLift.asData wf child value) tail, ?_⟩
              simp only [argValues, BaseLift.putField]
              rw [tailEq]
              apply congrArg (fun head => head ::
                argValues law wf productive priorRel priorModels ctorRef rest
                  (fun ref => refs (.there ref)) tail)
              exact congrArg (Value.typed (.base (block.decl child).sort))
                (BaseLift.data_asData wf child value).symm

/-- Lookup in an embedded argument list recovers the corresponding field. -/
private theorem argValues_get_aux
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    ∀ {fields : List (FieldDecl arity)}
      (refs : ∀ {field}, Datatype.Ref fields field → FieldRef ctor field)
      (args : Args block prior.carriers.Base fields)
      {field : FieldDecl arity} (ref : Datatype.Ref fields field),
    (argValues law wf productive priorRel priorModels ctorRef fields refs args)[ref.index]? =
      some (.typed (field.fo block)
        (BaseLift.putField wf productive prior.carriers ctorRef field (refs ref)
          (args.get ref))) := by
  intro fields refs args field ref
  induction ref with
  | here => cases args <;> rfl
  | there ref ih =>
      cases args with
      | base value tail => exact ih (fun ref => refs (.there ref)) tail
      | data value tail => exact ih (fun ref => refs (.there ref)) tail

/-- Lookup in the complete constructor specialization. -/
theorem argValues_get {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    (args : Args block prior.carriers.Base ctor.fields)
    {field : FieldDecl arity} (fieldRef : FieldRef ctor field) :
    (ctorArgs law wf productive priorRel priorModels ctorRef args)[fieldRef.index]? =
      some (.typed (field.fo block)
        (BaseLift.putField wf productive prior.carriers ctorRef field fieldRef
          (args.get fieldRef))) :=
  argValues_get_aux law wf productive priorRel priorModels ctorRef
    (fun ref => ref) args fieldRef

/-- Target constructor currying consumes the embedded payload list and rebuilds
the same free constructor value. -/
def ctorValue {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    (args : Args block prior.carriers.Base ctor.fields) :
    (FO.FOSort.base data.decl.sort).Denote
      (law.extend wf productive prior priorRel priorModels).carriers := by
  change BaseLift block prior.carriers.Base data.decl.sort
  exact .data data rfl (.ctor ctorRef args)

/-- View target currying at the carrier family of `law.extend`. -/
def curry {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    (fields : List (FieldDecl arity))
    (refs : ∀ {field}, Datatype.Ref fields field → FieldRef ctor field)
    (build : Args block prior.carriers.Base fields →
      BaseLift block prior.carriers.Base data.decl.sort) :
    FO.SymbolDenote (law.extend wf productive prior priorRel priorModels).carriers
      (fields.map fun field => field.fo block) (.base data.decl.sort) := by
  change FO.SymbolDenote (BaseLift.carriers productive prior.carriers)
    (fields.map fun field => field.fo block) (.base data.decl.sort)
  exact BaseLift.targetCurry wf productive prior.carriers ctorRef fields refs build

private theorem applyValues_curry
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) :
    ∀ (fields : List (FieldDecl arity))
      (refs : ∀ {field}, Datatype.Ref fields field → FieldRef ctor field)
      (build : Args block prior.carriers.Base fields →
        BaseLift block prior.carriers.Base data.decl.sort)
      (args : Args block prior.carriers.Base fields),
      SMT.applyValues (law.extend wf productive prior priorRel priorModels)
        (fields.map fun field => field.fo block)
        (curry law wf productive priorRel priorModels ctorRef fields refs build)
        (argValues law wf productive priorRel priorModels ctorRef fields refs args) =
      (show (FO.FOSort.base data.decl.sort).Denote
          (law.extend wf productive prior priorRel priorModels).carriers from
        by change BaseLift block prior.carriers.Base data.decl.sort; exact build args)
  | [], _, _, .nil => rfl
  | field :: rest, refs, build, args => by
      cases field with
      | mk name sort =>
          cases sort with
          | base base =>
              cases args with
              | base value tail =>
                  simp only [List.map_cons, FieldDecl.fo, FieldSort.fo,
                    SMT.applyValues, SMT.decode_typed, argValues, curry,
                    BaseLift.targetCurry, BaseLift.putField]
                  exact applyValues_curry law wf productive priorRel priorModels ctorRef rest
                    (fun ref => refs (.there ref))
                    (fun tail => build (.base value tail)) tail
          | data child =>
              cases args with
              | data value tail =>
                  simp only [List.map_cons, FieldDecl.fo, FieldSort.fo,
                    SMT.applyValues, SMT.decode_typed, argValues, curry,
                    BaseLift.targetCurry, BaseLift.putField]
                  exact applyValues_curry law wf productive priorRel priorModels ctorRef rest
                    (fun ref => refs (.there ref))
                    (fun tail => build (.data value tail)) tail

theorem applyValues_ctor
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (rolesUnique : native.RolesUnique)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    (args : Args block prior.carriers.Base ctor.fields) :
    SMT.applyValues (law.extend wf productive prior priorRel priorModels)
      (CtorDecl.fo block data ctor).args
      (result := (CtorDecl.fo block data ctor).result)
      ((law.extend wf productive prior priorRel priorModels).symbol (native.ctor ctorRef))
      (ctorArgs law wf productive priorRel priorModels ctorRef args) =
    ctorValue law wf productive priorRel priorModels ctorRef args := by
  rw [law.extend_ctor rolesUnique wf productive prior priorRel priorModels ctorRef]
  change SMT.applyValues _ (ctor.fields.map fun field => field.fo block)
      (curry law wf productive priorRel priorModels ctorRef ctor.fields (fun ref => ref)
        (fun args => .data data rfl (.ctor ctorRef args)))
      (ctorArgs law wf productive priorRel priorModels ctorRef args) = _
  exact applyValues_curry law wf productive priorRel priorModels ctorRef ctor.fields
    (fun ref => ref) (fun args => .data data rfl (.ctor ctorRef args)) args

/-- Applying one represented native constructor builds the corresponding free
target value. -/
theorem ctor_apply {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor)
    (args : Args block prior.carriers.Base ctor.fields) :
    (SMT.model fo (law.extend wf productive prior priorRel priorModels)).apply
      (.symb (data.name (.ctor child ctorRef.index)))
      (ctorArgs law wf productive priorRel priorModels ctorRef args)
      (.typed (.base child.decl.sort)
        (ctorValue law wf productive priorRel priorModels ctorRef args)) := by
  refine ⟨_, symbols.datatypeSymbols.ctor ctorRef,
    (represented.flattenedCtor_ident ctorRef).symm, ?_⟩
  have applied := applyValues_ctor law wf productive priorRel priorModels rolesUnique
    ctorRef args
  exact congrArg (Value.typed (.base child.decl.sort)) applied.symm

/-- One constructor payload viewed in the corresponding enlarged FO carrier. -/
def fieldTarget {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (field : FieldDecl arity)
    (fieldRef : FieldRef ctor field)
    (value : field.Denote block prior.carriers.Base) :
    (field.fo block).Denote
      (law.extend wf productive prior priorRel priorModels).carriers := by
  change (field.fo block).Denote (BaseLift.carriers productive prior.carriers)
  exact BaseLift.putField wf productive prior.carriers ctorRef field fieldRef value

/-- One target constructor field embedded in the shared raw universe. -/
def fieldValue {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (field : FieldDecl arity)
    (fieldRef : FieldRef ctor field)
    (value : field.Denote block prior.carriers.Base) :
    Value (law.extend wf productive prior priorRel priorModels) :=
  .typed (field.fo block)
    (fieldTarget law wf productive priorRel priorModels ctorRef field fieldRef value)

theorem fieldValue_typed {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (fo : SMT.Encoding (Symbol signature))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) (field : FieldDecl arity)
    (fieldRef : FieldRef ctor field)
    (value : field.Denote block prior.carriers.Base) :
    (SMT.model fo (law.extend wf productive prior priorRel priorModels)).inSort
      (fo.sort (field.fo block))
      (fieldValue law wf productive priorRel priorModels ctorRef field fieldRef value) :=
  Value.inSort_typed (target := law.extend wf productive prior priorRel priorModels)
    fo (field.fo block)
      (fieldTarget law wf productive priorRel priorModels ctorRef field fieldRef value)

/-- The exact target selector returns `fieldTarget` on its own constructor. -/
theorem sel_value {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (rolesUnique : native.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (args : Args block prior.carriers.Base ctor.fields) :
    (law.extend wf productive prior priorRel priorModels).symbol
        (native.sel ctorRef fieldRef)
        (ctorValue law wf productive priorRel priorModels ctorRef args) =
      fieldTarget law wf productive priorRel priorModels ctorRef field fieldRef
        (args.get fieldRef) := by
  rw [law.extend_sel rolesUnique wf productive prior priorRel priorModels]
  exact eq_of_heq (heq_of_eq
    (BaseLift.targetSel_ctor wf productive source.carriers prior.carriers
      priorRel law.carrier ctorRef fieldRef _ (law.sel_ctor ctorRef fieldRef)
      args))

/-- A matching selector recovers its embedded free constructor field. -/
theorem sel_apply_ctor {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (args : Args block prior.carriers.Base ctor.fields) :
    (SMT.model fo (law.extend wf productive prior priorRel priorModels)).apply
      (.symb (data.name (.sel child ctorRef.index fieldRef.index)))
      [.typed (.base child.decl.sort)
        (ctorValue law wf productive priorRel priorModels ctorRef args)]
      (fieldValue law wf productive priorRel priorModels ctorRef field fieldRef
        (args.get fieldRef)) := by
  refine ⟨_, symbols.datatypeSymbols.sel ctorRef fieldRef,
    (represented.flattenedSelector_ident ctorRef fieldRef).symm, ?_⟩
  apply congrArg (Value.typed (field.fo block))
  simpa only [FieldDecl.sel, SMT.applyValues, SMT.decode_typed,
    FO.SymbolDenote] using
    (sel_value law rolesUnique wf productive priorRel priorModels ctorRef
      fieldRef args).symm

/-- A represented tester denotes the typed constructor tag on every free
target value. -/
theorem test_apply {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor)
    (value : Val block prior.carriers.Base child) :
    (SMT.model fo (law.extend wf productive prior priorRel priorModels)).apply
      (.indexed "is" #[.inl (data.name (.ctor child ctorRef.index))])
      [.typed (.base child.decl.sort) (.data child rfl value)]
      (.typed .bool (IsCtor ctorRef value)) := by
  refine ⟨_, symbols.datatypeSymbols.test ctorRef,
    (represented.flattenedTester_ident ctorRef).symm, ?_⟩
  apply congrArg (Value.typed .bool)
  rw [law.extend_test rolesUnique wf productive prior priorRel priorModels]
  simp [SMT.applyValues, SMT.decode_typed, BaseLift.targetTest]

@[simp] theorem test_apply_ctor {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor)
    (args : Args block prior.carriers.Base ctor.fields) :
    (SMT.model fo (law.extend wf productive prior priorRel priorModels)).apply
      (.indexed "is" #[.inl (data.name (.ctor child ctorRef.index))])
      [.typed (.base child.decl.sort)
        (ctorValue law wf productive priorRel priorModels ctorRef args)]
      ((SMT.model fo (law.extend wf productive prior priorRel priorModels)).bool true) := by
  simpa [ctorValue, SMT.model_bool, boolValue] using
    test_apply law rolesUnique wf productive priorRel priorModels represented ctorRef
      (.ctor ctorRef args)

/-- A represented constructor has its exact native SMT function type in the
enlarged model. -/
theorem ctor_has_type {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) :
    Crush.SMT.SymbolHasType
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (.symb (data.name (.ctor child ctorRef.index)))
      (ctorDecl (block := block) data child ctorRef.index ctor).argSorts
      (dataSort data child) := by
  have typed := SMT.symbol_has_type fo
    (law.extend wf productive prior priorRel priorModels) (symbols.datatypeSymbols.ctor ctorRef)
  rw [represented.flattenedCtor_ident ctorRef] at typed
  simpa [raw_ctor_argSorts, Datatype.fieldSort_eq represented,
    CtorDecl.fo, represented.sort_eq child, Function.comp_def] using typed

/-- Invert a constructor application in the enlarged graph into its unique
typed payload telescope. -/
theorem ctor_apply_inv {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor)
    {values : List (SMT.Value (law.extend wf productive prior priorRel priorModels))}
    {output : SMT.Value (law.extend wf productive prior priorRel priorModels)}
    (typed : Crush.SMT.ValuesTyped
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (ctorDecl (block := block) data child ctorRef.index ctor).argSorts values)
    (applied : (SMT.model fo (law.extend wf productive prior priorRel priorModels)).apply
      (.symb (data.name (.ctor child ctorRef.index))) values output) :
    ∃ args : Args block prior.carriers.Base ctor.fields,
      values = ctorArgs law wf productive priorRel priorModels ctorRef args ∧
      output = .typed (.base child.decl.sort)
        (ctorValue law wf productive priorRel priorModels ctorRef args) := by
  have fieldsTyped : Crush.SMT.ValuesTyped
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (ctor.fields.map fun field => fo.sort (field.fo block)) values := by
    simpa [raw_ctor_argSorts, Datatype.fieldSort_eq represented] using typed
  obtain ⟨args, rfl⟩ := typed_args law wf productive priorRel priorModels fo ctorRef
    ctor.fields (fun ref => ref) fieldsTyped
  let expected : SMT.Value (law.extend wf productive prior priorRel priorModels) :=
    .typed (.base child.decl.sort)
      (ctorValue law wf productive priorRel priorModels ctorRef args)
  have expectedApply := ctor_apply law rolesUnique wf productive priorRel priorModels
    represented ctorRef args
  have argsTyped : Crush.SMT.ValuesTyped
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (ctorDecl (block := block) data child ctorRef.index ctor).argSorts
      (ctorArgs law wf productive priorRel priorModels ctorRef args) := by
    simpa [raw_ctor_argSorts, Datatype.fieldSort_eq represented] using
      (argValues_typed law wf productive priorRel priorModels fo ctorRef ctor.fields
        (fun ref => ref) args)
  obtain ⟨chosen, chosenTyped, chosenApply, unique⟩ :=
    ctor_has_type law wf productive priorRel priorModels represented ctorRef
      (ctorArgs law wf productive priorRel priorModels ctorRef args) argsTyped
  have outputEq := unique output applied
  have expectedEq := unique expected expectedApply
  exact ⟨args, rfl, outputEq.trans expectedEq.symm⟩

/-- Enlarged free constructors are total, typed, and injective. -/
theorem ctor_holds {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) :
    Crush.SMT.ConstructorHolds
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (dataSort data child)
      (ctorDecl (block := block) data child ctorRef.index ctor) := by
  constructor
  · exact ctor_has_type law wf productive priorRel priorModels represented ctorRef
  · intro leftArgs rightArgs leftResult rightResult
      leftApply rightApply resultEq
    obtain ⟨left, leftArgsEq, leftResultEq⟩ :=
      ctor_apply_inv law rolesUnique wf productive priorRel priorModels represented ctorRef
        leftApply.1 leftApply.2
    obtain ⟨right, rightArgsEq, rightResultEq⟩ :=
      ctor_apply_inv law rolesUnique wf productive priorRel priorModels represented ctorRef
        rightApply.1 rightApply.2
    have valueEq :
        (Value.typed (.base child.decl.sort)
          (ctorValue law wf productive priorRel priorModels ctorRef left) :
          SMT.Value (law.extend wf productive prior priorRel priorModels)) =
        .typed (.base child.decl.sort)
          (ctorValue law wf productive priorRel priorModels ctorRef right) := by
      rw [← leftResultEq, ← rightResultEq, resultEq]
    have carrierEq :
        ctorValue law wf productive priorRel priorModels ctorRef left =
          ctorValue law wf productive priorRel priorModels ctorRef right :=
      eq_of_heq (Value.typed.inj valueEq).2
    have coreEq : (Val.ctor ctorRef left :
        Val block prior.carriers.Base child) = .ctor ctorRef right := by
      change BaseLift.data child rfl (.ctor ctorRef left) =
        BaseLift.data child rfl (.ctor ctorRef right) at carrierEq
      injection carrierEq
    have argsEq := Datatype.ctor_inj ctorRef coreEq
    rw [leftArgsEq, rightArgsEq, argsEq]

theorem sel_has_type {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    Crush.SMT.SymbolHasType
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (.symb (data.name (.sel child ctorRef.index fieldRef.index)))
      [dataSort data child]
      (fieldSort (block := block) data field.sort) := by
  have typed := SMT.symbol_has_type fo
    (law.extend wf productive prior priorRel priorModels)
    (symbols.datatypeSymbols.sel ctorRef fieldRef)
  rw [represented.flattenedSelector_ident ctorRef fieldRef] at typed
  cases field with
  | mk name sort =>
      cases sort with
      | base base =>
          simpa [FieldDecl.sel, FieldDecl.fo, FieldSort.fo, fieldSort,
            represented.base_eq base, represented.sort_eq child,
            Function.comp_def] using typed
      | data fieldData =>
          change Crush.SMT.SymbolHasType _ _ [dataSort data child]
            (dataSort data fieldData)
          rw [← represented.sort_eq child, ← represented.sort_eq fieldData]
          simpa [FieldDecl.sel, FieldDecl.fo, FieldSort.fo, fieldSort,
            DataRef.decl, Function.comp_def] using typed

/-- Every selector is total and recovers its matching constructor field. -/
theorem sel_holds {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) :
    Crush.SMT.SelectorsHold
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (dataSort data child)
      (ctorDecl (block := block) data child ctorRef.index ctor) := by
  intro index name resultSort lookup
  have rawBounds : index <
      (ctorDecl (block := block) data child ctorRef.index ctor).selDecls.size :=
    (Array.getElem?_eq_some_iff.mp lookup).1
  have inBounds : index < ctor.fields.length := by
    simpa [ctorDecl] using rawBounds
  let field := ctor.fields[index]
  let fieldRef : FieldRef ctor field :=
    Datatype.Ref.ofIdx ctor.fields index inBounds
  have indexEq : fieldRef.index = index :=
    Datatype.Ref.index_ofIdx ctor.fields index inBounds
  have canonical := sel_get data ctorRef fieldRef
  rw [indexEq, lookup] at canonical
  have pairEq := Option.some.inj canonical
  cases pairEq
  constructor
  · simpa [indexEq] using
      sel_has_type law wf productive priorRel priorModels represented ctorRef fieldRef
  · intro arguments result selected ctorApplied selectedAt
    obtain ⟨args, argumentsEq, resultEq⟩ :=
      ctor_apply_inv law rolesUnique wf productive priorRel priorModels represented ctorRef
        ctorApplied.1 ctorApplied.2
    have canonicalGet := argValues_get law wf productive priorRel priorModels ctorRef args
      fieldRef
    rw [indexEq] at canonicalGet
    rw [argumentsEq] at selectedAt
    have selectedEq := Option.some.inj (selectedAt.symm.trans canonicalGet)
    rw [resultEq, selectedEq]
    simpa [indexEq, fieldValue, fieldTarget] using
      sel_apply_ctor law rolesUnique wf productive priorRel priorModels represented ctorRef
        fieldRef args

theorem test_has_type {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) :
    Crush.SMT.SymbolHasType
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (ctorDecl (block := block) data child ctorRef.index ctor).tester
      [dataSort data child] Crush.SMT.boolSort := by
  have typed := SMT.symbol_has_type fo
    (law.extend wf productive prior priorRel priorModels) (symbols.datatypeSymbols.test ctorRef)
  rw [represented.flattenedTester_ident ctorRef] at typed
  simpa [Crush.SMT.CtorDecl.tester, ctorDecl, CtorDecl.test,
    represented.sort_eq child, fo.bool_eq, Function.comp_def] using typed

theorem test_apply_ne {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {leftCtor rightCtor : CtorDecl arity}
    (leftRef : CtorRef block child leftCtor)
    (rightRef : CtorRef block child rightCtor)
    (different : leftRef.index ≠ rightRef.index)
    (args : Args block prior.carriers.Base rightCtor.fields) :
    (SMT.model fo (law.extend wf productive prior priorRel priorModels)).apply
      (.indexed "is" #[.inl (data.name (.ctor child leftRef.index))])
      [.typed (.base child.decl.sort)
        (ctorValue law wf productive priorRel priorModels rightRef args)]
      ((SMT.model fo (law.extend wf productive prior priorRel priorModels)).bool false) := by
  have applied := test_apply law rolesUnique wf productive priorRel priorModels represented
    leftRef (.ctor rightRef args)
  have rejected : IsCtor leftRef (.ctor rightRef args) = False := by
    apply propext
    exact ⟨fun holds => test_ne leftRef rightRef different args holds,
      False.elim⟩
  simpa [ctorValue, SMT.model_bool, boolValue, rejected] using applied

theorem test_holds {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) :
    Crush.SMT.TesterHolds
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (dataSort data child)
      (ctorDecl (block := block) data child ctorRef.index ctor) := by
  constructor
  · exact test_has_type law wf productive priorRel priorModels represented ctorRef
  · intro arguments result applied
    obtain ⟨args, argumentsEq, resultEq⟩ :=
      ctor_apply_inv law rolesUnique wf productive priorRel priorModels represented ctorRef
        applied.1 applied.2
    rw [resultEq]
    exact test_apply_ctor law rolesUnique wf productive priorRel priorModels represented
      ctorRef args

/-- Every constructor emitted by the block satisfies its constructor,
selector, and tester laws in the enlarged model. -/
theorem ctor_laws {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {sort : Crush.SMT.SSort} {rawCtor : Crush.SMT.CtorDecl}
    (member : (sort, rawCtor) ∈
      Crush.SMT.datatypeCtors (entries block data)) :
    Crush.SMT.ConstructorHolds
        (SMT.model fo (law.extend wf productive prior priorRel priorModels)) sort rawCtor ∧
      Crush.SMT.SelectorsHold
        (SMT.model fo (law.extend wf productive prior priorRel priorModels)) sort rawCtor ∧
      Crush.SMT.TesterHolds
        (SMT.model fo (law.extend wf productive prior priorRel priorModels)) sort rawCtor := by
  obtain ⟨child, ctor, ctorRef, rfl, rfl⟩ := raw_ctor_ref data member
  exact ⟨ctor_holds law rolesUnique wf productive priorRel priorModels represented ctorRef,
    sel_holds law rolesUnique wf productive priorRel priorModels represented ctorRef,
    test_holds law rolesUnique wf productive priorRel priorModels represented ctorRef⟩

/-- Results of different constructors are distinct in the enlarged free
algebra. -/
theorem ctor_disjoint {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {leftSort rightSort : Crush.SMT.SSort}
    {leftCtor rightCtor : Crush.SMT.CtorDecl}
    (leftMem : (leftSort, leftCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    (rightMem : (rightSort, rightCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    (different : leftCtor.name ≠ rightCtor.name)
    {leftArgs rightArgs : List
      (SMT.Value (law.extend wf productive prior priorRel priorModels))}
    {leftResult rightResult :
      SMT.Value (law.extend wf productive prior priorRel priorModels)}
    (leftApply : Crush.SMT.CtorApplies
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      leftCtor leftArgs leftResult)
    (rightApply : Crush.SMT.CtorApplies
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      rightCtor rightArgs rightResult) :
    leftResult ≠ rightResult := by
  obtain ⟨leftData, leftDecl, leftRef, rfl, rfl⟩ :=
    raw_ctor_ref data leftMem
  obtain ⟨rightData, rightDecl, rightRef, rfl, rfl⟩ :=
    raw_ctor_ref data rightMem
  obtain ⟨left, leftArgsEq, leftResultEq⟩ :=
    ctor_apply_inv law rolesUnique wf productive priorRel priorModels represented leftRef
      leftApply.1 leftApply.2
  obtain ⟨right, rightArgsEq, rightResultEq⟩ :=
    ctor_apply_inv law rolesUnique wf productive priorRel priorModels represented rightRef
      rightApply.1 rightApply.2
  intro resultEq
  have valueEq :
      (Value.typed (.base leftData.decl.sort)
        (ctorValue law wf productive priorRel priorModels leftRef left) :
        SMT.Value (law.extend wf productive prior priorRel priorModels)) =
      .typed (.base rightData.decl.sort)
        (ctorValue law wf productive priorRel priorModels rightRef right) := by
    rw [← leftResultEq, ← rightResultEq, resultEq]
  have sortEq := (Value.typed.inj valueEq).1
  have baseEq : leftData.decl.sort = rightData.decl.sort := by
    injection sortEq
  have dataEq := wf.data_eq baseEq
  subst rightData
  have carrierEq :
      ctorValue law wf productive priorRel priorModels leftRef left =
        ctorValue law wf productive priorRel priorModels rightRef right :=
    eq_of_heq (Value.typed.inj valueEq).2
  have coreEq : (Val.ctor leftRef left :
      Val block prior.carriers.Base leftData) = .ctor rightRef right := by
    change BaseLift.data leftData rfl (.ctor leftRef left) =
      BaseLift.data leftData rfl (.ctor rightRef right) at carrierEq
    injection carrierEq
  have indexNe : leftRef.index ≠ rightRef.index := by
    intro indexEq
    apply different
    simp [ctorDecl, indexEq]
  exact ctor_ne leftRef rightRef indexNe left right coreEq

/-- A tester rejects a value built by another constructor of the same datatype
datatype. -/
theorem test_disjoint {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {sort : Crush.SMT.SSort} {leftCtor rightCtor : Crush.SMT.CtorDecl}
    (leftMem : (sort, leftCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    (rightMem : (sort, rightCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    (different : leftCtor.name ≠ rightCtor.name)
    {arguments : List (SMT.Value (law.extend wf productive prior priorRel priorModels))}
    {result : SMT.Value (law.extend wf productive prior priorRel priorModels)}
    (applied : Crush.SMT.CtorApplies
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      rightCtor arguments result) :
    (SMT.model fo (law.extend wf productive prior priorRel priorModels)).apply
      leftCtor.tester [result]
      ((SMT.model fo (law.extend wf productive prior priorRel priorModels)).bool false) := by
  obtain ⟨leftData, leftDecl, leftRef, leftSortEq, leftCtorEq⟩ :=
    raw_ctor_ref data leftMem
  obtain ⟨rightData, rightDecl, rightRef, rightSortEq, rightCtorEq⟩ :=
    raw_ctor_ref data rightMem
  have dataEq : leftData = rightData := dataSort_injective represented.wf.names
    (leftSortEq.symm.trans rightSortEq)
  subst rightData
  have indexNe : leftRef.index ≠ rightRef.index := by
    intro indexEq
    apply different
    rw [leftCtorEq, rightCtorEq]
    simp [ctorDecl, indexEq]
  rw [rightCtorEq] at applied
  rw [leftCtorEq]
  obtain ⟨args, argumentsEq, resultEq⟩ :=
    ctor_apply_inv law rolesUnique wf productive priorRel priorModels represented rightRef
      applied.1 applied.2
  rw [resultEq]
  simpa [Crush.SMT.CtorDecl.tester, ctorDecl] using
    test_apply_ne law rolesUnique wf productive priorRel priorModels represented leftRef
      rightRef indexNe args

/-- Every value at a datatype sort is built by a constructor of that exact
native declaration. -/
theorem exhaustive {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {name : String} {count : Nat} {decl : Crush.SMT.DatatypeDecl}
    (member : (name, count, decl) ∈ (entries block data).toList)
    (value : SMT.Value (law.extend wf productive prior priorRel priorModels))
    (typed : (SMT.model fo (law.extend wf productive prior priorRel priorModels)).inSort
      (Crush.SMT.datatypeSort name) value) :
    ∃ ctor, ctor ∈ decl.ctors.toList ∧
      ∃ arguments, Crush.SMT.CtorApplies
        (SMT.model fo (law.extend wf productive prior priorRel priorModels))
        ctor arguments value := by
  obtain ⟨child, nameEq, countEq, declEq⟩ :=
    raw_entry_ref block data member
  subst name
  subst count
  subst decl
  change (SMT.model fo (law.extend wf productive prior priorRel priorModels)).inSort
    (dataSort data child) value at typed
  rw [← represented.sort_eq child] at typed
  obtain ⟨targetValue, rfl⟩ := Value.exists_typed_of_inSort
    fo (.base child.decl.sort) _ typed
  let core := BaseLift.asData wf child targetValue
  obtain ⟨ctor, ctorRef, args, coreEq⟩ := ctor_cases core
  have targetEq : targetValue =
      (BaseLift.data child rfl (.ctor ctorRef args) :
        BaseLift block prior.carriers.Base child.decl.sort) := by
    calc
      targetValue = .data child rfl core :=
        (BaseLift.data_asData wf child targetValue).symm
      _ = .data child rfl (.ctor ctorRef args) := congrArg _ coreEq
  let rawCtor := ctorDecl (block := block) data child ctorRef.index ctor
  refine ⟨rawCtor, ?_, ctorArgs law wf productive priorRel priorModels ctorRef args, ?_, ?_⟩
  · change rawCtor ∈ (block.decl child).ctors.mapIdx fun index ctor =>
      ctorDecl (block := block) data child index ctor
    exact Datatype.Ref.mem_mapIdx ctorRef fun index ctor =>
      ctorDecl (block := block) data child index ctor
  · simpa [rawCtor, raw_ctor_argSorts, Datatype.fieldSort_eq represented] using
      (argValues_typed law wf productive priorRel priorModels fo ctorRef ctor.fields
        (fun ref => ref) args)
  · rw [targetEq]
    exact ctor_apply law rolesUnique wf productive priorRel priorModels represented ctorRef args

/-- Structural height of values declared by this block inside the one raw value
universe. Values at other sorts have rank zero. -/
noncomputable def rank {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel) :
    SMT.Value (law.extend wf productive prior priorRel priorModels) → Nat
  | .typed (.base sort) value =>
      if present : ∃ child : DataRef block, child.decl.sort = sort then
        let child := Classical.choose present
        let equal := Classical.choose_spec present
        (BaseLift.asData wf child (equal.symm ▸ value)).height
      else 0
  | _ => 0

private theorem rank_cast {selected child : DataRef block}
    (wf : block.WF) (dataEq : selected = child)
    (sortEq : selected.decl.sort = child.decl.sort)
    {Prior : BaseSort → Type} (value : Val block Prior child) :
    (BaseLift.asData wf selected
      (sortEq.symm ▸ (BaseLift.data child rfl value))).height = value.height := by
  subst selected
  have proofEq : sortEq = rfl := Subsingleton.elim _ _
  rw [proofEq]
  simp

/-- The rank of a datatype value is exactly its free-tree height. -/
@[simp] theorem rank_data {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel native source) (wf : block.WF)
    (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (child : DataRef block) (value : Val block prior.carriers.Base child) :
    rank law wf productive priorRel priorModels
      (.typed (.base child.decl.sort) (.data child rfl value)) =
      value.height := by
  rw [rank]
  split
  next present =>
    let selected := Classical.choose present
    have sortEq : selected.decl.sort = child.decl.sort :=
      Classical.choose_spec present
    have selectedEq : selected = child := wf.data_eq sortEq
    exact rank_cast wf selectedEq (Classical.choose_spec present) value
  next absent =>
    exact False.elim (absent ⟨child, rfl⟩)

/-- Every recursive field of an applied constructor strictly decreases the
structural rank. -/
theorem rank_lt {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data)
    {sort : Crush.SMT.SSort} {rawCtor : Crush.SMT.CtorDecl}
    (member : (sort, rawCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    {arguments : List (SMT.Value (law.extend wf productive prior priorRel priorModels))}
    {result : SMT.Value (law.extend wf productive prior priorRel priorModels)}
    (applied : Crush.SMT.CtorApplies
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      rawCtor arguments result)
    (index : Nat) (rawFieldSort : Crush.SMT.SSort)
    (rawFieldValue : SMT.Value (law.extend wf productive prior priorRel priorModels))
    (sortAt : rawCtor.argSorts[index]? = some rawFieldSort)
    (valueAt : arguments[index]? = some rawFieldValue)
    (recursive : rawFieldSort ∈
      Crush.SMT.datatypeSorts (entries block data)) :
    rank law wf productive priorRel priorModels rawFieldValue <
      rank law wf productive priorRel priorModels result := by
  obtain ⟨parent, ctor, ctorRef, rfl, rfl⟩ := raw_ctor_ref data member
  obtain ⟨args, argumentsEq, resultEq⟩ :=
    ctor_apply_inv law rolesUnique wf productive priorRel priorModels represented ctorRef
      applied.1 applied.2
  rw [raw_ctor_argSorts] at sortAt
  have rawBounds : index <
      (ctor.fields.map fun field =>
        fieldSort (block := block) data field.sort).length :=
    (List.getElem?_eq_some_iff.mp sortAt).1
  have inBounds : index < ctor.fields.length := by simpa using rawBounds
  let field := ctor.fields[index]
  let fieldRef : FieldRef ctor field :=
    Datatype.Ref.ofIdx ctor.fields index inBounds
  have indexEq : fieldRef.index = index :=
    Datatype.Ref.index_ofIdx ctor.fields index inBounds
  have canonicalSort :
      (ctor.fields.map fun field =>
        fieldSort (block := block) data field.sort)[fieldRef.index]? =
      some (fieldSort (block := block) data field.sort) := by
    simp
  rw [indexEq, sortAt] at canonicalSort
  have fieldSortEq := Option.some.inj canonicalSort
  obtain ⟨child, recursiveEq⟩ := raw_sort_ref block data recursive
  have encoded : fieldSort (block := block) data field.sort =
      dataSort data child := fieldSortEq.symm.trans recursiveEq
  obtain ⟨name, dataFieldRef, dataIndexEq⟩ :=
    field_data_ref represented ctorRef fieldRef child encoded
  have dataIndex : dataFieldRef.index = index := dataIndexEq.trans indexEq
  let childValue : Val block prior.carriers.Base child := args.get dataFieldRef
  rw [argumentsEq] at valueAt
  have canonicalValue := argValues_get law wf productive priorRel priorModels ctorRef args
    dataFieldRef
  rw [dataIndex] at canonicalValue
  have valueEq := Option.some.inj (valueAt.symm.trans canonicalValue)
  rw [resultEq, valueEq]
  change rank law wf productive priorRel priorModels
      (.typed (.base child.decl.sort)
        (BaseLift.data child rfl (args.get dataFieldRef))) <
    rank law wf productive priorRel priorModels
      (.typed (.base parent.decl.sort)
        (BaseLift.data parent rfl (.ctor ctorRef args)))
  rw [rank_data law wf productive priorRel priorModels,
    rank_data law wf productive priorRel priorModels]
  simpa [childValue] using
    Args.get_height_lt_ctor args dataFieldRef ctorRef rfl

/-- The enlarged model satisfies every semantic law of this native datatype
block. -/
theorem data_hold {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (rolesUnique : symbols.datatypeSymbols.RolesUnique)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data) :
    Crush.SMT.DatatypesHold
      (SMT.model fo (law.extend wf productive prior priorRel priorModels))
      (entries block data) := by
  refine ⟨wellFormed represented.wf, ?_, ?_, ?_, ?_,
    rank law wf productive priorRel priorModels, ?_⟩
  · intro sort ctor member
    exact ctor_laws law rolesUnique wf productive priorRel priorModels represented member
  · intro leftSort leftCtor rightSort rightCtor leftMem rightMem different
      leftArgs leftResult rightArgs rightResult leftApply rightApply
    exact ctor_disjoint law rolesUnique wf productive priorRel priorModels represented
      leftMem rightMem different leftApply rightApply
  · intro name count decl member value typed
    exact exhaustive law rolesUnique wf productive priorRel priorModels represented member
      value typed
  · intro sort leftCtor rightCtor leftMem rightMem different arguments result
      applied
    exact test_disjoint law rolesUnique wf productive priorRel priorModels represented
      leftMem rightMem different applied
  · intro sort ctor member arguments result applied index fieldSort fieldValue
      sortAt valueAt recursive
    exact rank_lt law rolesUnique wf productive priorRel priorModels represented member applied
      index fieldSort fieldValue sortAt valueAt recursive

/-- One emitted native `declare-datatypes` command is valid directly in the
enlarged model. -/
theorem command_sound {symbols : Symbols signature block}
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data) :
    (SMT.model fo (law.extend wf productive prior priorRel priorModels)).SatisfiesCommand
      (command block data) :=
  data_hold law represented.rolesUnique wf productive priorRel priorModels
    represented

/-- The command theorem stated at the actual dependency-fold step. -/
theorem extend_sound {symbols : Symbols signature block}
    {source : FO.FamilyModel (Symbol signature)}
    (law : IsFreeDatatypeFamilyModel symbols.datatypeSymbols source)
    (prior : Lifted source) (wf : block.WF) (productive : Productive block)
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Repr block symbols fo data) :
    (SMT.model fo (prior.extend law wf productive).target).SatisfiesCommand
      (command block data) := by
  simpa [Lifted.extend] using
    command_sound law wf productive prior.relation prior.models represented

end Crush.Metatheory.SMT.Datatype.Native
