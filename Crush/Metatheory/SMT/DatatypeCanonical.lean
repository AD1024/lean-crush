import Crush.Metatheory.SMT.DatatypeRepresentation
import Crush.Metatheory.SMT.Model

/-!
# Canonical datatype semantics in the shared SMT model

This file proves native datatype obligations directly in the ordinary SMT
model induced from the flattened FO model. Datatype values are carried by the
existing `SMT.Value.typed` constructor; there is no second raw universe.
-/

namespace Crush.Metatheory.SMT.Datatype

open Crush.Metatheory.Datatype
open Crush.Metatheory.Defunctionalization.Flattened
open Crush.SMT.Model (satisfiesCommands_append satisfiesCommands_empty
  satisfiesCommands_push)
open scoped Crush.Metatheory Crush.SMT

variable {signature : Signature} {arity : Nat}
variable {block : Block arity} {symbols : Symbols signature block}

/-- Canonical constructor arguments embedded in the one generic raw universe. -/
def argValues {source : Model signature} (law : IsFreeDatatypeModel symbols source) :
    {fields : List (FieldDecl arity)} →
      Args block source.Base fields →
        List (SMT.Value
          (canonicalModel source))
  | _, .nil => []
  | _, .base value rest =>
      .typed (.base _) value :: argValues law (fields := _) rest
  | _, .data (data := data) value rest =>
      .typed (.base data.decl.sort) ((law.carrier data).«from» value) ::
        argValues law (fields := _) rest

/-- Embed one canonical field in the generic raw universe. -/
def fieldValue {source : Model signature} (law : IsFreeDatatypeModel symbols source)
    (field : FieldDecl arity) :
    field.Denote block source.Base →
      SMT.Value
        (canonicalModel source) :=
  match field with
  | ⟨_, .base sort⟩ => fun value => .typed (.base sort) value
  | ⟨_, .data data⟩ => fun value =>
      .typed (.base (block.decl data).sort) ((law.carrier data).«from» value)

@[simp] theorem fieldSort_eq
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    (field : FieldDecl arity) :
    fieldSort (block := block) data field.sort =
      fo.sort (field.fo block) := by
  cases field with
  | mk name sort =>
      cases sort with
      | base sort => exact represented.base_eq sort
      | data child => exact (represented.sort_eq child).symm

/-- Canonical constructor arguments have exactly their shared encoded sorts. -/
theorem argValues_typed {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {fields : List (FieldDecl arity)}
    (args : Args block source.Base fields) :
    Crush.SMT.ValuesTyped
      (SMT.model fo
        (canonicalModel source))
      (fields.map fun field : FieldDecl arity =>
        fo.sort (FieldDecl.fo block field))
      (argValues law args) := by
  exact Args.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun fields args =>
      Crush.SMT.ValuesTyped
        (SMT.model fo
          (canonicalModel source))
        (fields.map fun field : FieldDecl arity =>
          fo.sort (FieldDecl.fo block field))
        (argValues law args))
    (ctor := fun _ _ _ => trivial)
    (nil := .nil)
    (base := @fun name sort rest value tail tailIH =>
      .cons (Value.inSort_typed
        (target := canonicalModel source)
        fo (.base sort) value) tailIH)
    (data := @fun name child rest value valueIH tail tailIH =>
      .cons (Value.inSort_typed
        (target := canonicalModel source)
        fo (.base child.decl.sort)
        ((law.carrier child).«from» value)) tailIH)
    args

/-- Positional lookup commutes with canonical argument embedding. -/
@[simp] theorem argValues_get {source : Model signature}
    (law : IsFreeDatatypeModel symbols source) {fields : List (FieldDecl arity)}
    (args : Args block source.Base fields) {field : FieldDecl arity}
    (ref : Datatype.Ref fields field) :
    (argValues law args)[ref.index]? = some (fieldValue law field (args.get ref)) := by
  induction ref with
  | here => cases args <;> rfl
  | there ref ih =>
      cases args with
      | base value rest => exact ih rest
      | data value rest => exact ih rest

/-- Every generic raw list typed by a constructor telescope comes from one
canonical typed argument telescope. -/
theorem typed_args {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    (fo : SMT.Encoding (Symbol signature))
    {fields : List (FieldDecl arity)}
    {values : List (SMT.Value
      (canonicalModel source))}
    (typed : Crush.SMT.ValuesTyped
      (SMT.model fo
        (canonicalModel source))
      (fields.map fun field : FieldDecl arity => fo.sort (field.fo block))
      values) :
    ∃ args : Args block source.Base fields, values = argValues law args := by
  induction fields generalizing values with
  | nil =>
      have equal := typed.eq_nil
      subst values
      exact ⟨.nil, rfl⟩
  | cons field fields ih =>
      obtain ⟨headValue, tailValues, rfl, head, tail⟩ :=
        typed.exists_cons
      cases field with
      | mk name sort =>
          cases sort with
          | base base =>
              obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
                fo (.base base) _ head
              obtain ⟨rest, rfl⟩ := ih tail
              exact ⟨.base value rest, rfl⟩
          | data child =>
              obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
                fo (.base (block.decl child).sort) _ head
              obtain ⟨rest, rfl⟩ := ih tail
              refine ⟨.data ((law.carrier child).to value) rest, ?_⟩
              simp only [argValues, DataRef.decl]
              rw [(law.carrier child).left_inv value]
              rfl

/-- Erasing one datatype field type agrees with its typed FO sort. -/
@[simp] theorem ofTy_field (field : FieldDecl arity) :
    FO.FOSort.ofTy (field.ty block) = field.fo block := by
  cases field with
  | mk name sort => cases sort <;> rfl

/-- Arrow flattening preserves a constructor field telescope exactly. -/
@[simp] theorem flatten_fields (fields : List (FieldDecl arity))
    (result : BaseSort) :
    FO.flattenArrow
      (fields.foldr (fun field rest => .arrow (field.ty block) rest)
        (.base result)) =
      (fields.map fun field => field.ty block, .base result) := by
  induction fields with
  | nil => rfl
  | cons field fields ih => simp [ih]

/-- Flattening a constructor telescope produces exactly its typed FO
declaration. -/
@[simp] theorem sourceDecl_fields (fields : List (FieldDecl arity))
    (result : BaseSort) :
    Defunctionalization.sourceDecl
      (fields.foldr (fun field rest => .arrow (field.ty block) rest)
        (.base result)) =
      { args := fields.map fun field => field.fo block
        result := .base result } := by
  simp [Defunctionalization.sourceDecl]

/-- Curried constructor semantics stated directly at the flattened FO type. -/
def foCurry {source : Model signature}
    (carrier : ∀ data : DataRef block,
      Iso (source.Base data.decl.sort) (Val block source.Base data)) :
    (fields : List (FieldDecl arity)) → (result : BaseSort) →
    (Args block source.Base fields → source.Base result) →
      FO.SymbolDenote
        (canonicalModel source).carriers
        (fields.map fun field => field.fo block) (.base result)
  | [], _, build => build .nil
  | { name, sort := .base sort } :: rest, result, build =>
      fun value => foCurry carrier rest result fun tail =>
        build (.base value tail)
  | { name, sort := .data child } :: rest, result, build =>
      fun value => foCurry carrier rest result fun tail =>
        build (.data ((carrier child).to value) tail)

/-- Generic SMT application of a flattened constructor telescope is ordinary
curried source application. Recursive arguments cross the carrier isomorphism
exactly once in each direction. -/
theorem applyValues_foCurry {source : Model signature}
    (law : IsFreeDatatypeModel symbols source) (fields : List (FieldDecl arity))
    (result : BaseSort)
    (build : Args block source.Base fields → source.Base result)
    (args : Args block source.Base fields) :
    SMT.applyValues
      (canonicalModel source)
      (fields.map fun field : FieldDecl arity => field.fo block)
      (result := .base result) (foCurry law.carrier fields result build)
      (argValues law args) = build args := by
  induction fields with
  | nil => cases args; rfl
  | cons field fields ih =>
      cases field with
      | mk name sort =>
          cases sort with
          | base base =>
              cases args with
              | base value rest =>
                  simp only [List.map_cons, FieldDecl.fo, FieldSort.fo,
                    foCurry, argValues, SMT.applyValues,
                    SMT.decode_typed]
                  exact ih _ rest
          | data child =>
              cases args with
              | data value rest =>
                  simp only [List.map_cons, FieldDecl.fo, FieldSort.fo,
                    foCurry, argValues, SMT.applyValues,
                    DataRef.decl, SMT.decode_typed]
                  rw [(law.carrier child).right_inv value]
                  exact ih _ rest

/-- Source currying followed by flattened denotation has the expected result
on a canonical constructor argument telescope. `HEq` exposes the declaration
normalization without introducing a second semantic carrier. -/
theorem applyValues_curry {source : Model signature}
    (law : IsFreeDatatypeModel symbols source) (fields : List (FieldDecl arity))
    (result : BaseSort)
    (build : Args block source.Base fields → source.Base result)
    (args : Args block source.Base fields) :
    HEq
      (SMT.applyValues
        (canonicalModel source)
        (Defunctionalization.sourceDecl
          (fields.foldr (fun field rest => .arrow (field.ty block) rest)
            (.base result))).args
        (result := (Defunctionalization.sourceDecl
          (fields.foldr (fun field rest => .arrow (field.ty block) rest)
            (.base result))).result)
      (flattenedDenote source
        (fields.foldr (fun field rest => .arrow (field.ty block) rest)
          (.base result))
        (Args.curry law.carrier fields (.base result) build))
        (argValues law args))
      (build args) := by
  induction fields with
  | nil => cases args; rfl
  | cons field fields ih =>
      cases field with
      | mk name sort =>
          cases sort with
          | base base =>
              cases args with
              | base value rest =>
                  simpa [Defunctionalization.sourceDecl,
                    FieldDecl.ty, FieldSort.ty, DataRef.decl,
                    Args.curry, argValues,
                    flattenedDenote,
                    Defunctionalization.fromCanonical,
                    SMT.applyValues,
                    SMT.decode_typed]
                    using ih (fun tail => build (.base value tail)) rest
          | data child =>
              cases args with
              | data value rest =>
                  have inverse := (law.carrier child).right_inv value
                  simpa [Defunctionalization.sourceDecl,
                    FieldDecl.ty, FieldSort.ty, DataRef.decl,
                    Args.curry, argValues,
                    flattenedDenote,
                    Defunctionalization.fromCanonical,
                    SMT.applyValues,
                    SMT.decode_typed, inverse]
                    using ih (fun tail => build (.data value tail)) rest

/-- Applying an encoded datatype constructor in the shared graph yields the
source carrier value corresponding to the canonical constructor tree. -/
theorem ctor_apply {source : Model signature} (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor)
    (args : Args block source.Base ctor.fields) :
    (SMT.model fo
      (canonicalModel source)).apply
      (.symb (data.name (.ctor child ref.index))) (argValues law args)
      (.typed (.base child.decl.sort)
        ((law.carrier child).«from» (.ctor ref args))) := by
  refine ⟨_, .sourceConstant (symbols.ctor ref), ?_, ?_⟩
  · exact (represented.ctor_ident ref).symm
  · rw [canonicalModel_sourceConstant,
      law.ctor_denote]
    have applied := applyValues_curry law ctor.fields child.decl.sort
      (fun args => (law.carrier child).«from» (.ctor ref args)) args
    apply eq_of_heq
    congr 1
    · exact (congrArg FO.SymbolDecl.result
        (sourceDecl_fields (block := block) ctor.fields child.decl.sort)).symm
    · exact applied.symm

/-- A canonical field value has the shared encoding of its typed FO sort. -/
theorem fieldValue_typed {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    (field : FieldDecl arity)
    (value : field.Denote block source.Base) :
    (SMT.model fo
      (canonicalModel source)).inSort
      (fo.sort (field.fo block)) (fieldValue law field value) := by
  cases field with
  | mk name sort =>
      cases sort with
      | base base =>
          exact Value.inSort_typed
            (target := canonicalModel source)
            fo _ value
      | data child =>
          exact Value.inSort_typed
            (target := canonicalModel source)
            fo _ ((law.carrier child).«from» value)

/-- An encoded selector recovers its field on its own constructor in the
shared symbol graph. -/
theorem sel_apply_ctor {source : Model signature} (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field)
    (args : Args block source.Base ctor.fields) :
    (SMT.model fo
      (canonicalModel source)).apply
      (.symb (data.name (.sel child ctorRef.index fieldRef.index)))
      [.typed (.base child.decl.sort)
        ((law.carrier child).«from» (.ctor ctorRef args))]
      (fieldValue law field (args.get fieldRef)) := by
  refine ⟨_, .sourceConstant (symbols.sel ctorRef fieldRef), ?_, ?_⟩
  · exact (represented.sel_ident ctorRef fieldRef).symm
  · rw [canonicalModel_sourceConstant]
    cases field with
    | mk name sort =>
        cases sort with
        | base base =>
            apply congrArg (Value.typed (.base base))
            simpa [SMT.applyValues,
              SMT.decode_typed,
              Defunctionalization.sourceDecl,
              FieldDecl.ty, FieldSort.ty,
              flattenedDenote,
              Defunctionalization.fromCanonical,
              fieldValue, FieldDecl.fromVal]
              using (law.sel_ctor ctorRef fieldRef args).symm
        | data fieldData =>
            apply congrArg (Value.typed (.base (block.decl fieldData).sort))
            simpa [SMT.applyValues,
              SMT.decode_typed,
              Defunctionalization.sourceDecl,
              FieldDecl.ty, FieldSort.ty, DataRef.decl,
              flattenedDenote,
              Defunctionalization.fromCanonical,
              fieldValue, FieldDecl.fromVal]
              using (law.sel_ctor ctorRef fieldRef args).symm

/-- An encoded tester returns the proposition that its canonical value has the
selected constructor. -/
theorem test_apply {source : Model signature} (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) (value : Val block source.Base child) :
    (SMT.model fo
      (canonicalModel source)).apply
      (.indexed "is" #[.inl (data.name (.ctor child ref.index))])
      [.typed (.base child.decl.sort) ((law.carrier child).«from» value)]
      (.typed .bool (IsCtor ref value)) := by
  refine ⟨_, .sourceConstant (symbols.test ref), ?_, ?_⟩
  · exact (represented.test_ident ref).symm
  · apply congrArg (Value.typed .bool)
    rw [canonicalModel_sourceConstant]
    apply propext
    simpa [SMT.applyValues,
      SMT.decode_typed,
      flattenedDenote,
      Defunctionalization.toCanonical,
      Defunctionalization.fromCanonical,
      (law.carrier child).right_inv value]
      using (law.test_denote ref ((law.carrier child).«from» value)).symm

@[simp] theorem test_apply_ctor {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor)
    (args : Args block source.Base ctor.fields) :
    (SMT.model fo
      (canonicalModel source)).apply
      (.indexed "is" #[.inl (data.name (.ctor child ref.index))])
      [.typed (.base child.decl.sort)
        ((law.carrier child).«from» (.ctor ref args))]
      ((SMT.model fo
        (canonicalModel source)).bool
        true) := by
  simpa [SMT.model_bool, boolValue] using
    test_apply law represented ref (.ctor ref args)

/-- SMT constructor typing is the generic typed-symbol theorem,
specialized through the declaration representation. -/
theorem ctor_has_type {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    Crush.SMT.SymbolHasType
      (SMT.model fo
        (canonicalModel source))
      (.symb (data.name (.ctor child ref.index)))
      (ctorDecl (block := block) data child ref.index ctor).argSorts
      (dataSort data child) := by
  have typed := SMT.symbol_has_type fo
    (canonicalModel source)
    (.sourceConstant (symbols.ctor ref))
  rw [represented.ctor_ident ref] at typed
  simpa [raw_ctor_argSorts, fieldSort_eq represented, CtorDecl.ty,
    sourceDecl_fields, represented.sort_eq child,
    Function.comp_def] using typed

/-- Invert a native constructor application in the shared graph. -/
theorem ctor_apply_inv {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor)
    {values : List (SMT.Value
      (canonicalModel source))}
    {output : SMT.Value
      (canonicalModel source)}
    (typed : Crush.SMT.ValuesTyped
      (SMT.model fo
        (canonicalModel source))
      (ctorDecl (block := block) data child ref.index ctor).argSorts values)
    (applied : (SMT.model fo
      (canonicalModel source)).apply
      (.symb (data.name (.ctor child ref.index))) values output) :
    ∃ args : Args block source.Base ctor.fields,
      values = argValues law args ∧
      output = .typed (.base child.decl.sort)
        ((law.carrier child).«from» (.ctor ref args)) := by
  have fieldsTyped : Crush.SMT.ValuesTyped
      (SMT.model fo
        (canonicalModel source))
      (ctor.fields.map fun field : FieldDecl arity =>
        fo.sort (field.fo block)) values := by
    simpa [raw_ctor_argSorts, fieldSort_eq represented] using typed
  obtain ⟨args, rfl⟩ := typed_args law fo fieldsTyped
  let expected : SMT.Value
      (canonicalModel source) :=
    .typed (.base child.decl.sort)
      ((law.carrier child).«from» (.ctor ref args))
  have expectedApply := ctor_apply law represented ref args
  have argsTyped : Crush.SMT.ValuesTyped
      (SMT.model fo
        (canonicalModel source))
      (ctorDecl (block := block) data child ref.index ctor).argSorts
      (argValues law args) := by
    simpa [raw_ctor_argSorts, fieldSort_eq represented] using
      (argValues_typed law (fo := fo) args)
  obtain ⟨chosen, chosenTyped, chosenApply, unique⟩ :=
    ctor_has_type law represented ref (argValues law args)
      argsTyped
  have outputEq := unique output applied
  have expectedEq := unique expected expectedApply
  exact ⟨args, rfl, outputEq.trans expectedEq.symm⟩

/-- Canonical constructors are total, typed, and injective in the shared raw
model. -/
theorem ctor_holds {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    Crush.SMT.ConstructorHolds
      (SMT.model fo
        (canonicalModel source))
      (dataSort data child)
      (ctorDecl (block := block) data child ref.index ctor) := by
  constructor
  · exact ctor_has_type law represented ref
  · intro leftArgs rightArgs leftResult rightResult
      leftApply rightApply resultEq
    obtain ⟨left, leftArgsEq, leftResultEq⟩ :=
      ctor_apply_inv law represented ref leftApply.1 leftApply.2
    obtain ⟨right, rightArgsEq, rightResultEq⟩ :=
      ctor_apply_inv law represented ref rightApply.1 rightApply.2
    have valueEq :
        (Value.typed (.base child.decl.sort)
          ((law.carrier child).«from» (.ctor ref left)) :
          SMT.Value
            (canonicalModel source)) =
        .typed (.base child.decl.sort)
          ((law.carrier child).«from» (.ctor ref right)) := by
      rw [← leftResultEq, ← rightResultEq, resultEq]
    have sourceEq :
        (law.carrier child).«from» (.ctor ref left) =
          (law.carrier child).«from» (.ctor ref right) :=
      eq_of_heq (Value.typed.inj valueEq).2
    have coreEq := congrArg (law.carrier child).to sourceEq
    simp only [(law.carrier child).right_inv] at coreEq
    have argsEq := Datatype.ctor_inj ref coreEq
    rw [leftArgsEq, rightArgsEq, argsEq]

theorem sel_has_type {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    Crush.SMT.SymbolHasType
      (SMT.model fo
        (canonicalModel source))
      (.symb (data.name (.sel child ctorRef.index fieldRef.index)))
      [dataSort data child]
      (fieldSort (block := block) data field.sort) := by
  have typed := SMT.symbol_has_type fo
    (canonicalModel source)
    (.sourceConstant (symbols.sel ctorRef fieldRef))
  rw [represented.sel_ident ctorRef fieldRef] at typed
  cases field with
  | mk name sort =>
      cases sort with
      | base base =>
        simpa [Defunctionalization.sourceDecl,
          FieldDecl.ty, FieldSort.ty, FieldDecl.fo, FieldSort.fo,
          FO.FOSort.ofTy,
          fieldSort, represented.base_eq base, represented.sort_eq child,
          Function.comp_def] using typed
      | data fieldData =>
        change Crush.SMT.SymbolHasType _ _ [dataSort data child]
          (dataSort data fieldData)
        rw [← represented.sort_eq child, ← represented.sort_eq fieldData]
        simpa [Defunctionalization.sourceDecl,
          FieldDecl.ty, FieldSort.ty, FieldDecl.fo, FieldSort.fo,
          FO.FOSort.ofTy, DataRef.decl, fieldSort,
          Function.comp_def] using typed

/-- All selectors emitted for a constructor are total and recover their own
constructor field. -/
theorem sel_holds {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) :
    Crush.SMT.SelectorsHold
      (SMT.model fo
        (canonicalModel source))
      (dataSort data child)
      (ctorDecl (block := block) data child ctorRef.index ctor) := by
  intro index name resultSort lookup
  have rawBounds : index <
      (ctorDecl (block := block) data child ctorRef.index ctor).selDecls.size :=
    (Array.getElem?_eq_some_iff.mp lookup).1
  have inBounds : index < ctor.fields.length := by
    simpa [ctorDecl] using rawBounds
  let field := ctor.fields[index]
  let fieldRef : FieldRef ctor field := Datatype.Ref.ofIdx ctor.fields index inBounds
  have indexEq : fieldRef.index = index :=
    Datatype.Ref.index_ofIdx ctor.fields index inBounds
  have canonical := sel_get data ctorRef fieldRef
  rw [indexEq, lookup] at canonical
  have pairEq := Option.some.inj canonical
  cases pairEq
  constructor
  · simpa [indexEq] using sel_has_type law represented ctorRef fieldRef
  · intro arguments result selected ctorApplied selectedAt
    obtain ⟨args, argumentsEq, resultEq⟩ :=
      ctor_apply_inv law represented ctorRef ctorApplied.1 ctorApplied.2
    have canonicalGet := argValues_get law args fieldRef
    rw [indexEq] at canonicalGet
    rw [argumentsEq] at selectedAt
    have selectedEq := Option.some.inj (selectedAt.symm.trans canonicalGet)
    rw [resultEq, selectedEq]
    simpa [indexEq] using sel_apply_ctor law represented ctorRef fieldRef args

theorem test_has_type {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    Crush.SMT.SymbolHasType
      (SMT.model fo
        (canonicalModel source))
      (ctorDecl (block := block) data child ref.index ctor).tester
      [dataSort data child] Crush.SMT.boolSort := by
  have typed := SMT.symbol_has_type fo
    (canonicalModel source)
    (.sourceConstant (symbols.test ref))
  rw [represented.test_ident ref] at typed
  simpa [Crush.SMT.CtorDecl.tester, ctorDecl,
    Defunctionalization.sourceDecl,
    represented.sort_eq child, fo.bool_eq, Function.comp_def] using typed

theorem test_apply_ne {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {leftCtor rightCtor : CtorDecl arity}
    (leftRef : CtorRef block child leftCtor)
    (rightRef : CtorRef block child rightCtor)
    (different : leftRef.index ≠ rightRef.index)
    (args : Args block source.Base rightCtor.fields) :
    (SMT.model fo
      (canonicalModel source)).apply
      (.indexed "is" #[.inl (data.name (.ctor child leftRef.index))])
      [.typed (.base child.decl.sort)
        ((law.carrier child).«from» (.ctor rightRef args))]
      ((SMT.model fo
        (canonicalModel source)).bool
        false) := by
  have applied := test_apply law represented leftRef (.ctor rightRef args)
  have rejected : IsCtor leftRef (.ctor rightRef args) = False := by
    apply propext
    exact ⟨fun holds => test_ne leftRef rightRef different args holds,
      False.elim⟩
  simpa [SMT.model_bool, boolValue, rejected] using applied

theorem test_holds {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    Crush.SMT.TesterHolds
      (SMT.model fo
        (canonicalModel source))
      (dataSort data child)
      (ctorDecl (block := block) data child ref.index ctor) := by
  constructor
  · exact test_has_type law represented ref
  · intro arguments result applied
    obtain ⟨args, argumentsEq, resultEq⟩ :=
      ctor_apply_inv law represented ref applied.1 applied.2
    rw [resultEq]
    exact test_apply_ctor law represented ref args

/-- Every raw constructor emitted by the native declaration satisfies its
constructor, selector, and tester laws in the shared model. -/
theorem ctor_laws {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {sort : Crush.SMT.SSort} {rawCtor : Crush.SMT.CtorDecl}
    (member : (sort, rawCtor) ∈
      Crush.SMT.datatypeCtors (entries block data)) :
    Crush.SMT.ConstructorHolds
        (SMT.model fo
          (canonicalModel source))
        sort rawCtor ∧
      Crush.SMT.SelectorsHold
        (SMT.model fo
          (canonicalModel source))
        sort rawCtor ∧
      Crush.SMT.TesterHolds
        (SMT.model fo
          (canonicalModel source))
        sort rawCtor := by
  obtain ⟨child, ctor, ref, rfl, rfl⟩ := raw_ctor_ref data member
  exact ⟨ctor_holds law represented ref,
    sel_holds law represented ref, test_holds law represented ref⟩

/-- Results of distinct raw constructors are distinct in the shared model. -/
theorem ctor_disjoint {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {leftSort rightSort : Crush.SMT.SSort}
    {leftCtor rightCtor : Crush.SMT.CtorDecl}
    (leftMem : (leftSort, leftCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    (rightMem : (rightSort, rightCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    (different : leftCtor.name ≠ rightCtor.name)
    {leftArgs rightArgs : List (SMT.Value
      (canonicalModel source))}
    {leftResult rightResult : SMT.Value
      (canonicalModel source)}
    (leftApply : Crush.SMT.CtorApplies
      (SMT.model fo
        (canonicalModel source))
      leftCtor leftArgs leftResult)
    (rightApply : Crush.SMT.CtorApplies
      (SMT.model fo
        (canonicalModel source))
      rightCtor rightArgs rightResult) :
    leftResult ≠ rightResult := by
  obtain ⟨leftData, leftDecl, leftRef, rfl, rfl⟩ :=
    raw_ctor_ref data leftMem
  obtain ⟨rightData, rightDecl, rightRef, rfl, rfl⟩ :=
    raw_ctor_ref data rightMem
  obtain ⟨left, leftArgsEq, leftResultEq⟩ :=
    ctor_apply_inv law represented leftRef leftApply.1 leftApply.2
  obtain ⟨right, rightArgsEq, rightResultEq⟩ :=
    ctor_apply_inv law represented rightRef rightApply.1 rightApply.2
  intro resultEq
  have valueEq :
      (Value.typed (.base leftData.decl.sort)
        ((law.carrier leftData).«from» (.ctor leftRef left)) :
        SMT.Value
          (canonicalModel source)) =
      .typed (.base rightData.decl.sort)
        ((law.carrier rightData).«from» (.ctor rightRef right)) := by
    rw [← leftResultEq, ← rightResultEq, resultEq]
  have sortEq := (Value.typed.inj valueEq).1
  have baseEq : leftData.decl.sort = rightData.decl.sort := by
    injection sortEq
  have dataEq := represented.wf.blockWF.data_eq baseEq
  subst rightData
  have sourceEq :
      (law.carrier leftData).«from» (.ctor leftRef left) =
        (law.carrier leftData).«from» (.ctor rightRef right) :=
    eq_of_heq (Value.typed.inj valueEq).2
  have coreEq := congrArg (law.carrier leftData).to sourceEq
  simp only [(law.carrier leftData).right_inv] at coreEq
  have indexNe : leftRef.index ≠ rightRef.index := by
    intro indexEq
    apply different
    simp [ctorDecl, indexEq]
  exact ctor_ne leftRef rightRef indexNe left right coreEq

/-- A tester rejects values built by another constructor of the same datatype. -/
theorem test_disjoint {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {sort : Crush.SMT.SSort} {leftCtor rightCtor : Crush.SMT.CtorDecl}
    (leftMem : (sort, leftCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    (rightMem : (sort, rightCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    (different : leftCtor.name ≠ rightCtor.name)
    {arguments : List (SMT.Value
      (canonicalModel source))}
    {result : SMT.Value
      (canonicalModel source)}
    (applied : Crush.SMT.CtorApplies
      (SMT.model fo
        (canonicalModel source))
      rightCtor arguments result) :
    (SMT.model fo
      (canonicalModel source)).apply
      leftCtor.tester [result]
      ((SMT.model fo
        (canonicalModel source)).bool
        false) := by
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
    ctor_apply_inv law represented rightRef applied.1 applied.2
  rw [resultEq]
  simpa [Crush.SMT.CtorDecl.tester, ctorDecl] using
    test_apply_ne law represented leftRef rightRef indexNe args

/-- Every value inhabiting a declared datatype sort is built by one constructor
from that exact native declaration. -/
theorem exhaustive {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {name : String} {count : Nat} {decl : Crush.SMT.DatatypeDecl}
    (member : (name, count, decl) ∈ (entries block data).toList)
    (value : SMT.Value
      (canonicalModel source))
    (typed : (SMT.model fo
      (canonicalModel source)).inSort
      (Crush.SMT.datatypeSort name) value) :
    ∃ ctor, ctor ∈ decl.ctors.toList ∧
      ∃ arguments, Crush.SMT.CtorApplies
        (SMT.model fo
          (canonicalModel source))
        ctor arguments value := by
  obtain ⟨child, nameEq, countEq, declEq⟩ := raw_entry_ref block data member
  subst name
  subst count
  subst decl
  change (SMT.model fo
    (canonicalModel source)).inSort
    (dataSort data child) value at typed
  rw [← represented.sort_eq child] at typed
  obtain ⟨sourceValue, rfl⟩ := Value.exists_typed_of_inSort
    fo (.base child.decl.sort) _ typed
  let core := (law.carrier child).to sourceValue
  obtain ⟨ctor, ref, args, coreEq⟩ := ctor_cases core
  have sourceEq : sourceValue =
      (law.carrier child).«from» (.ctor ref args) := by
    calc
      sourceValue = (law.carrier child).«from» core := by
        exact ((law.carrier child).left_inv sourceValue).symm
      _ = (law.carrier child).«from» (.ctor ref args) :=
        congrArg (law.carrier child).«from» coreEq
  let rawCtor := ctorDecl (block := block) data child ref.index ctor
  refine ⟨rawCtor, ?_, argValues law args, ?_, ?_⟩
  · change rawCtor ∈ (block.decl child).ctors.mapIdx fun index ctor =>
      ctorDecl (block := block) data child index ctor
    exact Datatype.Ref.mem_mapIdx ref fun index ctor =>
      ctorDecl (block := block) data child index ctor
  · simpa [rawCtor, raw_ctor_argSorts, fieldSort_eq represented] using
      (argValues_typed law (fo := fo) args)
  · rw [sourceEq]
    exact ctor_apply law represented ref args

/-- Height of a datatype value inside the one shared raw SMT universe. Values
at ordinary sorts have rank zero. The datatype sort is recovered from its
typed base-sort identity, rather than from a parallel raw-value tag. -/
noncomputable def rank {source : Model signature}
    (law : IsFreeDatatypeModel symbols source) :
    SMT.Value
      (canonicalModel source) →
      Nat
  | .typed (.base sort) value =>
      if present : ∃ child : DataRef block, child.decl.sort = sort then
        let child := Classical.choose present
        let equal := Classical.choose_spec present
        ((law.carrier child).to (equal.symm ▸ value)).height
      else 0
  | _ => 0

private theorem rank_cast {source : Model signature}
    (law : IsFreeDatatypeModel symbols source) {selected child : DataRef block}
    (dataEq : selected = child)
    (sortEq : selected.decl.sort = child.decl.sort)
    (value : Val block source.Base child) :
    ((law.carrier selected).to
      (sortEq.symm ▸ (law.carrier child).«from» value)).height =
      value.height := by
  subst selected
  have proofEq : sortEq = rfl := Subsingleton.elim _ _
  rw [proofEq]
  exact congrArg Val.height ((law.carrier child).right_inv value)

/-- On a represented datatype carrier, the shared raw rank is exactly the
height of the canonical finite constructor tree. -/
@[simp] theorem rank_data {source : Model signature}
    (law : IsFreeDatatypeModel symbols source) (wf : block.WF)
    (child : DataRef block) (value : Val block source.Base child) :
    rank law (.typed (.base child.decl.sort)
      ((law.carrier child).«from» value)) = value.height := by
  rw [rank]
  split
  next present =>
    let selected := Classical.choose present
    have sortEq : selected.decl.sort = child.decl.sort :=
      Classical.choose_spec present
    have selectedEq : selected = child := wf.data_eq sortEq
    have chosenEq : Classical.choose present = child := selectedEq
    exact rank_cast law chosenEq (Classical.choose_spec present) value
  next absent =>
    exact False.elim (absent ⟨child, rfl⟩)

/-- A field whose encoded sort is declared by this SMT datatype block was
intrinsically
classified as recursive. Structural well-formedness rules out an external
base field merely reusing a datatype sort identity. -/
theorem field_data_ref
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {parent : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block parent ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) (child : DataRef block)
    (encoded : fieldSort (block := block) data field.sort =
      dataSort data child) :
    ∃ name, ∃ dataRef : FieldRef ctor
        { name := name, sort := .data child },
      dataRef.index = fieldRef.index := by
  cases field with
  | mk name sort =>
      cases sort with
      | base base =>
          have rawEq : fo.sort (.base base) =
              fo.sort (.base child.decl.sort) :=
            (represented.base_eq base).symm.trans
              (encoded.trans (represented.sort_eq child).symm)
          have intrinsicEq := fo.sort_injective rawEq
          have baseEq : base = child.decl.sort := by injection intrinsicEq
          exact False.elim
            (represented.wf.blockWF.base_ne_data ctorRef fieldRef rfl child baseEq)
      | data fieldData =>
          have dataEq : fieldData = child :=
            dataSort_injective represented.wf.names encoded
          subst fieldData
          exact ⟨name, fieldRef, rfl⟩

/-- Every recursive constructor argument strictly decreases the shared raw
rank. This is the well-foundedness clause required by native SMT datatypes. -/
theorem rank_lt {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data)
    {sort : Crush.SMT.SSort} {rawCtor : Crush.SMT.CtorDecl}
    (member : (sort, rawCtor) ∈
      Crush.SMT.datatypeCtors (entries block data))
    {arguments : List (SMT.Value
      (canonicalModel source))}
    {result : SMT.Value
      (canonicalModel source)}
    (applied : Crush.SMT.CtorApplies
      (SMT.model fo
        (canonicalModel source))
      rawCtor arguments result)
    (index : Nat) (rawFieldSort : Crush.SMT.SSort)
    (rawFieldValue : SMT.Value
      (canonicalModel source))
    (sortAt : rawCtor.argSorts[index]? = some rawFieldSort)
    (valueAt : arguments[index]? = some rawFieldValue)
    (recursive : rawFieldSort ∈
      Crush.SMT.datatypeSorts (entries block data)) :
    rank law rawFieldValue < rank law result := by
  obtain ⟨parent, ctor, ctorRef, rfl, rfl⟩ := raw_ctor_ref data member
  obtain ⟨args, argumentsEq, resultEq⟩ :=
    ctor_apply_inv law represented ctorRef applied.1 applied.2
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
  let childValue : Val block source.Base child := args.get dataFieldRef
  rw [argumentsEq] at valueAt
  have canonicalValue := argValues_get law args dataFieldRef
  rw [dataIndex] at canonicalValue
  have valueEq := Option.some.inj (valueAt.symm.trans canonicalValue)
  rw [resultEq, valueEq]
  simp only [fieldValue]
  rw [rank_data law represented.wf.blockWF]
  change rank law (.typed (.base child.decl.sort)
    ((law.carrier child).«from» childValue)) < _
  rw [rank_data law represented.wf.blockWF]
  simpa [childValue] using
    Args.get_height_lt_ctor args dataFieldRef ctorRef rfl

/-- The ordinary SMT model induced from a free-datatype source model satisfies
every semantic law of one emitted SMT datatype block. -/
theorem data_hold {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data) :
    Crush.SMT.DatatypesHold
      (SMT.model fo
      (canonicalModel source))
      (entries block data) := by
  refine ⟨supported represented.wf law.productive, ?_, ?_, ?_, ?_, rank law, ?_⟩
  · intro sort ctor member
    exact ctor_laws law represented member
  · intro leftSort leftCtor rightSort rightCtor leftMem rightMem different
      leftArgs leftResult rightArgs rightResult leftApply rightApply
    exact ctor_disjoint law represented leftMem rightMem different
      leftApply rightApply
  · intro name count decl member value typed
    exact exhaustive law represented member value typed
  · intro sort leftCtor rightCtor leftMem rightMem different arguments result
      applied
    exact test_disjoint law represented leftMem rightMem different applied
  · intro sort ctor member arguments result applied index fieldSort fieldValue
      sortAt valueAt recursive
    exact rank_lt law represented member applied index fieldSort fieldValue
      sortAt valueAt recursive

/-- One emitted native `declare-datatypes` command is satisfied in the same
raw SMT model used for all ordinary symbols and formulas. -/
theorem command_sound {source : Model signature}
    (law : IsFreeDatatypeModel symbols source)
    {fo : SMT.Encoding (Symbol signature)}
    {data : BlockEncoding arity} (represented : Representation block symbols fo data) :
    (SMT.model fo
      (canonicalModel source)).SatisfiesCommand
      (command block data) := by
  exact ⟨supported represented.wf law.productive, data_hold law represented⟩

/-- Every command described by a datatype environment is valid in the one
shared raw model. -/
theorem Represented.commands_valid {source : Model signature}
    {fo : SMT.Encoding (Symbol signature)}
    {env : Datatype.Env signature}
    (represented : Represented fo env)
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source env) :
    SMT.model fo
        (canonicalModel source)
      ⊨ₛᶜ represented.commands := by
  induction represented with
  | nil =>
      exact satisfiesCommands_empty _
  | cons head tail ih =>
      cases freeDataModel with
      | cons headLaw tailLaw =>
          rw [Represented.commands, satisfiesCommands_append]
          constructor
          · let raw := SMT.model fo
                (canonicalModel source)
            simpa using satisfiesCommands_push raw
              (satisfiesCommands_empty raw)
              (command_sound headLaw head)
          · exact ih tailLaw

/-- Exact environment representation discharges the SMT-datatype-command premise of
the generic FO-to-SMT soundness theorem. -/
theorem EnvRepresentation.datatypeCommands_valid {source : Model signature}
    {fo : SMT.Encoding (Symbol signature)}
    {env : Datatype.Env signature}
    (represented : EnvRepresentation fo env)
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source env) :
    SMT.model fo
        (canonicalModel source)
      ⊨ₛᶜ fo.nativeCommands := by
  rw [represented.datatypeCommands_eq]
  exact represented.blocks.commands_valid freeDataModel

end Crush.Metatheory.SMT.Datatype
