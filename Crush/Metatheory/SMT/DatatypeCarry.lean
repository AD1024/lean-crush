import Crush.Metatheory.SMT.DatatypeLifted
import Crush.Metatheory.SMT.Int

/-!
# Carrying native datatype laws through later blocks

Dependency blocks are installed from dependencies to users. A later block wraps
the carriers of an earlier native command but, by dependency order, does not own
any sort used by that command. This file gives that external wrapping one small
raw-value interface; command preservation can then be proved once instead of
rebuilding datatype semantics for every suffix of the environment.
-/

namespace Crush.Metatheory.SMT.Datatype.Native

open Crush.Metatheory.Datatype
open Crush.Metatheory.Defunctionalization.Flattened
open Crush.Metatheory.Datatype.Env (Lawful BlocksWF liftFrom)

/-- One actual dependency-fold extension step. -/
structure Step {signature : Signature}
    (source : FO.FamilyModel (Symbol signature)) where
  arity : Nat
  block : Block arity
  symbols : Symbols signature block
  law : FamilyLawful symbols.native source
  wf : block.WF
  productive : Productive block
  prior : Lifted source

namespace Step

variable {signature : Signature}
variable {source : FO.FamilyModel (Symbol signature)}

/-- The target produced by this exact fold step. -/
noncomputable abbrev target (step : Step source) :
    FO.FamilyModel (Symbol signature) :=
  step.law.extend step.wf step.productive step.prior.target
    step.prior.relation step.prior.models

/-- Embed one prior raw value into a later block. At an external sort this is
the genuine carrier isomorphism; the fallback branch only totalizes the map and
is never observed by an externally typed command. -/
noncomputable def wrap (step : Step source) :
    SMT.Value step.prior.target → SMT.Value step.target
  | .typed sort value => by
      classical
      exact if external : BaseLift.External step.block sort then
        .typed sort (BaseLift.wrapWith step.productive external value)
      else
        .typed sort (SMT.defaultValue step.target.carriers sort)
  | .raw sort => .raw sort

/-- Read a later raw value back into the preceding model. -/
noncomputable def unwrap (step : Step source) :
    SMT.Value step.target → SMT.Value step.prior.target
  | .typed sort value => by
      classical
      exact if external : BaseLift.External step.block sort then
        .typed sort (BaseLift.unwrap step.productive external value)
      else
        .typed sort (SMT.defaultValue step.prior.target.carriers sort)
  | .raw sort => .raw sort

@[simp] theorem wrap_typed (step : Step source) {sort : FO.FOSort}
    (external : BaseLift.External step.block sort)
    (value : sort.Denote step.prior.target.carriers) :
    step.wrap (.typed sort value) =
      .typed sort (BaseLift.wrapWith step.productive external value) := by
  simp [wrap, external]

@[simp] theorem unwrap_typed (step : Step source) {sort : FO.FOSort}
    (external : BaseLift.External step.block sort)
    (value : sort.Denote step.target.carriers) :
    step.unwrap (.typed sort value) =
      .typed sort (BaseLift.unwrap step.productive external value) := by
  simp [unwrap, external]

@[simp] theorem unwrap_wrap (step : Step source) {sort : FO.FOSort}
    (external : BaseLift.External step.block sort)
    (value : sort.Denote step.prior.target.carriers) :
    step.unwrap (step.wrap (.typed sort value)) = .typed sort value := by
  simp [external]

@[simp] theorem wrap_unwrap (step : Step source) {sort : FO.FOSort}
    (external : BaseLift.External step.block sort)
    (value : sort.Denote step.target.carriers) :
    step.wrap (step.unwrap (.typed sort value)) = .typed sort value := by
  rw [unwrap_typed step external, wrap_typed step external]
  apply congrArg (SMT.Value.typed sort)
  cases sort with
  | bool => rfl
  | fn domain codomain => rfl
  | base sort => exact BaseLift.external_asExternal sort external value

private theorem wrap_typed_exists (step : Step source) (sort : FO.FOSort)
    (value : sort.Denote step.prior.target.carriers) :
    ∃ output, step.wrap (.typed sort value) = .typed sort output := by
  simp only [wrap]
  split <;> exact ⟨_, rfl⟩

private theorem unwrap_typed_exists (step : Step source) (sort : FO.FOSort)
    (value : sort.Denote step.target.carriers) :
    ∃ output, step.unwrap (.typed sort value) = .typed sort output := by
  simp only [unwrap]
  split <;> exact ⟨_, rfl⟩

theorem wrap_inSort (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {sort : SMT.SSort}
    {value : SMT.Value step.prior.target}
    (typed : (SMT.model fo step.prior.target).inSort sort value) :
    (SMT.model fo step.target).inSort sort (step.wrap value) := by
  cases value with
  | typed intrinsic value =>
      obtain ⟨output, equal⟩ := step.wrap_typed_exists intrinsic value
      rw [equal]
      exact typed
  | raw rawSort =>
      change rawSort = sort ∧ ∀ intrinsic, fo.sort intrinsic ≠ rawSort at typed ⊢
      exact typed

theorem inSort_of_wrap (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {sort : SMT.SSort}
    {value : SMT.Value step.prior.target}
    (typed : (SMT.model fo step.target).inSort sort (step.wrap value)) :
    (SMT.model fo step.prior.target).inSort sort value := by
  cases value with
  | typed intrinsic value =>
      obtain ⟨output, equal⟩ := step.wrap_typed_exists intrinsic value
      rw [equal] at typed
      exact typed
  | raw rawSort =>
      change rawSort = sort ∧ ∀ intrinsic, fo.sort intrinsic ≠ rawSort at typed ⊢
      exact typed

theorem unwrap_inSort (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {sort : SMT.SSort}
    {value : SMT.Value step.target}
    (typed : (SMT.model fo step.target).inSort sort value) :
    (SMT.model fo step.prior.target).inSort sort (step.unwrap value) := by
  cases value with
  | typed intrinsic value =>
      obtain ⟨output, equal⟩ := step.unwrap_typed_exists intrinsic value
      rw [equal]
      exact typed
  | raw rawSort =>
      change rawSort = sort ∧ ∀ intrinsic, fo.sort intrinsic ≠ rawSort at typed ⊢
      exact typed

theorem wrap_injective (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {sort : FO.FOSort}
    (external : BaseLift.External step.block sort)
    {left right : SMT.Value step.prior.target}
    (leftTyped : (SMT.model fo step.prior.target).inSort (fo.sort sort) left)
    (rightTyped : (SMT.model fo step.prior.target).inSort (fo.sort sort) right)
    (equal : step.wrap left = step.wrap right) : left = right := by
  obtain ⟨leftValue, rfl⟩ :=
    SMT.Value.exists_typed_of_inSort fo sort left leftTyped
  obtain ⟨rightValue, rfl⟩ :=
    SMT.Value.exists_typed_of_inSort fo sort right rightTyped
  have unwrapped := congrArg step.unwrap equal
  simpa [external] using unwrapped

/-- Decoding a wrapped, well-typed argument and then crossing the external
carrier isomorphism recovers the preceding argument. -/
theorem unwrap_decode_wrap (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {sort : FO.FOSort}
    (external : BaseLift.External step.block sort)
    (value : SMT.Value step.prior.target)
    (typed : (SMT.model fo step.prior.target).inSort (fo.sort sort) value) :
    BaseLift.unwrap step.productive external
        (SMT.decode step.target sort (step.wrap value)) =
      SMT.decode step.prior.target sort value := by
  obtain ⟨input, rfl⟩ := SMT.Value.exists_typed_of_inSort fo sort value typed
  simp [external]

theorem values_wrap (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) :
    ∀ {sorts : List SMT.SSort}
      {values : List (SMT.Value step.prior.target)},
      Crush.SMT.ValuesTyped (SMT.model fo step.prior.target) sorts values →
      Crush.SMT.ValuesTyped (SMT.model fo step.target)
        sorts (values.map step.wrap)
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (step.wrap_inSort fo head) (step.values_wrap fo tail)

theorem values_unwrap (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) :
    ∀ {sorts : List SMT.SSort}
      {values : List (SMT.Value step.target)},
      Crush.SMT.ValuesTyped (SMT.model fo step.target) sorts values →
      Crush.SMT.ValuesTyped (SMT.model fo step.prior.target)
        sorts (values.map step.unwrap)
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (step.unwrap_inSort fo head) (step.values_unwrap fo tail)

private theorem getElem?_map_some {α β : Type} (f : α → β)
    (values : List α) (index : Nat) (value : α)
    (atIndex : values[index]? = some value) :
    (values.map f)[index]? = some (f value) := by
  induction values generalizing index with
  | nil => simp at atIndex
  | cons head tail ih =>
      cases index with
      | zero =>
          have equal : head = value := by simpa using atIndex
          simp [equal]
      | succ index => exact ih index (by simpa using atIndex)

theorem values_typed_at {model : Crush.SMT.Model}
    {sorts : List Crush.SMT.SSort} {values : List model.Value}
    (typed : Crush.SMT.ValuesTyped model sorts values)
    (index : Nat) {sort : Crush.SMT.SSort} {value : model.Value}
    (sortAt : sorts[index]? = some sort)
    (valueAt : values[index]? = some value) : model.inSort sort value := by
  induction typed generalizing index with
  | nil => simp at sortAt
  | cons head tail ih =>
      cases index with
      | zero => simp_all
      | succ index =>
          exact ih index (by simpa using sortAt) (by simpa using valueAt)

theorem wrap_unwrap_of_inSort (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {sort : FO.FOSort}
    (external : BaseLift.External step.block sort)
    (value : SMT.Value step.target)
    (typed : (SMT.model fo step.target).inSort (fo.sort sort) value) :
    step.wrap (step.unwrap value) = value := by
  obtain ⟨input, rfl⟩ := SMT.Value.exists_typed_of_inSort fo sort value typed
  exact step.wrap_unwrap external input

theorem values_wrap_unwrap (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) :
    ∀ {sorts : List FO.FOSort}
      (external : ∀ sort ∈ sorts, BaseLift.External step.block sort)
      {values : List (SMT.Value step.target)},
      Crush.SMT.ValuesTyped (SMT.model fo step.target)
        (sorts.map fo.sort) values →
      (values.map step.unwrap).map step.wrap = values
  | [], external, values, typed => by
      have equal := Crush.SMT.ValuesTyped.eq_nil (by simpa using typed)
      subst values
      rfl
  | sort :: sorts, external, values, typed => by
      have normalized : Crush.SMT.ValuesTyped (SMT.model fo step.target)
          (fo.sort sort :: sorts.map fo.sort) values := by
        simpa using typed
      obtain ⟨head, tail, rfl, headTyped, tailTyped⟩ :=
        normalized.exists_cons
      simp only [List.map]
      rw [step.wrap_unwrap_of_inSort fo (external sort (by simp)) head
        headTyped]
      exact congrArg (head :: ·) (step.values_wrap_unwrap fo
        (fun other member => external other (by simp [member])) tailTyped)

/-- Applying a carried curried interpretation to wrapped typed arguments is
exactly the wrapped preceding result. -/
theorem applyValues_carry (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) :
    ∀ {arguments : List FO.FOSort} {result : FO.FOSort}
      (argumentsExternal : ∀ sort ∈ arguments,
        BaseLift.External step.block sort)
      (resultExternal : BaseLift.External step.block result)
      (function : FO.SymbolDenote step.prior.target.carriers arguments result)
      {values : List (SMT.Value step.prior.target)},
      Crush.SMT.ValuesTyped (SMT.model fo step.prior.target)
        (arguments.map fo.sort) values →
      SMT.applyValues step.target arguments
          (BaseLift.carry step.productive argumentsExternal resultExternal
            function)
          (values.map step.wrap) =
        BaseLift.wrapWith step.productive resultExternal
          (SMT.applyValues step.prior.target arguments function values)
  | [], _, argumentsExternal, resultExternal, function, values, typed => by
      have equal := Crush.SMT.ValuesTyped.eq_nil (by simpa using typed)
      subst values
      rfl
  | argument :: arguments, result, argumentsExternal, resultExternal,
      function, values, typed => by
      have normalized : Crush.SMT.ValuesTyped
          (SMT.model fo step.prior.target)
          (fo.sort argument :: arguments.map fo.sort) values := by
        simpa using typed
      obtain ⟨head, tail, rfl, headTyped, tailTyped⟩ :=
        normalized.exists_cons
      have decoded := step.unwrap_decode_wrap fo
        (argumentsExternal argument (by simp)) head headTyped
      dsimp only [target, Lifted.extend] at decoded
      dsimp only [target, Lifted.extend]
      simp only [List.map, SMT.applyValues, BaseLift.carry]
      rw [decoded]
      exact step.applyValues_carry fo
        (fun sort member => argumentsExternal sort (by simp [member]))
        resultExternal _ tailTyped

/-- Evidence that a symbol installed before `step` is carried unchanged rather
than being owned or freshly lifted by the later block. -/
structure Carries (step : Step source) {decl : FO.SymbolDecl}
    (symbol : Symbol signature decl) : Prop where
  unowned : ¬Nonempty (NativeRef step.symbols.native symbol)
  external : BaseLift.ExternalDecl step.block decl

/-- At a carried encoded symbol, applying wrapped typed arguments and wrapping
the result is equivalent to the preceding graph application. -/
theorem apply_wrap_iff (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {decl : FO.SymbolDecl}
    (symbol : Symbol signature decl) (carried : step.Carries symbol)
    (values : List (SMT.Value step.prior.target))
    (valuesTyped : Crush.SMT.ValuesTyped (SMT.model fo step.prior.target)
      (decl.args.map fo.sort) values)
    (output : SMT.Value step.prior.target) :
    (SMT.model fo step.target).apply (fo.ident symbol)
        (values.map step.wrap) (step.wrap output) ↔
      (SMT.model fo step.prior.target).apply (fo.ident symbol) values output := by
  have external := carried.external
  change (∀ sort ∈ decl.args, BaseLift.External step.block sort) ∧
    BaseLift.External step.block decl.result at external
  have symbolEq := step.law.extend_symbol_external step.wf step.productive
    step.prior.target step.prior.relation step.prior.models symbol
    carried.unowned external
  let expected : SMT.Value step.prior.target :=
    .typed decl.result
      (SMT.applyValues step.prior.target decl.args
        (step.prior.target.symbol symbol) values)
  have expectedTyped : (SMT.model fo step.prior.target).inSort
      (fo.sort decl.result) expected :=
    SMT.Value.inSort_typed (target := step.prior.target) fo decl.result
      (SMT.applyValues step.prior.target decl.args
        (step.prior.target.symbol symbol) values)
  have carriedEval := step.applyValues_carry fo external.1
    external.2 (step.prior.target.symbol symbol) valuesTyped
  dsimp only [target, Lifted.extend] at symbolEq carriedEval ⊢
  constructor
  · rintro ⟨otherDecl, otherSymbol, identEq, outputEq⟩
    have declEq := fo.ident_decl_injective symbol otherSymbol identEq
    subst otherDecl
    have otherEq := fo.ident_injective symbol otherSymbol identEq
    subst otherSymbol
    have wrapEq : step.wrap output = step.wrap expected := by
      rw [outputEq, symbolEq]
      simp only [expected]
      rw [step.wrap_typed external.2]
      exact congrArg (SMT.Value.typed decl.result) carriedEval
    have targetTyped : (SMT.model fo step.target).inSort
        (fo.sort decl.result) (step.wrap output) := by
      rw [outputEq]
      exact SMT.Value.inSort_typed (target := step.target) fo decl.result
        (SMT.applyValues step.target decl.args
          (step.target.symbol symbol) (values.map step.wrap))
    have outputTyped := step.inSort_of_wrap fo targetTyped
    have outputExpected := step.wrap_injective fo external.2
      outputTyped expectedTyped wrapEq
    subst output
    exact ⟨decl, symbol, rfl, rfl⟩
  · rintro ⟨otherDecl, otherSymbol, identEq, outputEq⟩
    have declEq := fo.ident_decl_injective symbol otherSymbol identEq
    subst otherDecl
    have otherEq := fo.ident_injective symbol otherSymbol identEq
    subst otherSymbol
    refine ⟨decl, symbol, rfl, ?_⟩
    rw [outputEq, symbolEq]
    rw [step.wrap_typed external.2]
    exact congrArg (SMT.Value.typed decl.result) carriedEval.symm

/-- Inverting a carried target application by external unwrapping yields the
exact preceding graph application. -/
theorem apply_unwrap (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {decl : FO.SymbolDecl}
    (symbol : Symbol signature decl) (carried : step.Carries symbol)
    (values : List (SMT.Value step.target))
    (valuesTyped : Crush.SMT.ValuesTyped (SMT.model fo step.target)
      (decl.args.map fo.sort) values)
    (output : SMT.Value step.target)
    (applied : (SMT.model fo step.target).apply
      (fo.ident symbol) values output) :
    (SMT.model fo step.prior.target).apply (fo.ident symbol)
      (values.map step.unwrap) (step.unwrap output) := by
  have external := carried.external
  change (∀ sort ∈ decl.args, BaseLift.External step.block sort) ∧
    BaseLift.External step.block decl.result at external
  rcases applied with ⟨otherDecl, otherSymbol, identEq, outputEq⟩
  have declEq := fo.ident_decl_injective symbol otherSymbol identEq
  subst otherDecl
  have otherEq := fo.ident_injective symbol otherSymbol identEq
  subst otherSymbol
  have outputTyped : (SMT.model fo step.target).inSort
      (fo.sort decl.result) output := by
    rw [outputEq]
    exact SMT.Value.inSort_typed (target := step.target) fo decl.result
      (SMT.applyValues step.target decl.args (step.target.symbol symbol) values)
  have valuesEq := step.values_wrap_unwrap fo external.1 valuesTyped
  have outputRoundtrip :=
    step.wrap_unwrap_of_inSort fo external.2 output outputTyped
  dsimp only [target, Lifted.extend] at valuesEq outputRoundtrip outputEq ⊢
  have baseApply : (SMT.model fo step.target).apply
      (fo.ident symbol) values output :=
    ⟨decl, symbol, rfl, outputEq⟩
  have mappedApply : (SMT.model fo step.target).apply (fo.ident symbol)
      ((values.map step.unwrap).map step.wrap)
      (step.wrap (step.unwrap output)) := by
    have argumentsApply := valuesEq.symm ▸ baseApply
    exact outputRoundtrip.symm ▸ argumentsApply
  exact (step.apply_wrap_iff fo symbol carried (values.map step.unwrap)
    (step.values_unwrap fo valuesTyped) (step.unwrap output)).mp mappedApply

/-- Every application at an encoded symbol returns a value of the symbol's
encoded result sort. -/
theorem apply_result_typed (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {decl : FO.SymbolDecl}
    (symbol : Symbol signature decl) (values : List (SMT.Value step.target))
    (output : SMT.Value step.target)
    (applied : (SMT.model fo step.target).apply
      (fo.ident symbol) values output) :
    (SMT.model fo step.target).inSort (fo.sort decl.result) output := by
  rcases applied with ⟨otherDecl, otherSymbol, identEq, outputEq⟩
  have declEq := fo.ident_decl_injective symbol otherSymbol identEq
  subst otherDecl
  have otherEq := fo.ident_injective symbol otherSymbol identEq
  subst otherSymbol
  rw [outputEq]
  exact SMT.Value.inSort_typed (target := step.target) fo decl.result
    (SMT.applyValues step.target decl.args (step.target.symbol symbol) values)

/-- Totality, result typing, and graph uniqueness are preserved when an
external symbol is carried through a later block. -/
theorem hasType_carry (step : Step source)
    (fo : SMT.Encoding (Symbol signature)) {decl : FO.SymbolDecl}
    (symbol : Symbol signature decl) (carried : step.Carries symbol)
    (typed : Crush.SMT.SymbolHasType (SMT.model fo step.prior.target)
      (fo.ident symbol) (decl.args.map fo.sort) (fo.sort decl.result)) :
    Crush.SMT.SymbolHasType (SMT.model fo step.target)
      (fo.ident symbol) (decl.args.map fo.sort) (fo.sort decl.result) := by
  intro values valuesTyped
  have external := carried.external
  change (∀ sort ∈ decl.args, BaseLift.External step.block sort) ∧
    BaseLift.External step.block decl.result at external
  let oldValues := values.map step.unwrap
  have oldTyped : Crush.SMT.ValuesTyped (SMT.model fo step.prior.target)
      (decl.args.map fo.sort) oldValues := step.values_unwrap fo valuesTyped
  obtain ⟨oldOutput, oldOutputTyped, oldApply, oldUnique⟩ :=
    typed oldValues oldTyped
  let output := step.wrap oldOutput
  refine ⟨output, step.wrap_inSort fo oldOutputTyped, ?_, ?_⟩
  · have mappedApply := (step.apply_wrap_iff fo symbol carried oldValues
      oldTyped oldOutput).mpr oldApply
    have valuesEq : oldValues.map step.wrap = values := by
      exact step.values_wrap_unwrap fo external.1 valuesTyped
    exact valuesEq ▸ mappedApply
  · intro other otherApply
    have oldOtherApply := step.apply_unwrap fo symbol carried values
      valuesTyped other otherApply
    have oldEq := oldUnique (step.unwrap other) oldOtherApply
    have otherTyped := step.apply_result_typed fo symbol values other otherApply
    calc
      other = step.wrap (step.unwrap other) :=
        (step.wrap_unwrap_of_inSort fo external.2 other otherTyped).symm
      _ = step.wrap oldOutput := congrArg step.wrap oldEq
      _ = output := rfl

/-- Exact evidence that every sort and native symbol of an earlier represented
block is external to, and unowned by, a later dependency step. -/
structure CarriedBy
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (step : Step source) : Prop where
  sort : ∀ child : DataRef oldBlock,
    BaseLift.External step.block (.base child.decl.sort)
  ctor : ∀ {child : DataRef oldBlock} {ctor : CtorDecl oldArity}
    (ref : CtorRef oldBlock child ctor),
    step.Carries (oldSymbols.native.ctor ref)
  sel : ∀ {child : DataRef oldBlock} {ctor : CtorDecl oldArity}
    (ctorRef : CtorRef oldBlock child ctor) {field : FieldDecl oldArity}
    (fieldRef : FieldRef ctor field),
    step.Carries (oldSymbols.native.sel ctorRef fieldRef)
  test : ∀ {child : DataRef oldBlock} {ctor : CtorDecl oldArity}
    (ref : CtorRef oldBlock child ctor),
    step.Carries (oldSymbols.native.test ref)

/-- Invert an earlier constructor application after one later carrier step. -/
theorem ctorApplies_unwrap (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {child : DataRef oldBlock} {ctor : CtorDecl oldArity}
    (ctorRef : CtorRef oldBlock child ctor)
    {arguments : List (SMT.Value step.target)}
    {result : SMT.Value step.target}
    (applied : Crush.SMT.CtorApplies (SMT.model fo step.target)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor)
      arguments result) :
    Crush.SMT.CtorApplies (SMT.model fo step.prior.target)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor)
      (arguments.map step.unwrap) (step.unwrap result) := by
  constructor
  · exact step.values_unwrap fo applied.1
  · have fieldsTyped : Crush.SMT.ValuesTyped (SMT.model fo step.target)
        (ctor.fields.map fun field => fo.sort (field.fo oldBlock)) arguments := by
      simpa [raw_ctor_argSorts, Datatype.fieldSort_eq represented] using applied.1
    have graph := step.apply_unwrap fo (oldSymbols.native.ctor ctorRef)
      (carried.ctor ctorRef) arguments (by
        simpa [CtorDecl.fo, Function.comp_def] using fieldsTyped) result (by
        simpa [represented.native_ctor_ident ctorRef, ctorDecl] using applied.2)
    simpa [represented.native_ctor_ident ctorRef, ctorDecl] using graph

/-- Wrap an earlier constructor application into the next target model. -/
theorem ctorApplies_wrap (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {child : DataRef oldBlock} {ctor : CtorDecl oldArity}
    (ctorRef : CtorRef oldBlock child ctor)
    {arguments : List (SMT.Value step.prior.target)}
    {result : SMT.Value step.prior.target}
    (applied : Crush.SMT.CtorApplies (SMT.model fo step.prior.target)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor)
      arguments result) :
    Crush.SMT.CtorApplies (SMT.model fo step.target)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor)
      (arguments.map step.wrap) (step.wrap result) := by
  constructor
  · exact step.values_wrap fo applied.1
  · have fieldsTyped : Crush.SMT.ValuesTyped
        (SMT.model fo step.prior.target)
        ((ctor.fo oldBlock child).args.map fo.sort) arguments := by
      simpa [raw_ctor_argSorts, Datatype.fieldSort_eq represented,
        CtorDecl.fo, Function.comp_def] using applied.1
    have graph := (step.apply_wrap_iff fo
      (oldSymbols.native.ctor ctorRef) (carried.ctor ctorRef)
      arguments fieldsTyped result).mpr (by
        simpa [represented.native_ctor_ident ctorRef, ctorDecl] using applied.2)
    simpa [represented.native_ctor_ident ctorRef, ctorDecl] using graph

/-- Constructor totality and injectivity survive a later disjoint block. -/
theorem ctor_holds_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {child : DataRef oldBlock} {ctor : CtorDecl oldArity}
    (ctorRef : CtorRef oldBlock child ctor)
    (holds : Crush.SMT.ConstructorHolds (SMT.model fo step.prior.target)
      (dataSort data child)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor)) :
    Crush.SMT.ConstructorHolds (SMT.model fo step.target)
      (dataSort data child)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor) := by
  constructor
  · have sourceType := SMT.symbol_has_type fo step.prior.target
      (oldSymbols.native.ctor ctorRef)
    have targetType := step.hasType_carry fo
      (oldSymbols.native.ctor ctorRef) (carried.ctor ctorRef) sourceType
    rw [raw_ctor_argSorts]
    simp only [ctorDecl]
    rw [← represented.native_ctor_ident ctorRef,
      ← represented.sort_eq child]
    simpa [Datatype.fieldSort_eq represented, CtorDecl.fo,
      Function.comp_def] using targetType
  · intro leftArgs rightArgs leftResult rightResult
      leftApply rightApply resultEq
    have leftOld := step.ctorApplies_unwrap represented carried ctorRef leftApply
    have rightOld := step.ctorApplies_unwrap represented carried ctorRef rightApply
    have oldResultEq := congrArg step.unwrap resultEq
    have oldArgsEq := holds.2 _ _ _ _ leftOld rightOld oldResultEq
    have fieldsExternal := (carried.ctor ctorRef).external
    change (∀ sort ∈ (ctor.fo oldBlock child).args,
        BaseLift.External step.block sort) ∧
      BaseLift.External step.block (ctor.fo oldBlock child).result
      at fieldsExternal
    have leftTyped : Crush.SMT.ValuesTyped (SMT.model fo step.target)
        (ctor.fields.map fun field => fo.sort (field.fo oldBlock)) leftArgs := by
      simpa [raw_ctor_argSorts, Datatype.fieldSort_eq represented] using leftApply.1
    have rightTyped : Crush.SMT.ValuesTyped (SMT.model fo step.target)
        (ctor.fields.map fun field => fo.sort (field.fo oldBlock)) rightArgs := by
      simpa [raw_ctor_argSorts, Datatype.fieldSort_eq represented] using rightApply.1
    have fieldExternal : ∀ sort ∈
        ctor.fields.map (FieldDecl.fo oldBlock),
        BaseLift.External step.block sort := by
      simpa [CtorDecl.fo] using fieldsExternal.1
    have leftRound := step.values_wrap_unwrap fo
      (sorts := ctor.fields.map (FieldDecl.fo oldBlock)) fieldExternal (by
        simpa [List.map_map, Function.comp_def] using leftTyped)
    have rightRound := step.values_wrap_unwrap fo
      (sorts := ctor.fields.map (FieldDecl.fo oldBlock)) fieldExternal (by
        simpa [List.map_map, Function.comp_def] using rightTyped)
    have mappedEq := congrArg (List.map step.wrap) oldArgsEq
    dsimp only [target, Lifted.extend] at leftRound rightRound mappedEq ⊢
    exact leftRound.symm.trans (mappedEq.trans rightRound)

/-- Selector totality and the matching-constructor equation survive a later
disjoint block. -/
theorem sel_holds_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {child : DataRef oldBlock} {ctor : CtorDecl oldArity}
    (ctorRef : CtorRef oldBlock child ctor)
    (holds : Crush.SMT.SelectorsHold (SMT.model fo step.prior.target)
      (dataSort data child)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor)) :
    Crush.SMT.SelectorsHold (SMT.model fo step.target)
      (dataSort data child)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor) := by
  intro index name resultSort lookup
  have rawBounds : index <
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor).selDecls.size :=
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
  have old := holds index _ _ lookup
  constructor
  · have sourceType := SMT.symbol_has_type fo step.prior.target
      (oldSymbols.native.sel ctorRef fieldRef)
    have targetType := step.hasType_carry fo
      (oldSymbols.native.sel ctorRef fieldRef)
      (carried.sel ctorRef fieldRef) sourceType
    rw [← indexEq, ← represented.native_sel_ident ctorRef fieldRef,
      Datatype.fieldSort_eq represented, ← represented.sort_eq child]
    simpa [FieldDecl.sel, Function.comp_def] using targetType
  · intro arguments result selected ctorApplied selectedAt
    change List (SMT.Value step.target) at arguments
    change SMT.Value step.target at result selected
    have oldCtor := step.ctorApplies_unwrap represented carried ctorRef
      ctorApplied
    have oldSelected : (arguments.map step.unwrap)[index]? =
        some (step.unwrap selected) := by
      exact getElem?_map_some step.unwrap arguments index selected selectedAt
    have oldSel := old.2 (arguments.map step.unwrap) (step.unwrap result)
      (step.unwrap selected) oldCtor oldSelected
    have fieldsTyped : Crush.SMT.ValuesTyped (SMT.model fo step.target)
        (ctor.fields.map fun item => fo.sort (item.fo oldBlock)) arguments := by
      simpa [raw_ctor_argSorts, Datatype.fieldSort_eq represented] using
        ctorApplied.1
    have intrinsicSortAt :
        (ctor.fields.map fun item => fo.sort (item.fo oldBlock))[index]? =
          some (fo.sort (field.fo oldBlock)) := by
      rw [← indexEq]
      simp
    have selectedTyped := values_typed_at fieldsTyped index intrinsicSortAt
      selectedAt
    have resultApply : (SMT.model fo step.target).apply
        (fo.ident (oldSymbols.native.ctor ctorRef)) arguments result := by
      simpa [represented.native_ctor_ident ctorRef, ctorDecl] using ctorApplied.2
    have resultTyped := step.apply_result_typed fo
      (oldSymbols.native.ctor ctorRef) arguments result resultApply
    have oldResultTyped := step.unwrap_inSort fo resultTyped
    have oldResultTyped' : (SMT.model fo step.prior.target).inSort
        (fo.sort (.base child.decl.sort)) (step.unwrap result) := by
      simpa [CtorDecl.fo] using oldResultTyped
    have oldSelTyped : Crush.SMT.ValuesTyped (SMT.model fo step.prior.target)
        ((field.sel oldBlock child).args.map fo.sort)
        [step.unwrap result] := by
      rw [FieldDecl.sel]
      exact .cons oldResultTyped' .nil
    have oldSel' : (SMT.model fo step.prior.target).apply
        (fo.ident (oldSymbols.native.sel ctorRef fieldRef))
        [step.unwrap result] (step.unwrap selected) := by
      rw [represented.native_sel_ident ctorRef fieldRef]
      simpa [indexEq, ctorDecl] using oldSel
    have mapped := (step.apply_wrap_iff fo
      (oldSymbols.native.sel ctorRef fieldRef)
      (carried.sel ctorRef fieldRef) [step.unwrap result] oldSelTyped
      (step.unwrap selected)).mpr oldSel'
    have resultRound := step.wrap_unwrap_of_inSort fo (carried.sort child)
      result resultTyped
    have selectedRound := step.wrap_unwrap_of_inSort fo
      (by
        have external := (carried.sel ctorRef fieldRef).external
        change (∀ sort ∈ (field.sel oldBlock child).args,
            BaseLift.External step.block sort) ∧
          BaseLift.External step.block (field.sel oldBlock child).result
          at external
        simpa [FieldDecl.sel] using external.2)
      selected selectedTyped
    simpa [represented.native_sel_ident ctorRef fieldRef, ctorDecl, indexEq,
      resultRound, selectedRound] using mapped

@[simp] theorem wrap_bool (step : Step source)
    (value : Bool) :
    step.wrap (SMT.boolValue step.prior.target value) =
      SMT.boolValue step.target value := by
  cases value with
  | false =>
      simpa [SMT.boolValue, BaseLift.wrapWith] using
        step.wrap_typed (sort := FO.FOSort.bool) trivial (False : Prop)
  | true =>
      simpa [SMT.boolValue, BaseLift.wrapWith] using
        step.wrap_typed (sort := FO.FOSort.bool) trivial (True : Prop)

/-- A tester for an earlier constructor remains total and recognizes that
constructor after one later disjoint block. -/
theorem test_holds_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {child : DataRef oldBlock} {ctor : CtorDecl oldArity}
    (ctorRef : CtorRef oldBlock child ctor)
    (holds : Crush.SMT.TesterHolds (SMT.model fo step.prior.target)
      (dataSort data child)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor)) :
    Crush.SMT.TesterHolds (SMT.model fo step.target)
      (dataSort data child)
      (ctorDecl (block := oldBlock) data child ctorRef.index ctor) := by
  constructor
  · have sourceType := SMT.symbol_has_type fo step.prior.target
      (oldSymbols.native.test ctorRef)
    have targetType := step.hasType_carry fo
      (oldSymbols.native.test ctorRef) (carried.test ctorRef) sourceType
    rw [represented.native_test_ident ctorRef] at targetType
    rw [← represented.sort_eq child]
    simpa [Crush.SMT.CtorDecl.tester, ctorDecl, CtorDecl.test,
      fo.bool_eq, Function.comp_def] using targetType
  · intro arguments result applied
    change List (SMT.Value step.target) at arguments
    change SMT.Value step.target at result
    have oldCtor := step.ctorApplies_unwrap represented carried ctorRef applied
    have oldTest := holds.2 (arguments.map step.unwrap)
      (step.unwrap result) oldCtor
    have resultApply : (SMT.model fo step.target).apply
        (fo.ident (oldSymbols.native.ctor ctorRef)) arguments result := by
      simpa [represented.native_ctor_ident ctorRef, ctorDecl] using applied.2
    have resultTyped := step.apply_result_typed fo
      (oldSymbols.native.ctor ctorRef) arguments result resultApply
    have oldResultTyped := step.unwrap_inSort fo resultTyped
    have oldResultTyped' : (SMT.model fo step.prior.target).inSort
        (fo.sort (.base child.decl.sort)) (step.unwrap result) := by
      simpa [CtorDecl.fo] using oldResultTyped
    have oldTestTyped : Crush.SMT.ValuesTyped
        (SMT.model fo step.prior.target)
        ((ctor.test oldBlock child).args.map fo.sort) [step.unwrap result] := by
      rw [CtorDecl.test]
      exact .cons oldResultTyped' .nil
    have oldTest' : (SMT.model fo step.prior.target).apply
        (fo.ident (oldSymbols.native.test ctorRef)) [step.unwrap result]
        ((SMT.model fo step.prior.target).bool true) := by
      rw [represented.native_test_ident ctorRef]
      simpa [Crush.SMT.CtorDecl.tester, ctorDecl] using oldTest
    have mapped := (step.apply_wrap_iff fo
      (oldSymbols.native.test ctorRef) (carried.test ctorRef)
      [step.unwrap result] oldTestTyped
      ((SMT.model fo step.prior.target).bool true)).mpr oldTest'
    have resultRound := step.wrap_unwrap_of_inSort fo (carried.sort child)
      result resultTyped
    simpa [represented.native_test_ident ctorRef,
      Crush.SMT.CtorDecl.tester, ctorDecl, resultRound] using mapped

/-- All three local laws of an earlier raw constructor survive one step. -/
theorem ctor_laws_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {sort : Crush.SMT.SSort} {rawCtor : Crush.SMT.CtorDecl}
    (member : (sort, rawCtor) ∈
      Crush.SMT.datatypeCtors (entries oldBlock data))
    (holds : Crush.SMT.ConstructorHolds
        (SMT.model fo step.prior.target) sort rawCtor ∧
      Crush.SMT.SelectorsHold
        (SMT.model fo step.prior.target) sort rawCtor ∧
      Crush.SMT.TesterHolds
        (SMT.model fo step.prior.target) sort rawCtor) :
    Crush.SMT.ConstructorHolds (SMT.model fo step.target) sort rawCtor ∧
      Crush.SMT.SelectorsHold (SMT.model fo step.target) sort rawCtor ∧
      Crush.SMT.TesterHolds (SMT.model fo step.target) sort rawCtor := by
  obtain ⟨child, ctor, ctorRef, rfl, rfl⟩ := raw_ctor_ref data member
  exact ⟨step.ctor_holds_carry represented carried ctorRef holds.1,
    step.sel_holds_carry represented carried ctorRef holds.2.1,
    step.test_holds_carry represented carried ctorRef holds.2.2⟩

/-- Distinct earlier constructors remain disjoint after one step. -/
theorem ctor_disjoint_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {leftSort rightSort : Crush.SMT.SSort}
    {leftCtor rightCtor : Crush.SMT.CtorDecl}
    (leftMem : (leftSort, leftCtor) ∈
      Crush.SMT.datatypeCtors (entries oldBlock data))
    (rightMem : (rightSort, rightCtor) ∈
      Crush.SMT.datatypeCtors (entries oldBlock data))
    (different : leftCtor.name ≠ rightCtor.name)
    (holds : ∀ leftArgs leftResult rightArgs rightResult,
      Crush.SMT.CtorApplies (SMT.model fo step.prior.target)
          leftCtor leftArgs leftResult →
        Crush.SMT.CtorApplies (SMT.model fo step.prior.target)
          rightCtor rightArgs rightResult →
        leftResult ≠ rightResult)
    {leftArgs rightArgs : List (SMT.Value step.target)}
    {leftResult rightResult : SMT.Value step.target}
    (leftApply : Crush.SMT.CtorApplies (SMT.model fo step.target)
      leftCtor leftArgs leftResult)
    (rightApply : Crush.SMT.CtorApplies (SMT.model fo step.target)
      rightCtor rightArgs rightResult) :
    leftResult ≠ rightResult := by
  obtain ⟨leftData, leftDecl, leftRef, rfl, rfl⟩ :=
    raw_ctor_ref data leftMem
  obtain ⟨rightData, rightDecl, rightRef, rfl, rfl⟩ :=
    raw_ctor_ref data rightMem
  have oldLeft := step.ctorApplies_unwrap represented carried leftRef leftApply
  have oldRight := step.ctorApplies_unwrap represented carried rightRef rightApply
  intro equal
  exact holds _ _ _ _ oldLeft oldRight (congrArg step.unwrap equal)

/-- An earlier tester still rejects values of a distinct constructor. -/
theorem test_disjoint_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {sort : Crush.SMT.SSort} {leftCtor rightCtor : Crush.SMT.CtorDecl}
    (leftMem : (sort, leftCtor) ∈
      Crush.SMT.datatypeCtors (entries oldBlock data))
    (rightMem : (sort, rightCtor) ∈
      Crush.SMT.datatypeCtors (entries oldBlock data))
    (different : leftCtor.name ≠ rightCtor.name)
    (holds : ∀ arguments result,
      Crush.SMT.CtorApplies (SMT.model fo step.prior.target)
          rightCtor arguments result →
        (SMT.model fo step.prior.target).apply leftCtor.tester [result]
          ((SMT.model fo step.prior.target).bool false))
    {arguments : List (SMT.Value step.target)}
    {result : SMT.Value step.target}
    (applied : Crush.SMT.CtorApplies (SMT.model fo step.target)
      rightCtor arguments result) :
    (SMT.model fo step.target).apply leftCtor.tester [result]
      ((SMT.model fo step.target).bool false) := by
  obtain ⟨leftData, leftDecl, leftRef, leftSortEq, leftCtorEq⟩ :=
    raw_ctor_ref data leftMem
  obtain ⟨rightData, rightDecl, rightRef, rightSortEq, rightCtorEq⟩ :=
    raw_ctor_ref data rightMem
  have dataEq : leftData = rightData := dataSort_injective represented.wf.names
    (leftSortEq.symm.trans rightSortEq)
  subst rightData
  rw [rightCtorEq] at applied
  have oldCtor := step.ctorApplies_unwrap represented carried rightRef applied
  have oldReject := holds (arguments.map step.unwrap) (step.unwrap result) (by
    simpa [rightCtorEq] using oldCtor)
  have resultApply : (SMT.model fo step.target).apply
      (fo.ident (oldSymbols.native.ctor rightRef)) arguments result := by
    simpa [represented.native_ctor_ident rightRef, ctorDecl] using applied.2
  have resultTyped := step.apply_result_typed fo
    (oldSymbols.native.ctor rightRef) arguments result resultApply
  have oldResultTyped := step.unwrap_inSort fo resultTyped
  have oldResultTyped' : (SMT.model fo step.prior.target).inSort
      (fo.sort (.base leftData.decl.sort)) (step.unwrap result) := by
    simpa [CtorDecl.fo] using oldResultTyped
  have oldTestTyped : Crush.SMT.ValuesTyped
      (SMT.model fo step.prior.target)
      ((leftDecl.test oldBlock leftData).args.map fo.sort)
      [step.unwrap result] := by
    rw [CtorDecl.test]
    exact .cons oldResultTyped' .nil
  have oldReject' : (SMT.model fo step.prior.target).apply
      (fo.ident (oldSymbols.native.test leftRef)) [step.unwrap result]
      ((SMT.model fo step.prior.target).bool false) := by
    rw [represented.native_test_ident leftRef]
    simpa [leftCtorEq, Crush.SMT.CtorDecl.tester, ctorDecl] using oldReject
  have mapped := (step.apply_wrap_iff fo
    (oldSymbols.native.test leftRef) (carried.test leftRef)
    [step.unwrap result] oldTestTyped
    ((SMT.model fo step.prior.target).bool false)).mpr oldReject'
  have resultRound := step.wrap_unwrap_of_inSort fo (carried.sort leftData)
    result resultTyped
  simpa [leftCtorEq, represented.native_test_ident leftRef,
    Crush.SMT.CtorDecl.tester, ctorDecl, resultRound] using mapped

/-- Exhaustiveness of an earlier datatype sort survives one step. -/
theorem exhaustive_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    {name : String} {count : Nat} {decl : Crush.SMT.DatatypeDecl}
    (member : (name, count, decl) ∈ (entries oldBlock data).toList)
    (holds : ∀ value, (SMT.model fo step.prior.target).inSort
        (Crush.SMT.datatypeSort name) value →
      ∃ ctor, ctor ∈ decl.ctors.toList ∧
        ∃ arguments, Crush.SMT.CtorApplies
          (SMT.model fo step.prior.target) ctor arguments value)
    (value : SMT.Value step.target)
    (typed : (SMT.model fo step.target).inSort
      (Crush.SMT.datatypeSort name) value) :
    ∃ ctor, ctor ∈ decl.ctors.toList ∧
      ∃ arguments, Crush.SMT.CtorApplies
        (SMT.model fo step.target) ctor arguments value := by
  obtain ⟨child, nameEq, countEq, declEq⟩ :=
    raw_entry_ref oldBlock data member
  have oldTyped := step.unwrap_inSort fo typed
  obtain ⟨rawCtor, ctorMem, arguments, oldApply⟩ :=
    holds (step.unwrap value) oldTyped
  have pairMem : (dataSort data child, rawCtor) ∈
      Crush.SMT.datatypeCtors (entries oldBlock data) := by
    subst name
    subst count
    subst decl
    simp only [Crush.SMT.datatypeCtors, entries, List.mem_flatMap,
      List.mem_map]
    refine ⟨(data.name (.sort child), 0,
      dataDecl (block := oldBlock) data child), ?_, rawCtor, ctorMem, rfl⟩
    exact ⟨child, by simp, rfl⟩
  obtain ⟨madeChild, madeCtor, ctorRef, sortEq, ctorEq⟩ :=
    raw_ctor_ref data pairMem
  rw [ctorEq] at oldApply
  have mapped := step.ctorApplies_wrap represented carried ctorRef oldApply
  have encodedTyped : (SMT.model fo step.target).inSort
      (fo.sort (.base child.decl.sort)) value := by
    rw [represented.sort_eq child]
    simpa [Crush.SMT.datatypeSort, dataSort, nameEq] using typed
  have valueRound := step.wrap_unwrap_of_inSort fo (carried.sort child)
    value encodedTyped
  have mapped' : Crush.SMT.CtorApplies (SMT.model fo step.target)
      rawCtor (arguments.map step.wrap) (step.wrap (step.unwrap value)) := by
    dsimp only [target, Lifted.extend] at mapped ⊢
    exact ctorEq.symm ▸ mapped
  refine ⟨rawCtor, ctorMem, arguments.map step.wrap, ?_⟩
  dsimp only [target, Lifted.extend] at valueRound mapped' ⊢
  exact valueRound ▸ mapped'

/-- The preceding structural rank, composed with unwrapping, still decreases
on every recursive field of an earlier constructor. -/
theorem rank_lt_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    (rank : SMT.Value step.prior.target → Nat)
    (decreases : ∀ dataSort rawCtor,
      (dataSort, rawCtor) ∈
          Crush.SMT.datatypeCtors (entries oldBlock data) →
      ∀ arguments result,
        Crush.SMT.CtorApplies (SMT.model fo step.prior.target)
            rawCtor arguments result →
        ∀ (index : Nat) fieldSort fieldValue,
          rawCtor.argSorts[index]? = some fieldSort →
          arguments[index]? = some fieldValue →
          fieldSort ∈ Crush.SMT.datatypeSorts (entries oldBlock data) →
          rank fieldValue < rank result)
    {dataSort : Crush.SMT.SSort} {rawCtor : Crush.SMT.CtorDecl}
    (member : (dataSort, rawCtor) ∈
      Crush.SMT.datatypeCtors (entries oldBlock data))
    {arguments : List (SMT.Value step.target)}
    {result : SMT.Value step.target}
    (applied : Crush.SMT.CtorApplies (SMT.model fo step.target)
      rawCtor arguments result)
    (index : Nat) (fieldSort : Crush.SMT.SSort)
    (fieldValue : SMT.Value step.target)
    (sortAt : rawCtor.argSorts[index]? = some fieldSort)
    (valueAt : arguments[index]? = some fieldValue)
    (recursive : fieldSort ∈
      Crush.SMT.datatypeSorts (entries oldBlock data)) :
    rank (step.unwrap fieldValue) < rank (step.unwrap result) := by
  obtain ⟨child, ctor, ctorRef, rfl, rfl⟩ := raw_ctor_ref data member
  have oldApply := step.ctorApplies_unwrap represented carried ctorRef applied
  have oldValueAt : (arguments.map step.unwrap)[index]? =
      some (step.unwrap fieldValue) :=
    getElem?_map_some step.unwrap arguments index fieldValue valueAt
  exact decreases _ _ (raw_ctor_mem data ctorRef)
    (arguments.map step.unwrap) (step.unwrap result) oldApply
    index fieldSort (step.unwrap fieldValue) sortAt oldValueAt recursive

/-- One later disjoint dependency block preserves every semantic component of
an earlier native datatype declaration, with no datatype-specific re-modeling. -/
theorem data_hold_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    (holds : Crush.SMT.DatatypesHold (SMT.model fo step.prior.target)
      (entries oldBlock data)) :
    Crush.SMT.DatatypesHold (SMT.model fo step.target)
      (entries oldBlock data) := by
  rcases holds with
    ⟨supported, laws, disjoint, exhaustive, testDisjoint, rank, decreases⟩
  refine ⟨supported, ?_, ?_, ?_, ?_, fun value => rank (step.unwrap value), ?_⟩
  · intro sort ctor member
    exact step.ctor_laws_carry represented carried member (laws sort ctor member)
  · intro leftSort leftCtor rightSort rightCtor leftMem rightMem different
      leftArgs leftResult rightArgs rightResult leftApply rightApply
    exact step.ctor_disjoint_carry represented carried leftMem rightMem different
      (disjoint leftSort leftCtor rightSort rightCtor leftMem rightMem different)
      leftApply rightApply
  · intro name count decl member value typed
    exact step.exhaustive_carry represented carried member
      (exhaustive name count decl member) value typed
  · intro sort leftCtor rightCtor leftMem rightMem different arguments result
      applied
    exact step.test_disjoint_carry represented carried leftMem rightMem different
      (testDisjoint sort leftCtor rightCtor leftMem rightMem different) applied
  · intro sort ctor member arguments result applied index fieldSort fieldValue
      sortAt valueAt recursive
    exact step.rank_lt_carry represented carried rank decreases member applied
      index fieldSort fieldValue sortAt valueAt recursive

/-- Validity of an earlier `declare-datatypes` command survives one later
disjoint dependency block. -/
theorem command_sound_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    (valid : (SMT.model fo step.prior.target).SatisfiesCommand
      (command oldBlock data)) :
    (SMT.model fo step.target).SatisfiesCommand
      (command oldBlock data) := by
  exact ⟨valid.1, step.data_hold_carry represented carried valid.2⟩

/-- Exact interpretation of a carried unary symbol. The later model unwraps its
external argument, applies the preceding interpretation, then wraps the external
result. -/
theorem symbol_unary_carry (step : Step source)
    {argument result : FO.FOSort}
    (symbol : Symbol signature { args := [argument], result })
    (carried : step.Carries symbol)
    (value : argument.Denote step.target.carriers) :
    step.target.symbol symbol value =
      BaseLift.wrapWith step.productive carried.external.2
        (step.prior.target.symbol symbol
          (BaseLift.unwrap step.productive
            (carried.external.1 argument (by simp)) value)) := by
  have equal := step.law.extend_symbol_external step.wf step.productive
    step.prior.target step.prior.relation step.prior.models symbol
    carried.unowned carried.external
  dsimp only [target, Lifted.extend] at equal ⊢
  rw [equal]
  rfl

/-- On a sort external to a later datatype block, the composed carrier guard
is exactly the preceding guard after unwrapping the external carrier. -/
theorem relation_guard (step : Step source) (sort : FO.FOSort)
    (external : BaseLift.External step.block sort)
    (value : sort.Denote step.target.carriers) :
    ((BaseLift.carrierRel step.wf step.productive step.prior.relation
      step.law.carrier) sort).guard value ↔
      (step.prior.relation sort).guard
        (BaseLift.unwrap step.productive external value) := by
  cases sort with
  | bool => rfl
  | fn domain codomain => rfl
  | base base =>
      change (BaseLift.rel step.wf step.productive step.prior.relation.base
        step.law.carrier base).guard value ↔ _
      rw [BaseLift.rel_external step.wf step.productive
        step.prior.relation.base step.law.carrier base external]
      rfl

/-- The semantic tester/selector guard equation for an earlier block survives
one later dependency extension whenever the new guard is transported through
the same external carrier isomorphism. -/
theorem guardLaw_carry (step : Step source)
    {oldArity : Nat} {oldBlock : Block oldArity}
    {oldSymbols : Symbols signature oldBlock}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding oldArity}
    (represented : Representation oldBlock oldSymbols fo data)
    (carried : CarriedBy represented step)
    (oldGuard : ∀ sort : FO.FOSort,
      sort.Denote step.prior.target.carriers → Prop)
    (newGuard : ∀ sort : FO.FOSort, sort.Denote step.target.carriers → Prop)
    (guarded : ∀ (sort : FO.FOSort)
      (external : BaseLift.External step.block sort)
      (value : sort.Denote step.target.carriers),
      newGuard sort value ↔ oldGuard sort
        (BaseLift.unwrap step.productive external value))
    (law : represented.GuardLaw step.prior.target oldGuard) :
    represented.GuardLaw step.target newGuard := by
  intro child value
  let childExternal := carried.sort child
  let oldValue := BaseLift.unwrap step.productive childExternal value
  have testEq : ∀ {ctor : CtorDecl oldArity}
      (ctorRef : CtorRef oldBlock child ctor),
      step.target.symbol (oldSymbols.native.test ctorRef) value =
        step.prior.target.symbol (oldSymbols.native.test ctorRef) oldValue := by
    intro ctor ctorRef
    have equal := step.symbol_unary_carry
      (oldSymbols.native.test ctorRef) (carried.test ctorRef) value
    simpa [CtorDecl.test, oldValue, BaseLift.wrapWith] using equal
  have selGuard : ∀ {ctor : CtorDecl oldArity}
      (ctorRef : CtorRef oldBlock child ctor)
      {field : FieldDecl oldArity} (fieldRef : FieldRef ctor field),
      newGuard (field.fo oldBlock)
          (step.target.symbol
            (oldSymbols.native.sel ctorRef fieldRef) value) ↔
        oldGuard (field.fo oldBlock)
          (step.prior.target.symbol
            (oldSymbols.native.sel ctorRef fieldRef) oldValue) := by
    intro ctor ctorRef field fieldRef
    have equal := step.symbol_unary_carry
      (oldSymbols.native.sel ctorRef fieldRef)
      (carried.sel ctorRef fieldRef) value
    have fieldExternal := (carried.sel ctorRef fieldRef).external.2
    have equal' :
        step.target.symbol
            (oldSymbols.native.sel ctorRef fieldRef) value =
          BaseLift.wrapWith step.productive fieldExternal
            (step.prior.target.symbol
              (oldSymbols.native.sel ctorRef fieldRef) oldValue) := by
      calc
        _ = BaseLift.wrapWith step.productive
              (carried.sel ctorRef fieldRef).external.2
              (step.prior.target.symbol
                (oldSymbols.native.sel ctorRef fieldRef)
                (BaseLift.unwrap step.productive
                  ((carried.sel ctorRef fieldRef).external.1
                    (.base child.decl.sort) (by simp [FieldDecl.sel]))
                  value)) := equal
        _ = _ := by
          congr 1
    have held := guarded (field.fo oldBlock) fieldExternal
      (step.target.symbol
        (oldSymbols.native.sel ctorRef fieldRef) value)
    have selectedEq :
        BaseLift.unwrap step.productive fieldExternal
            (step.target.symbol
              (oldSymbols.native.sel ctorRef fieldRef) value) =
          step.prior.target.symbol
            (oldSymbols.native.sel ctorRef fieldRef) oldValue := by
      have mapped := congrArg
        (BaseLift.unwrap step.productive fieldExternal) equal'
      rw [BaseLift.unwrap_wrap] at mapped
      exact mapped
    constructor
    · intro accepted
      exact Eq.mp
        (congrArg (oldGuard (field.fo oldBlock)) selectedEq)
        (held.mp accepted)
    · intro accepted
      exact held.mpr (Eq.mpr
        (congrArg (oldGuard (field.fo oldBlock)) selectedEq)
        accepted)
  have childGuard := guarded (.base child.decl.sort) childExternal value
  constructor
  · intro current
    apply childGuard.mpr
    apply (law child oldValue).mp
    intro ctor ctorRef tested field fieldRef
    have newTest :
        step.target.symbol (oldSymbols.native.test ctorRef) value := by
      rw [testEq ctorRef]
      exact tested
    exact (selGuard ctorRef fieldRef).mp
      (current ctor ctorRef newTest field fieldRef)
  · intro accepted
    have oldAccepted := (law child oldValue).mpr (childGuard.mp accepted)
    intro ctor ctorRef tested field fieldRef
    have oldTest :
        step.prior.target.symbol (oldSymbols.native.test ctorRef) oldValue := by
      rw [← testEq ctorRef]
      exact tested
    exact (selGuard ctorRef fieldRef).mpr
      (oldAccepted ctor ctorRef oldTest field fieldRef)

/-! ## Dependency-ordered environments -/

/-- The native declaration of `earlier` is disjoint from one later represented
block. This is the only cross-block invariant needed by semantic transport. -/
structure Before
    {earlierArity laterArity : Nat}
    {earlierBlock : Block earlierArity} {laterBlock : Block laterArity}
    {earlierSymbols : Symbols signature earlierBlock}
    {laterSymbols : Symbols signature laterBlock}
    {fo : SMT.Encoding (Symbol signature)}
    {earlierData : BlockEncoding earlierArity}
    {laterData : BlockEncoding laterArity}
    (earlier : Representation earlierBlock earlierSymbols fo earlierData)
    (_later : Representation laterBlock laterSymbols fo laterData) : Prop where
  sort : ∀ child : DataRef earlierBlock,
    BaseLift.External laterBlock (.base child.decl.sort)
  ctor : ∀ {child : DataRef earlierBlock} {ctor : CtorDecl earlierArity}
    (ref : CtorRef earlierBlock child ctor),
    ¬Nonempty (NativeRef laterSymbols.native
        (earlierSymbols.native.ctor ref)) ∧
      BaseLift.ExternalDecl laterBlock (ctor.fo earlierBlock child)
  sel : ∀ {child : DataRef earlierBlock} {ctor : CtorDecl earlierArity}
    (ctorRef : CtorRef earlierBlock child ctor)
    {field : FieldDecl earlierArity} (fieldRef : FieldRef ctor field),
    ¬Nonempty (NativeRef laterSymbols.native
        (earlierSymbols.native.sel ctorRef fieldRef)) ∧
      BaseLift.ExternalDecl laterBlock (field.sel earlierBlock child)
  test : ∀ {child : DataRef earlierBlock} {ctor : CtorDecl earlierArity}
    (ref : CtorRef earlierBlock child ctor),
    ¬Nonempty (NativeRef laterSymbols.native
        (earlierSymbols.native.test ref)) ∧
      BaseLift.ExternalDecl laterBlock (ctor.test earlierBlock child)

namespace Before

/-- Turn the compact static ordering fact into the exact evidence consumed by
one semantic extension step. Declaration externality follows uniformly from
the earlier block's sort and field-sort ordering. -/
theorem carried
    {earlierArity laterArity : Nat}
    {earlierBlock : Block earlierArity} {laterBlock : Block laterArity}
    {earlierSymbols : Symbols signature earlierBlock}
    {laterSymbols : Symbols signature laterBlock}
    {fo : SMT.Encoding (Symbol signature)}
    {earlierData : BlockEncoding earlierArity}
    {laterData : BlockEncoding laterArity}
    {earlier : Representation earlierBlock earlierSymbols fo earlierData}
    {later : Representation laterBlock laterSymbols fo laterData}
    (before : Before earlier later)
    (law : FamilyLawful laterSymbols.native source)
    (wf : laterBlock.WF) (productive : Productive laterBlock)
    (prior : Lifted source) :
    CarriedBy earlier
      ({ arity := laterArity
         block := laterBlock
         symbols := laterSymbols
         law := law
         wf := wf
         productive := productive
         prior := prior } :
        Step source) := by
  refine {
    sort := before.sort
    ctor := fun {_child} {_ctor} ref =>
      ⟨(before.ctor ref).1, (before.ctor ref).2⟩
    sel := fun {_child} {_ctor} ctorRef {_field} fieldRef =>
      ⟨(before.sel ctorRef fieldRef).1, (before.sel ctorRef fieldRef).2⟩
    test := fun {_child} {_ctor} ref =>
      ⟨(before.test ref).1, (before.test ref).2⟩ }

end Before

/-- One represented block precedes every block in a represented suffix. -/
inductive After
    {earlierArity : Nat} {earlierBlock : Block earlierArity}
    {earlierSymbols : Symbols signature earlierBlock}
    {fo : SMT.Encoding (Symbol signature)}
    {earlierData : BlockEncoding earlierArity}
    (earlier : Representation earlierBlock earlierSymbols fo earlierData) :
    {env : List (Entry signature)} →
      Represented fo env → Prop where
  | nil : After earlier .nil
  | cons {entry : Entry signature}
      {rest : List (Entry signature)}
      {data : BlockEncoding entry.arity}
      {later : Representation entry.block entry.symbols fo data}
      {tail : Represented fo rest} :
      Before earlier later → After earlier tail →
        After earlier (.cons later tail)

/-- Every earlier native declaration is disjoint from every later dependency
block. Adjacent facts are insufficient because an early command must survive
the complete suffix. -/
inductive Ordered {fo : SMT.Encoding (Symbol signature)} :
    {env : List (Entry signature)} →
      (represented : Represented fo env) → Prop where
  | nil : Ordered .nil
  | cons {entry : Entry signature}
      {rest : List (Entry signature)}
      {data : BlockEncoding entry.arity}
      {head : Representation entry.block entry.symbols fo data}
      {tail : Represented fo rest} :
      After head tail → Ordered tail → Ordered (.cons head tail)

/-- One exact recursive guard command for a represented datatype block. The
names and binder are retained intrinsically, so semantic validation cannot
drift from the raw command. -/
structure GuardCommand
    {entry : Entry signature} {data : BlockEncoding entry.arity}
    {guarding : SMT.Guarding (Symbol signature)}
    (_head : Representation entry.block entry.symbols guarding.encoding data)
    where
  name : DataRef entry.block → String
  binder : DataRef entry.block → String
  command : Crush.SMT.Command
  command_eq : command = .defFunsRec
    (wfDefs (native := entry.symbols.native) guarding data name binder)

/-- Recursive guard commands aligned with the same dependency-ordered native
representation. -/
inductive GuardTrace (guarding : SMT.Guarding (Symbol signature)) :
    {env : List (Entry signature)} →
      Represented guarding.encoding env → Type 1 where
  | nil : GuardTrace guarding .nil
  | cons {entry : Entry signature} {rest : List (Entry signature)}
      {data : BlockEncoding entry.arity}
      {head : Representation entry.block entry.symbols guarding.encoding data}
      {tail : Represented guarding.encoding rest}
      (command : GuardCommand head)
      (rest : GuardTrace guarding tail) :
      GuardTrace guarding (.cons head tail)

namespace GuardTrace

/-- Exact recursive guard commands in dependency order. -/
def commands {guarding : SMT.Guarding (Symbol signature)} :
    {env : List (Entry signature)} →
      {represented : Represented guarding.encoding env} →
      GuardTrace guarding represented → Array Crush.SMT.Command
  | [], .nil, .nil => #[]
  | _ :: _, .cons _ _, .cons command rest =>
      #[command.command] ++ rest.commands

/-- An identifier allocation uses the exact names retained by every recursive
guard command. This is static syntax/provenance evidence and does not depend on
a target model or semantic predicate. -/
def Matches
    {guarding : SMT.Guarding (Symbol signature)}
    (ident : FO.FOSort → Option Crush.SMT.Ident) :
    {env : List (Entry signature)} →
      {represented : Represented guarding.encoding env} →
      GuardTrace guarding represented → Prop
  | [], .nil, .nil => True
  | _ :: _, .cons _ _, .cons command rest =>
      (∀ child, ident (.base child.decl.sort) =
        some (.symb (command.name child))) ∧ rest.Matches ident

end GuardTrace

namespace GuardCommand

/-- Global unary-identifier injectivity and unique datatype sort ownership make
the names of one mutual guard definition injective. -/
theorem name_injective
    {entry : Entry signature} {data : BlockEncoding entry.arity}
    {guarding : SMT.Guarding (Symbol signature)}
    {head : Representation entry.block entry.symbols guarding.encoding data}
    (command : GuardCommand head)
    (ident : FO.FOSort → Option Crush.SMT.Ident)
    (ident_injective : ∀ {left right identifier},
      ident left = some identifier → ident right = some identifier →
        left = right)
    (linked : ∀ child, ident (.base child.decl.sort) =
      some (.symb (command.name child))) :
    Function.Injective command.name := by
  intro left right equal
  have rightMatch : ident (.base right.decl.sort) =
      some (.symb (command.name left)) := by
    simpa [equal] using linked right
  have sortEq := ident_injective (linked left) rightMatch
  injection sortEq with baseEq
  exact head.wf.blockWF.data_eq baseEq

end GuardCommand

/-- Carry one command from its installation point through an entire later
dependency suffix. -/
theorem After.command_valid
    {earlierArity : Nat} {earlierBlock : Block earlierArity}
    {earlierSymbols : Symbols signature earlierBlock}
    {fo : SMT.Encoding (Symbol signature)}
    {earlierData : BlockEncoding earlierArity}
    {earlier : Representation earlierBlock earlierSymbols fo earlierData}
    {env : List (Entry signature)}
    {tail : Represented fo env}
    (after : After earlier tail)
    (sourceModel : Model signature)
    (lawful : Lawful sourceModel env)
    (wf : BlocksWF env)
    (prior : Lifted (canonicalModel sourceModel))
    (valid : (SMT.model fo prior.target).SatisfiesCommand
      (command earlierBlock earlierData)) :
    (SMT.model fo
      (liftFrom sourceModel env lawful wf prior).target).SatisfiesCommand
      (command earlierBlock earlierData) := by
  induction after generalizing prior with
  | nil =>
      cases lawful
      cases wf
      exact valid
  | @cons entry rest data later tail before after ih =>
      cases lawful with
      | cons headLaw tailLaw =>
          cases wf with
          | cons headWF tailWF =>
              let next := prior.extend headLaw.flattened headWF
                headLaw.productive
              let step : Step (canonicalModel sourceModel) := {
                arity := entry.arity
                block := entry.block
                symbols := entry.symbols
                law := headLaw.flattened
                wf := headWF
                productive := headLaw.productive
                prior := prior }
              have carried := before.carried headLaw.flattened headWF
                headLaw.productive prior
              have nextValid : (SMT.model fo next.target).SatisfiesCommand
                  (command earlierBlock earlierData) := by
                simpa [next, step, Step.target, Lifted.extend] using
                  step.command_sound_carry earlier carried valid
              exact ih tailLaw tailWF next nextValid

/-- The guard equation established when an earlier block is installed survives
the complete later dependency suffix. The final predicate is the guard of the
single composed source-to-final carrier relation. -/
theorem After.guardLaw
    {earlierArity : Nat} {earlierBlock : Block earlierArity}
    {earlierSymbols : Symbols signature earlierBlock}
    {fo : SMT.Encoding (Symbol signature)}
    {earlierData : BlockEncoding earlierArity}
    {earlier : Representation earlierBlock earlierSymbols fo earlierData}
    {env : List (Entry signature)}
    {tail : Represented fo env}
    (after : After earlier tail)
    (sourceModel : Model signature)
    (lawful : Lawful sourceModel env)
    (wf : BlocksWF env)
    (prior : Lifted (canonicalModel sourceModel))
    (law : earlier.GuardLaw prior.target
      (fun sort => (prior.relation sort).guard)) :
    earlier.GuardLaw
      (liftFrom sourceModel env lawful wf prior).target
      (fun sort =>
        ((liftFrom sourceModel env lawful wf prior).relation sort).guard) := by
  induction after generalizing prior with
  | nil =>
      cases lawful
      cases wf
      exact law
  | @cons entry rest data later tail before after ih =>
      cases lawful with
      | cons headLaw tailLaw =>
          cases wf with
          | cons headWF tailWF =>
              let step : Step (canonicalModel sourceModel) := {
                arity := entry.arity
                block := entry.block
                symbols := entry.symbols
                law := headLaw.flattened
                wf := headWF
                productive := headLaw.productive
                prior := prior }
              let next := step.prior.extend step.law step.wf step.productive
              have carried := before.carried headLaw.flattened headWF
                headLaw.productive prior
              have nextLaw := step.guardLaw_carry earlier carried
                (fun sort => (step.prior.relation sort).guard)
                (fun sort => (next.relation sort).guard)
                (by
                  intro sort external value
                  dsimp only [next, Lifted.extend]
                  cases sort with
                  | bool => rfl
                  | fn domain codomain => rfl
                  | base base =>
                      change (BaseLift.rel step.wf step.productive
                        step.prior.relation.base step.law.carrier base).guard
                          value ↔ _
                      rw [BaseLift.rel_external step.wf step.productive
                        step.prior.relation.base step.law.carrier base external]
                      rfl)
                (by simpa [step] using law)
              exact ih tailLaw tailWF next nextLaw

/-- Validate one block's exact recursive guard command after every later
dependency block has been installed. The canonical guard equation is derived at
the installation step and transported internally through the suffix. -/
theorem After.wfDefs_valid
    {entry : Entry signature} {data : BlockEncoding entry.arity}
    {fo : SMT.Encoding (Symbol signature)}
    {head : Representation entry.block entry.symbols fo data}
    {env : List (Entry signature)} {tail : Represented fo env}
    (after : After head tail)
    (sourceModel : Model signature)
    (headLaw : Datatype.Lawful entry.symbols sourceModel)
    (headWF : entry.block.WF)
    (tailLaw : Lawful sourceModel env) (tailWF : BlocksWF env)
    (prior : Lifted (canonicalModel sourceModel))
    (guarding : SMT.Guarding (Symbol signature))
    (encodingEq : guarding.encoding = fo)
    (extra : SMT.ExtraGraph guarding.encoding
      (liftFrom sourceModel env tailLaw tailWF
        (prior.extend headLaw.flattened headWF headLaw.productive)).target)
    (semantics : guarding.TermSemantics
      (liftFrom sourceModel env tailLaw tailWF
        (prior.extend headLaw.flattened headWF headLaw.productive)).target
      extra
      (fun sort => ((liftFrom sourceModel env tailLaw tailWF
        (prior.extend headLaw.flattened headWF headLaw.productive)).relation
          sort).guard))
    (functional : Crush.SMT.ApplyUnique
      (SMT.modelWith guarding.encoding
        (liftFrom sourceModel env tailLaw tailWF
          (prior.extend headLaw.flattened headWF headLaw.productive)).target
        extra))
    (guardName binder : DataRef entry.block → String)
    (nameInj : Function.Injective guardName)
    (notBuiltin : ∀ child, Crush.SMT.NotBuiltin (.symb (guardName child)))
    (hasType : ∀ child, Crush.SMT.SymbolHasType
      (SMT.modelWith guarding.encoding
        (liftFrom sourceModel env tailLaw tailWF
          (prior.extend headLaw.flattened headWF headLaw.productive)).target
        extra)
      (.symb (guardName child))
      [guarding.encoding.sort (.base child.decl.sort)]
      (guarding.encoding.sort .bool))
    (applies : ∀ child value output,
      (SMT.modelWith guarding.encoding
        (liftFrom sourceModel env tailLaw tailWF
          (prior.extend headLaw.flattened headWF headLaw.productive)).target
        extra).apply
          (.symb (guardName child))
          [.typed (.base child.decl.sort) value] output ↔
        output = .typed .bool
          (((liftFrom sourceModel env tailLaw tailWF
            (prior.extend headLaw.flattened headWF headLaw.productive)).relation
              (.base child.decl.sort)).guard value)) :
    (SMT.modelWith guarding.encoding
      (liftFrom sourceModel env tailLaw tailWF
        (prior.extend headLaw.flattened headWF headLaw.productive)).target
      extra).SatisfiesCommand
        (.defFunsRec (wfDefs (native := entry.symbols.native) guarding data
          guardName binder)) := by
  let next := prior.extend headLaw.flattened headWF headLaw.productive
  have initial := head.guardLaw_extend headLaw.flattened headWF
    headLaw.productive prior.relation prior.models
  have nextLaw : head.GuardLaw next.target
      (fun sort => (next.relation sort).guard) := by
    apply initial.congr
    intro sort value
    rfl
  have finalLaw := after.guardLaw sourceModel tailLaw tailWF next nextLaw
  exact wfDefs_valid_of_guard head guarding encodingEq extra
    (fun sort => ((liftFrom sourceModel env tailLaw tailWF next).relation
      sort).guard)
    semantics functional guardName binder nameInj notBuiltin hasType applies
    (by simpa [next] using finalLaw)

/-- Every dependency-ordered recursive guard command is valid in one final
graph-extended target model. Native datatype predicates, interpreted guards,
and all mutually recursive `wf_T` definitions therefore share one model. -/
theorem Ordered.guards_valid
    {guarding : SMT.Guarding (Symbol signature)}
    {env : List (Entry signature)}
    {represented : Represented guarding.encoding env}
    (ordered : Ordered represented)
    (trace : GuardTrace guarding represented)
    (sourceModel : Model signature)
    (lawful : Lawful sourceModel env)
    (prior : Lifted (canonicalModel sourceModel))
    (guards : SMT.UnaryGuards guarding.encoding
      (liftFrom sourceModel env lawful represented.blocksWF prior).target
      (fun sort => ((liftFrom sourceModel env lawful represented.blocksWF
        prior).relation sort).guard))
    (base : SMT.ExtraGraph guarding.encoding
      (liftFrom sourceModel env lawful represented.blocksWF prior).target)
    (baseUnique : Crush.SMT.ApplyUnique
      (SMT.modelWith guarding.encoding
        (liftFrom sourceModel env lawful represented.blocksWF prior).target
        base))
    (fresh : guards.Fresh base)
    (semantics : guarding.TermSemantics
      (liftFrom sourceModel env lawful represented.blocksWF prior).target
      (guards.over base)
      (fun sort => ((liftFrom sourceModel env lawful represented.blocksWF
        prior).relation sort).guard))
    (linked : trace.Matches guards.ident) :
    (SMT.modelWith guarding.encoding
      (liftFrom sourceModel env lawful represented.blocksWF prior).target
      (guards.over base)).SatisfiesCommands trace.commands := by
  induction ordered generalizing prior with
  | nil =>
      cases trace
      cases lawful
      exact Crush.SMT.Model.satisfiesCommands_empty _
  | @cons entry rest data head tail after ordered ih =>
      cases trace with
      | cons command restTrace =>
          cases lawful with
          | cons headLaw tailLaw =>
              let next := prior.extend headLaw.flattened head.wf.blockWF
                headLaw.productive
              have headLinked := linked.1
              have tailLinked := linked.2
              have headValid :
                  (SMT.modelWith guarding.encoding
                    (liftFrom sourceModel rest tailLaw tail.blocksWF next).target
                    (guards.over base)).SatisfiesCommand command.command := by
                rw [command.command_eq]
                apply after.wfDefs_valid sourceModel headLaw head.wf.blockWF
                  tailLaw tail.blocksWF prior guarding rfl (guards.over base)
                  semantics
                  (guards.applyUnique_over base baseUnique fresh)
                  command.name command.binder
                  (command.name_injective guards.ident guards.ident_injective
                    headLinked)
                · intro child
                  exact guards.notBuiltin _ _ (headLinked child)
                · intro child
                  exact guards.hasType_over base baseUnique fresh
                    (headLinked child)
                · intro child value output
                  exact guards.applies_iff_over base fresh
                    (headLinked child) value output
              have tailValid := ih restTrace tailLaw next guards base
                baseUnique fresh semantics tailLinked
              change (SMT.modelWith guarding.encoding
                (liftFrom sourceModel rest tailLaw tail.blocksWF next).target
                (guards.over base)).SatisfiesCommands
                  (#[command.command] ++ restTrace.commands)
              rw [Crush.SMT.Model.satisfiesCommands_append]
              exact ⟨by
                simpa using Crush.SMT.Model.satisfiesCommands_push
                  (SMT.modelWith guarding.encoding
                    (liftFrom sourceModel rest tailLaw tail.blocksWF next).target
                    (guards.over base))
                  (Crush.SMT.Model.satisfiesCommands_empty _) headValid,
                tailValid⟩

/-- All dependency-ordered native datatype commands are simultaneously valid
in the single final lifted target. -/
theorem Ordered.commands_valid
    {fo : SMT.Encoding (Symbol signature)}
    {env : List (Entry signature)}
    {represented : Represented fo env}
    (ordered : Ordered represented)
    (sourceModel : Model signature)
    (lawful : Lawful sourceModel env)
    (wf : BlocksWF env)
    (prior : Lifted (canonicalModel sourceModel)) :
    (SMT.model fo
        (liftFrom sourceModel env lawful wf prior).target).SatisfiesCommands
      represented.commands := by
  induction ordered generalizing prior with
  | nil =>
      cases lawful
      cases wf
      exact Crush.SMT.Model.satisfiesCommands_empty _
  | @cons entry rest data head tail after ordered ih =>
      cases lawful with
      | cons headLaw tailLaw =>
          cases wf with
          | cons headWF tailWF =>
              let next := prior.extend headLaw.flattened headWF
                headLaw.productive
              have installed : (SMT.model fo next.target).SatisfiesCommand
                  (command entry.block data) := by
                simpa [next] using
                  extend_sound headLaw.flattened prior headWF
                    headLaw.productive head
              have headValid := after.command_valid sourceModel tailLaw tailWF
                next installed
              have tailValid := ih tailLaw tailWF next
              change (SMT.model fo
                (liftFrom sourceModel rest tailLaw tailWF next).target).SatisfiesCommands
                (#[command entry.block data] ++ tail.commands)
              rw [Crush.SMT.Model.satisfiesCommands_append]
              exact ⟨by
                simpa using Crush.SMT.Model.satisfiesCommands_push
                  (SMT.model fo
                    (liftFrom sourceModel rest tailLaw tailWF next).target)
                  (Crush.SMT.Model.satisfiesCommands_empty _) headValid,
                tailValid⟩

end Step

end Crush.Metatheory.SMT.Datatype.Native

namespace Crush.Metatheory.SMT.Datatype

open Crush.Metatheory.Datatype
open Crush.Metatheory.Defunctionalization.Flattened
open Crush.Metatheory.Datatype.Env (Lawful liftFrom)

/-- Any `ExtraGraph` is inactive on a represented native datatype block: every
raw constructor, selector, and tester identifier is the encoding of an owned
source symbol, and `ExtraGraph.source_fresh` excludes exactly those identifiers. -/
theorem Representation.extra_inactive
    {signature : Signature} {arity : Nat} {block : Block arity}
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Representation block symbols fo data)
    (target : FO.FamilyModel (Symbol signature))
    (extra : SMT.ExtraGraph fo target) :
    extra.InactiveOnDatatypes (entries block data) := by
  intro identifier member values output applied
  simp only [Crush.SMT.datatypeSymbols, List.mem_flatMap] at member
  rcases member with ⟨⟨sort, rawCtor⟩, ctorMem, role⟩
  obtain ⟨child, ctor, ctorRef, sortEq, ctorEq⟩ := raw_ctor_ref data ctorMem
  rw [ctorEq] at role
  simp only [List.mem_cons, List.mem_map] at role
  rcases role with ctorRole | testerRole | selectorRole
  · have identEq : identifier = fo.ident (symbols.native.ctor ctorRef) := by
      rw [represented.native_ctor_ident ctorRef]
      simpa [ctorDecl] using ctorRole
    rw [identEq] at applied
    exact extra.source_fresh (symbols.native.ctor ctorRef) values output applied
  · have identEq : identifier = fo.ident (symbols.native.test ctorRef) := by
      rw [represented.native_test_ident ctorRef]
      simpa [Crush.SMT.CtorDecl.tester, ctorDecl] using testerRole
    rw [identEq] at applied
    exact extra.source_fresh (symbols.native.test ctorRef) values output applied
  · rcases selectorRole with ⟨selector, selectorMem, identifierEq⟩
    have mapped : selector ∈ ctor.fields.mapIdx fun index field =>
        (data.name (.sel child ctorRef.index index),
          fieldSort (block := block) data field.sort) := by
      simpa [ctorDecl] using selectorMem
    rw [List.mem_mapIdx] at mapped
    rcases mapped with ⟨index, inBounds, selectorEq⟩
    let field := ctor.fields[index]
    let fieldRef : FieldRef ctor field :=
      Ref.ofIdx ctor.fields index inBounds
    have indexEq : fieldRef.index = index :=
      Ref.index_ofIdx ctor.fields index inBounds
    have identEq : identifier = fo.ident
        (symbols.native.sel ctorRef fieldRef) := by
      rw [represented.native_sel_ident ctorRef fieldRef]
      rw [← identifierEq]
      simpa [field, indexEq] using congrArg Prod.fst selectorEq.symm
    rw [identEq] at applied
    exact extra.source_fresh (symbols.native.sel ctorRef fieldRef)
      values output applied

/-- A represented native command sequence remains valid after installing any
derived graph fresh for encoded source symbols. -/
theorem Represented.commands_with_extra
    {signature : Signature} {fo : SMT.Encoding (Symbol signature)}
    {env : List (Entry signature)} (represented : Represented fo env)
    (target : FO.FamilyModel (Symbol signature))
    (extra : SMT.ExtraGraph fo target)
    (valid : (SMT.model fo target).SatisfiesCommands represented.commands) :
    (SMT.modelWith fo target extra).SatisfiesCommands represented.commands := by
  induction represented with
  | nil => exact Crush.SMT.Model.satisfiesCommands_empty _
  | @cons entry rest data head tail ih =>
      rw [Represented.commands] at valid ⊢
      have parts := (Crush.SMT.Model.satisfiesCommands_append _ _ _).mp valid
      have headValid : (SMT.model fo target).SatisfiesCommand
          (command entry.block data) :=
        parts.1 _ (by simp)
      have headWith := datatypeCommand_with_extra fo target extra
        (entries entry.block data) (head.extra_inactive target extra) headValid
      have headWith' : (SMT.modelWith fo target extra).SatisfiesCommand
          (command entry.block data) := by
        simpa [command] using headWith
      rw [Crush.SMT.Model.satisfiesCommands_append]
      exact ⟨by
        simpa using Crush.SMT.Model.satisfiesCommands_push
          (SMT.modelWith fo target extra)
          (Crush.SMT.Model.satisfiesCommands_empty _) headWith',
        ih parts.2⟩

/-- One block's native declaration and exact recursive `wf_T` command coexist
in the same graph-extended model. The base graph may be `IntView.extra`; unary
guards are installed over it once and supply all premises of `wfDefs_valid`. -/
theorem Native.block_valid_with_guards
    {signature : Signature} {arity : Nat} {block : Block arity}
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Representation block symbols fo data)
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful symbols.native source)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (guards : SMT.UnaryGuards fo
      (law.extend wf productive prior priorRel priorModels)
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard))
    (omitted : ∀ sort, guards.ident sort = none → ∀ value,
      (BaseLift.carrierRel wf productive priorRel law.carrier sort).guard value)
    (base : SMT.ExtraGraph fo
      (law.extend wf productive prior priorRel priorModels))
    (baseUnique : Crush.SMT.ApplyUnique
      (SMT.modelWith fo
        (law.extend wf productive prior priorRel priorModels) base))
    (fresh : guards.Fresh base)
    (guardName binder : DataRef block → String)
    (guardIdent : ∀ child, guards.ident (.base child.decl.sort) =
      some (.symb (guardName child)))
    (nameInj : Function.Injective guardName) :
    (SMT.modelWith fo
      (law.extend wf productive prior priorRel priorModels)
      (guards.over base)).SatisfiesCommand (command block data) ∧
    (SMT.modelWith fo
      (law.extend wf productive prior priorRel priorModels)
      (guards.over base)).SatisfiesCommand
      (.defFunsRec (wfDefs (native := symbols.native) guards.guarding
        data guardName binder)) := by
  let target := law.extend wf productive prior priorRel priorModels
  have nativeOld : (SMT.model fo target).SatisfiesCommand
      (command block data) := by
    simpa [target] using Native.command_sound law wf productive priorRel
      priorModels represented
  have nativeWith : (SMT.modelWith fo target
      (guards.over base)).SatisfiesCommand (command block data) := by
    have preserved := datatypeCommand_with_extra fo target (guards.over base)
      (entries block data) (represented.extra_inactive target (guards.over base))
      (by simpa [command] using nativeOld)
    simpa [command] using preserved
  refine ⟨by simpa [target] using nativeWith, ?_⟩
  apply wfDefs_valid represented law represented.exclusive wf productive
    priorRel priorModels guards.guarding rfl (guards.over base)
    (guards.termSemantics_over base omitted)
    (guards.applyUnique_over base baseUnique fresh) guardName binder nameInj
  · intro child
    exact guards.notBuiltin _ _ (guardIdent child)
  · intro child
    exact guards.hasType_over base baseUnique fresh (guardIdent child)
  · intro child value output
    exact guards.applies_iff_over base fresh (guardIdent child) value output

/-- Specialization of `block_valid_with_guards` to the production integer graph.
The resulting model interprets numerals, `(>= · 0)`, datatype guards, and native
datatype symbols simultaneously. -/
theorem Native.block_valid_with_int
    {signature : Signature} {arity : Nat} {block : Block arity}
    {symbols : Symbols signature block}
    {fo : SMT.Encoding (Symbol signature)} {data : BlockEncoding arity}
    (represented : Representation block symbols fo data)
    {source prior : FO.FamilyModel (Symbol signature)}
    (law : FamilyLawful symbols.native source)
    (wf : block.WF) (productive : Productive block)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    (guards : SMT.UnaryGuards fo
      (law.extend wf productive prior priorRel priorModels)
      (fun sort => (BaseLift.carrierRel wf productive priorRel law.carrier
        sort).guard))
    (omitted : ∀ sort, guards.ident sort = none → ∀ value,
      (BaseLift.carrierRel wf productive priorRel law.carrier sort).guard value)
    (view : SMT.IntView fo
      (law.extend wf productive prior priorRel priorModels))
    (separate : ∀ sort identifier, guards.ident sort = some identifier →
      identifier ≠ .symb ">=")
    (guardName binder : DataRef block → String)
    (guardIdent : ∀ child, guards.ident (.base child.decl.sort) =
      some (.symb (guardName child)))
    (nameInj : Function.Injective guardName) :
    (SMT.modelWith fo
      (law.extend wf productive prior priorRel priorModels)
      (guards.over view.extra)).SatisfiesCommand (command block data) ∧
    (SMT.modelWith fo
      (law.extend wf productive prior priorRel priorModels)
      (guards.over view.extra)).SatisfiesCommand
      (.defFunsRec (wfDefs (native := symbols.native) guards.guarding
        data guardName binder)) :=
  Native.block_valid_with_guards represented law wf productive priorRel
    priorModels guards omitted view.extra view.applyUnique
    (view.guardsFresh guards separate) guardName binder guardIdent nameInj

/-- The exact native command prefix is valid after installing every datatype
block over an arbitrary already-guarded base model. -/
theorem EnvRepresentation.liftedFrom_valid
    {signature : Signature} {fo : SMT.Encoding (Symbol signature)}
    {env : List (Entry signature)}
    (represented : EnvRepresentation fo env)
    (ordered : Native.Step.Ordered represented.blocks)
    (source : Model signature)
    (lawful : Lawful source env)
    (prior : Lifted (canonicalModel source)) :
    (SMT.model fo
      (represented.liftedFrom source lawful prior).target).SatisfiesCommands
      fo.nativeCommands := by
  rw [represented.native_eq]
  change (SMT.model fo
    (liftFrom source env lawful represented.blocks.blocksWF
      prior).target).SatisfiesCommands
    represented.blocks.commands
  exact ordered.commands_valid source lawful represented.blocks.blocksWF
    prior

/-- Identity-base specialization of `liftedFrom_valid`. -/
theorem EnvRepresentation.lifted_valid
    {signature : Signature} {fo : SMT.Encoding (Symbol signature)}
    {env : List (Entry signature)}
    (represented : EnvRepresentation fo env)
    (ordered : Native.Step.Ordered represented.blocks)
    (source : Model signature)
    (lawful : Lawful source env) :
    (SMT.model fo (represented.lifted source lawful).target).SatisfiesCommands
      fo.nativeCommands := by
  simpa [EnvRepresentation.lifted, EnvRepresentation.liftedFrom, Env.lift] using
    represented.liftedFrom_valid ordered source lawful
      (Lifted.refl (canonicalModel source))

/-- The complete native prefix remains valid over an arbitrary prior lifting
after installing the combined guard/arithmetic graph. -/
theorem EnvRepresentation.liftedFrom_valid_with
    {signature : Signature} {fo : SMT.Encoding (Symbol signature)}
    {env : List (Entry signature)} (represented : EnvRepresentation fo env)
    (ordered : Native.Step.Ordered represented.blocks)
    (source : Model signature) (lawful : Lawful source env)
    (prior : Lifted (canonicalModel source))
    (extra : SMT.ExtraGraph fo
      (represented.liftedFrom source lawful prior).target) :
    (SMT.modelWith fo (represented.liftedFrom source lawful prior).target
      extra).SatisfiesCommands
      fo.nativeCommands := by
  rw [represented.native_eq]
  exact represented.blocks.commands_with_extra _ extra
    (by
      rw [← represented.native_eq]
      exact represented.liftedFrom_valid ordered source lawful prior)

/-- Identity-base specialization of `liftedFrom_valid_with`. -/
theorem EnvRepresentation.lifted_valid_with
    {signature : Signature} {fo : SMT.Encoding (Symbol signature)}
    {env : List (Entry signature)} (represented : EnvRepresentation fo env)
    (ordered : Native.Step.Ordered represented.blocks)
    (source : Model signature) (lawful : Lawful source env)
    (extra : SMT.ExtraGraph fo (represented.lifted source lawful).target) :
    (SMT.modelWith fo (represented.lifted source lawful).target extra).SatisfiesCommands
      fo.nativeCommands := by
  simpa [EnvRepresentation.lifted, EnvRepresentation.liftedFrom, Env.lift] using
    represented.liftedFrom_valid_with ordered source lawful
      (Lifted.refl (canonicalModel source)) extra

/-- Whole-theory model lifting over a caller-supplied interpreted or guarded
base model. Native datatypes, derived graphs, ordinary declarations, and
assertions share one raw model. -/
theorem EnvRepresentation.soundFrom
    {signature : Signature} {fo : SMT.Encoding (Symbol signature)}
    {env : List (Entry signature)} (represented : EnvRepresentation fo env)
    (ordered : Native.Step.Ordered represented.blocks)
    {theory : FO.FamilyTheory (Symbol signature)}
    {commands : Array Crush.SMT.Command}
    (representation : SMT.TheoryRepresentation fo theory commands)
    (source : Model signature) (lawful : Lawful source env)
    (prior : Lifted (canonicalModel source))
    (extra : SMT.ExtraGraph fo
      (represented.liftedFrom source lawful prior).target)
    (valid : (represented.liftedFrom source lawful prior).target.SatisfiesTheory
      theory) :
    ∃ model : Crush.SMT.Model, model.SatisfiesCommands commands :=
  SMT.lift_with_extra fo representation
    (represented.liftedFrom source lawful prior).target valid extra
    (represented.liftedFrom_valid_with ordered source lawful prior extra)

/-- Identity-base specialization of `soundFrom`. -/
theorem EnvRepresentation.sound_with
    {signature : Signature} {fo : SMT.Encoding (Symbol signature)}
    {env : List (Entry signature)} (represented : EnvRepresentation fo env)
    (ordered : Native.Step.Ordered represented.blocks)
    {theory : FO.FamilyTheory (Symbol signature)}
    {commands : Array Crush.SMT.Command}
    (representation : SMT.TheoryRepresentation fo theory commands)
    (source : Model signature) (lawful : Lawful source env)
    (extra : SMT.ExtraGraph fo (represented.lifted source lawful).target)
    (valid : (represented.lifted source lawful).target.SatisfiesTheory theory) :
    ∃ model : Crush.SMT.Model, model.SatisfiesCommands commands := by
  simpa [EnvRepresentation.lifted, EnvRepresentation.liftedFrom, Env.lift] using
    represented.soundFrom ordered representation source lawful
      (Lifted.refl (canonicalModel source)) extra valid

end Crush.Metatheory.SMT.Datatype
