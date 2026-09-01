import Crush.Metatheory.SMT.ModelExtension
import Crush.Metatheory.SMT.DatatypeCanonical

/-!
# Semantic soundness of FO-to-SMT representation

Every model of an intrinsically typed FO theory induces a model of its concrete
SMT representation. Values from the FO model are tagged by their typed
sort.  Raw values are used only for SMT sorts outside the representation image,
which preserves the standard nonemptiness requirement without confusing two
represented carriers.
-/

namespace Crush.Metatheory.SMT

open Defunctionalization.Flattened
open Crush.SMT.Model (satisfiesCommands_append)
open scoped Crush.Metatheory
open scoped Crush.SMT

variable {symbols : FO.SymbolFamily}

/-- Each ordinary symbol declaration emitted by the pure encoder is satisfied
by the same induced model used for native symbols. -/
theorem declaration_valid (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (declared : Declaration symbols)
    (ordinary : encoding.nativeSymbol declared.symbol = false) :
    (model encoding target).SatisfiesCommand (declaration encoding declared) := by
  rw [declaration]
  change Crush.SMT.SymbolHasType (model encoding target)
    (.symb (encoding.name declared.symbol))
    (declared.declaration.args.map encoding.sort)
    (encoding.sort declared.declaration.result)
  rw [← encoding.ordinary_ident declared.symbol ordinary]
  exact symbol_has_type encoding target declared.symbol

/-- Semantic argument values, tagged in the same order as their SMT terms. -/
def argumentValues (target : FO.FamilyModel symbols)
    {context : FO.Context} (valuation : FO.FamilyValuation target context) :
    {sorts : List FO.FOSort} → FO.FamilyArgs symbols context sorts →
      List (Value target)
  | [], .nil => []
  | _ :: _, .cons (sort := sort) argument rest =>
      .typed sort ⟦argument⟧[target, valuation] ::
        argumentValues target valuation rest

/-- Decoding the tagged argument list recovers ordinary curried FO
application. -/
theorem applyValues_argumentValues (target : FO.FamilyModel symbols)
    {context : FO.Context} (valuation : FO.FamilyValuation target context)
    {sorts : List FO.FOSort} (args : FO.FamilyArgs symbols context sorts)
    {result : FO.FOSort}
    (function : FO.SymbolDenote target.carriers sorts result) :
    applyValues target sorts function (argumentValues target valuation args) =
      args.apply target valuation function := by
  exact FO.FamilyArgs.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun context sorts args =>
      ∀ (valuation : FO.FamilyValuation target context) {result : FO.FOSort}
        (function : FO.SymbolDenote target.carriers sorts result),
        applyValues target sorts function (argumentValues target valuation args) =
          args.apply target valuation function)
    (var := fun _ => trivial)
    (symbol := fun _ _ _ => trivial)
    (boolLit := fun _ => trivial)
    (not := fun _ _ => trivial)
    (and := fun _ _ _ _ => trivial)
    (or := fun _ _ _ _ => trivial)
    (imp := fun _ _ _ _ => trivial)
    (iff := fun _ _ _ _ => trivial)
    (eq := fun _ _ _ _ => trivial)
    (forallE := fun _ _ => trivial)
    (existsE := fun _ _ => trivial)
    (nil := by
      intro context valuation result function
      simp only [applyValues, FO.FamilyArgs.apply.eq_1])
    (cons := fun argument rest argumentIH restIH => by
      intro valuation result function
      simp only [argumentValues, applyValues, decode_typed,
        FO.FamilyArgs.apply.eq_2]
      exact restIH valuation _)
    args valuation function

/-- A typed FO valuation and an SMT environment carry the same values, nearest
binder first. -/
def Env (target : FO.FamilyModel symbols) {context : FO.Context}
    (valuation : FO.FamilyValuation target context)
    (environment : List (Value target)) : Prop :=
  ∀ {sort : FO.FOSort} (ref : FO.Var context sort),
    environment[varIndex ref]? = some (.typed sort (valuation ref))

theorem Env.empty (target : FO.FamilyModel symbols) :
    Env target (FO.Valuation.empty target.carriers) [] := by
  intro sort ref
  nomatch ref

theorem Env.cons (target : FO.FamilyModel symbols)
    {context : FO.Context} {sort : FO.FOSort}
    {valuation : FO.FamilyValuation target context}
    {environment : List (Value target)}
    (related : Env target valuation environment)
    (value : sort.Denote target.carriers) :
    Env target (valuation.extend value) (.typed sort value :: environment) := by
  intro result ref
  cases ref with
  | here => rfl
  | there ref =>
      change environment[varIndex ref]? = some (.typed _ (valuation ref))
      exact related ref

/-- Related environments agree at every typed de Bruijn reference. -/
theorem Env.lookup (target : FO.FamilyModel symbols) :
    ∀ {context : FO.Context} {sort : FO.FOSort}
      {valuation : FO.FamilyValuation target context}
      {environment : List (Value target)},
      Env target valuation environment → (ref : FO.Var context sort) →
      environment[varIndex ref]? = some (.typed sort (valuation ref))
  | _, _, _, _, related, ref => related ref

private theorem eval_true (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {environment : List (Value target)}
    {source : STerm} {proposition : Prop}
    (evaluated : Crush.SMT.Eval (model encoding target) environment source
      (.typed .bool proposition))
    (valid : proposition) :
    Crush.SMT.Eval (model encoding target) environment source
      ((model encoding target).bool true) := by
  have equal : proposition = True := propext ⟨fun _ => trivial, fun _ => valid⟩
  simpa only [model, boolValue, equal] using evaluated

private theorem eval_false (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {environment : List (Value target)}
    {source : STerm} {proposition : Prop}
    (evaluated : Crush.SMT.Eval (model encoding target) environment source
      (.typed .bool proposition))
    (invalid : ¬proposition) :
    Crush.SMT.Eval (model encoding target) environment source
      ((model encoding target).bool false) := by
  have equal : proposition = False := propext ⟨invalid, False.elim⟩
  simpa only [model, boolValue, equal] using evaluated

private theorem bool_ne (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) :
    (model encoding target).bool true ≠ (model encoding target).bool false := by
  intro equality
  have impossible := (model encoding target).boolInjective equality
  contradiction

private theorem eval_and (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {environment : List (Value target)}
    {left right : STerm} {leftValue rightValue : Bool}
    (leftEval : Crush.SMT.Eval (model encoding target) environment left
      ((model encoding target).bool leftValue))
    (rightEval : Crush.SMT.Eval (model encoding target) environment right
      ((model encoding target).bool rightValue)) :
    Crush.SMT.Eval (model encoding target) environment
      (smt| (and $left $right))
      ((model encoding target).bool (leftValue && rightValue)) := by
  simpa using Crush.SMT.Eval.and
    (Crush.SMT.EvalList.cons leftEval
      (Crush.SMT.EvalList.cons rightEval .nil))
    (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))

private theorem eval_or (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {environment : List (Value target)}
    {left right : STerm} {leftValue rightValue : Bool}
    (leftEval : Crush.SMT.Eval (model encoding target) environment left
      ((model encoding target).bool leftValue))
    (rightEval : Crush.SMT.Eval (model encoding target) environment right
      ((model encoding target).bool rightValue)) :
    Crush.SMT.Eval (model encoding target) environment
      (smt| (or $left $right))
      ((model encoding target).bool (leftValue || rightValue)) := by
  simpa using Crush.SMT.Eval.or
    (Crush.SMT.EvalList.cons leftEval
      (Crush.SMT.EvalList.cons rightEval .nil))
    (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))

private def TermValid (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) : Prop :=
  ∀ (valuation : FO.FamilyValuation target context)
    (environment : List (Value target)), Env target valuation environment →
    Crush.SMT.Eval (model encoding target) environment (𝒶⟦source⟧[encoding])
      (.typed sort ⟦source⟧[target, valuation])

private def ArgsValid (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {context : FO.Context}
    {sorts : List FO.FOSort} (source : FO.FamilyArgs symbols context sorts) : Prop :=
  ∀ (valuation : FO.FamilyValuation target context)
    (environment : List (Value target)), Env target valuation environment →
    Crush.SMT.EvalList (model encoding target) environment
      (arguments encoding source).toList (argumentValues target valuation source)

/-- The pure term representation preserves denotation in the induced SMT
model. -/
theorem term_eval (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) : TermValid encoding target source := by
  classical
  exact FO.FamilyTerm.rec
    (motive_1 := fun _ _ source => TermValid encoding target source)
    (motive_2 := fun _ _ args => ArgsValid encoding target args)
    (var := fun ref => by
      intro valuation environment related
      simpa only [term, encodeTerm, FO.FamilyTerm.denote.eq_1] using
        Crush.SMT.Eval.bvar (related.lookup target ref))
    (symbol := fun symbol args argsIH => by
      intro valuation environment related
      have result : Crush.SMT.Eval (model encoding target) environment
          (.app (encoding.ident symbol) (arguments encoding args))
          (.typed _ (args.apply target valuation (target.symbol symbol))) := by
        apply Crush.SMT.Eval.symbol
          (encoding.ident_fresh symbol).notLogicalBuiltin
          (argsIH valuation environment related)
        refine ⟨_, symbol, rfl, ?_⟩
        rw [applyValues_argumentValues]
      simpa only [term, encodeTerm, arguments,
        FO.FamilyTerm.denote.eq_2] using result)
    (boolLit := fun value => by
      intro valuation environment related
      cases value <;> simpa only [term, encodeTerm, FO.FamilyTerm.denote.eq_3,
        FO.FamilyTerm.denote.eq_4, model, boolValue] using
          (Crush.SMT.Eval.boolLit (model := model encoding target)
            (environment := environment) _))
    (not := fun body bodyIH => by
      intro valuation environment related
      let bodyEval := bodyIH valuation environment related
      by_cases valid : ⟦body⟧[target, valuation]
      · have result := Crush.SMT.Eval.not (eval_true encoding target bodyEval valid)
        simpa [term, model, boolValue, valid] using result
      · have result := Crush.SMT.Eval.not (eval_false encoding target bodyEval valid)
        simpa [term, model, boolValue, valid] using result)
    (and := fun left right leftIH rightIH => by
      intro valuation environment related
      let leftEval := leftIH valuation environment related
      let rightEval := rightIH valuation environment related
      by_cases leftValid : ⟦left⟧[target, valuation] <;>
        by_cases rightValid : ⟦right⟧[target, valuation]
      all_goals
        first
        | have result := eval_and encoding target
            (eval_true encoding target leftEval leftValid)
            (eval_true encoding target rightEval rightValid)
        | have result := eval_and encoding target
            (eval_true encoding target leftEval leftValid)
            (eval_false encoding target rightEval rightValid)
        | have result := eval_and encoding target
            (eval_false encoding target leftEval leftValid)
            (eval_true encoding target rightEval rightValid)
        | have result := eval_and encoding target
            (eval_false encoding target leftEval leftValid)
            (eval_false encoding target rightEval rightValid)
      all_goals simpa [term, model, boolValue, leftValid, rightValid] using result)
    (or := fun left right leftIH rightIH => by
      intro valuation environment related
      let leftEval := leftIH valuation environment related
      let rightEval := rightIH valuation environment related
      by_cases leftValid : ⟦left⟧[target, valuation] <;>
        by_cases rightValid : ⟦right⟧[target, valuation]
      all_goals
        first
        | have result := eval_or encoding target
            (eval_true encoding target leftEval leftValid)
            (eval_true encoding target rightEval rightValid)
        | have result := eval_or encoding target
            (eval_true encoding target leftEval leftValid)
            (eval_false encoding target rightEval rightValid)
        | have result := eval_or encoding target
            (eval_false encoding target leftEval leftValid)
            (eval_true encoding target rightEval rightValid)
        | have result := eval_or encoding target
            (eval_false encoding target leftEval leftValid)
            (eval_false encoding target rightEval rightValid)
      all_goals simpa [term, model, boolValue, leftValid, rightValid] using result)
    (imp := fun left right leftIH rightIH => by
      intro valuation environment related
      let leftEval := leftIH valuation environment related
      let rightEval := rightIH valuation environment related
      by_cases leftValid : ⟦left⟧[target, valuation] <;>
        by_cases rightValid : ⟦right⟧[target, valuation]
      all_goals
        first
        | have result := Crush.SMT.Eval.imp
            (eval_true encoding target leftEval leftValid)
            (eval_true encoding target rightEval rightValid)
        | have result := Crush.SMT.Eval.imp
            (eval_true encoding target leftEval leftValid)
            (eval_false encoding target rightEval rightValid)
        | have result := Crush.SMT.Eval.imp
            (eval_false encoding target leftEval leftValid)
            (eval_true encoding target rightEval rightValid)
        | have result := Crush.SMT.Eval.imp
            (eval_false encoding target leftEval leftValid)
            (eval_false encoding target rightEval rightValid)
      all_goals simpa [term, model, boolValue, leftValid, rightValid] using result)
    (iff := fun left right leftIH rightIH => by
      intro valuation environment related
      let leftEval := leftIH valuation environment related
      let rightEval := rightIH valuation environment related
      by_cases leftValid : ⟦left⟧[target, valuation] <;>
        by_cases rightValid : ⟦right⟧[target, valuation]
      · have result := Crush.SMT.Eval.eqTrue
          (eval_true encoding target leftEval leftValid)
          (eval_true encoding target rightEval rightValid) rfl
        simpa [term, model, boolValue, leftValid, rightValid] using result
      · have result := Crush.SMT.Eval.eqFalse
          (eval_true encoding target leftEval leftValid)
          (eval_false encoding target rightEval rightValid)
          (bool_ne encoding target)
        simpa [term, model, boolValue, leftValid, rightValid] using result
      · have result := Crush.SMT.Eval.eqFalse
          (eval_false encoding target leftEval leftValid)
          (eval_true encoding target rightEval rightValid)
          (bool_ne encoding target).symm
        simpa [term, model, boolValue, leftValid, rightValid] using result
      · have result := Crush.SMT.Eval.eqTrue
          (eval_false encoding target leftEval leftValid)
          (eval_false encoding target rightEval rightValid) rfl
        simpa [term, model, boolValue, leftValid, rightValid] using result)
    (eq := fun left right leftIH rightIH => by
      intro valuation environment related
      let leftEval := leftIH valuation environment related
      let rightEval := rightIH valuation environment related
      by_cases equal : ⟦left⟧[target, valuation] = ⟦right⟧[target, valuation]
      · have result := Crush.SMT.Eval.eqTrue leftEval rightEval
          (congrArg (Value.typed _) equal)
        simpa [term, model, boolValue, equal] using result
      · have unequal :
          Value.typed _ ⟦left⟧[target, valuation] ≠
            Value.typed _ ⟦right⟧[target, valuation] := by
          intro equality
          exact equal (Value.typed.inj equality |>.2 |> eq_of_heq)
        have result := Crush.SMT.Eval.eqFalse leftEval rightEval unequal
        simpa [term, model, boolValue, equal] using result)
    (forallE := fun body bodyIH => by
      intro valuation environment related
      by_cases valid : ∀ value, ⟦body⟧[target, valuation.extend value]
      · have result := Crush.SMT.Eval.forallTrue
          (model := model encoding target)
          (binders := #[("x", encoding.sort _)])
          (body := term encoding body) (by
            intro values valuesTyped
            cases valuesTyped with
            | cons headTyped tailTyped =>
              cases tailTyped
              obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
                encoding _ _ headTyped
              exact eval_true encoding target
                (bodyIH (valuation.extend value) _
                  (Env.cons target related value)) (valid value))
        simpa [term, model, boolValue, valid] using result
      · obtain ⟨value, invalid⟩ := Classical.not_forall.mp valid
        have result := Crush.SMT.Eval.forallFalse
          (model := model encoding target)
          (environment := environment)
          (binders := #[("x", encoding.sort _)])
          (body := term encoding body)
          (values := [Value.typed _ value])
          (Crush.SMT.ValuesTyped.cons
            (Value.inSort_typed (target := target) encoding _ value) .nil)
          (eval_false encoding target
            (bodyIH (valuation.extend value) _
              (Env.cons target related value)) invalid)
        simpa [term, model, boolValue, valid] using result)
    (existsE := fun body bodyIH => by
      intro valuation environment related
      by_cases valid : ∃ value, ⟦body⟧[target, valuation.extend value]
      · have existsValid := valid
        obtain ⟨value, bodyValid⟩ := valid
        have result := Crush.SMT.Eval.existsTrue
          (model := model encoding target)
          (environment := environment)
          (binders := #[("x", encoding.sort _)])
          (body := term encoding body)
          (values := [Value.typed _ value])
          (Crush.SMT.ValuesTyped.cons
            (Value.inSort_typed (target := target) encoding _ value) .nil)
          (eval_true encoding target
            (bodyIH (valuation.extend value) _
              (Env.cons target related value)) bodyValid)
        simpa [term, model, boolValue, existsValid] using result
      · have everyInvalid := not_exists.mp valid
        have result := Crush.SMT.Eval.existsFalse
          (model := model encoding target)
          (binders := #[("x", encoding.sort _)])
          (body := term encoding body) (by
            intro values valuesTyped
            cases valuesTyped with
            | cons headTyped tailTyped =>
              cases tailTyped
              obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
                encoding _ _ headTyped
              exact eval_false encoding target
                (bodyIH (valuation.extend value) _
                  (Env.cons target related value)) (everyInvalid value))
        simpa [term, model, boolValue, valid] using result)
    (nil := fun {_} => by
      intro valuation environment related
      exact Crush.SMT.EvalList.nil)
    (cons := fun argument rest argumentIH restIH => by
      intro valuation environment related
      rw [arguments, encodeArguments, Array.toList_append,
        List.singleton_append, argumentValues]
      change Crush.SMT.EvalList (model encoding target) environment
        (term encoding argument :: (arguments encoding rest).toList)
        (Value.typed _ ⟦argument⟧[target, valuation] ::
          argumentValues target valuation rest)
      exact Crush.SMT.EvalList.cons
        (argumentIH valuation environment related)
        (restIH valuation environment related))
    source

/-- The typed FO encoder uses only Boolean literals. Other source
constants are typed family symbols, so native components may give raw SMT
numerals their interpreted meaning without changing encoded FO evaluations. -/
theorem term_literalFree (encoding : Encoding symbols)
    {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) :
    LiteralFree (𝒶⟦source⟧[encoding]) := by
  exact FO.FamilyTerm.rec
    (motive_1 := fun _ _ source => LiteralFree (term encoding source))
    (motive_2 := fun _ _ args =>
      LiteralFreeList (arguments encoding args).toList)
    (var := fun ref => .bvar _)
    (symbol := fun symbol args argsFree => .app argsFree)
    (boolLit := fun value => by
      cases value <;> simp only [term, encodeTerm] <;> exact .bool _)
    (not := fun body bodyFree => .app (.cons bodyFree .nil))
    (and := fun left right leftFree rightFree =>
      .app (.cons leftFree (.cons rightFree .nil)))
    (or := fun left right leftFree rightFree =>
      .app (.cons leftFree (.cons rightFree .nil)))
    (imp := fun left right leftFree rightFree =>
      .app (.cons leftFree (.cons rightFree .nil)))
    (iff := fun left right leftFree rightFree =>
      .app (.cons leftFree (.cons rightFree .nil)))
    (eq := fun left right leftFree rightFree =>
      .app (.cons leftFree (.cons rightFree .nil)))
    (forallE := fun body bodyFree => .forallE bodyFree)
    (existsE := fun body bodyFree => .existsE bodyFree)
    (nil := .nil)
    (cons := fun argument rest argumentFree restFree => by
      rw [arguments, encodeArguments, Array.toList_append,
        List.singleton_append]
      exact .cons argumentFree restFree)
    source

/-- Every encoded assertion of a valid typed theory holds in the induced SMT
model. -/
theorem assertions_valid (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (source : FO.FamilyTheory symbols)
    (valid : target ⊨ᵀ source) :
    model encoding target ⊨ₛᶜ
      (source.map fun formula => .assert (𝒶⟦formula⟧[encoding])).toArray := by
  intro command membership
  have arrayMembership : command ∈
      (source.map fun formula => Crush.SMT.Command.assert
        (𝒶⟦formula⟧[encoding])).toArray :=
    Array.mem_toList_iff.mp membership
  have listMembership : command ∈
      source.map fun formula => Crush.SMT.Command.assert
        (𝒶⟦formula⟧[encoding]) := by
    simpa using arrayMembership
  rcases List.mem_map.mp listMembership with ⟨formula, formulaMem, rfl⟩
  exact eval_true encoding target
    (term_eval encoding target formula
      (FO.Valuation.empty target.carriers) [] (Env.empty target))
    (valid formula formulaMem)

/-- Every emitted symbol declaration is valid in the induced relational
symbol graph. -/
theorem declarations_valid (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (declarations : List (Declaration symbols)) :
    model encoding target ⊨ₛᶜ
      ((ordinaryDecls encoding declarations).map
        (declaration encoding)).toArray := by
  intro command membership
  have arrayMembership : command ∈
      ((ordinaryDecls encoding declarations).map
        (declaration encoding)).toArray :=
    Array.mem_toList_iff.mp membership
  have listMembership : command ∈
      (ordinaryDecls encoding declarations).map (declaration encoding) := by
    simpa using arrayMembership
  rcases List.mem_map.mp listMembership with ⟨declared, declaredMem, rfl⟩
  apply declaration_valid encoding target declared
  have filtered := List.mem_filter.mp declaredMem
  simpa using filtered.2

/-- Sort declarations carry no constraint beyond belonging to the supported
command fragment. -/
theorem sortDeclarations_valid (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (sorts : List FO.FOSort) :
    model encoding target ⊨ₛᶜ
      (sorts.filterMap (sortDeclaration? encoding)).toArray := by
  intro command membership
  have arrayMembership : command ∈
      (sorts.filterMap (sortDeclaration? encoding)).toArray :=
    Array.mem_toList_iff.mp membership
  have listMembership : command ∈
      sorts.filterMap (sortDeclaration? encoding) := by
    simpa using arrayMembership
  rcases List.mem_filterMap.mp listMembership with
    ⟨sort, sortMem, declarationEqual⟩
  unfold sortDeclaration? at declarationEqual
  split at declarationEqual <;> try contradiction
  split at declarationEqual <;> try contradiction
  cases declarationEqual
  trivial

/-! ## Composition with native derived symbols -/

/-- Ordinary source-symbol declarations remain valid in an extended model. -/
theorem declaration_valid_with (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (declared : Declaration symbols)
    (ordinary : encoding.nativeSymbol declared.symbol = false) :
    (modelWith encoding target extra).SatisfiesCommand
      (declaration encoding declared) := by
  rw [declaration]
  change Crush.SMT.SymbolHasType (modelWith encoding target extra)
    (.symb (encoding.name declared.symbol))
    (declared.declaration.args.map encoding.sort)
    (encoding.sort declared.declaration.result)
  rw [← encoding.ordinary_ident declared.symbol ordinary]
  exact symbol_has_type_with encoding target extra declared.symbol

/-- Valid encoded assertions stay valid after installing a disjoint native
graph. -/
theorem assertions_valid_with (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (source : FO.FamilyTheory symbols) (valid : target ⊨ᵀ source) :
    modelWith encoding target extra ⊨ₛᶜ
      (source.map fun formula => .assert (𝒶⟦formula⟧[encoding])).toArray := by
  intro command membership
  have arrayMembership : command ∈
      (source.map fun formula => Crush.SMT.Command.assert
        (𝒶⟦formula⟧[encoding])).toArray :=
    Array.mem_toList_iff.mp membership
  have listMembership : command ∈
      source.map fun formula => Crush.SMT.Command.assert
        (𝒶⟦formula⟧[encoding]) := by
    simpa using arrayMembership
  rcases List.mem_map.mp listMembership with ⟨formula, formulaMem, rfl⟩
  have baseEval := eval_true encoding target
    (term_eval encoding target formula
      (FO.Valuation.empty target.carriers) [] (Env.empty target))
    (valid formula formulaMem)
  have extended := eval_with_extra encoding target extra
    (term_literalFree encoding formula) baseEval
  change Crush.SMT.Eval (modelWith encoding target extra) [] _
    ((modelWith encoding target extra).bool true)
  rw [modelWith_bool, ← model_bool]
  exact extended

/-- Every ordinary declaration in the represented list is valid in the extended
model. -/
theorem declarations_valid_with (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (declarations : List (Declaration symbols)) :
    modelWith encoding target extra ⊨ₛᶜ
      ((ordinaryDecls encoding declarations).map
        (declaration encoding)).toArray := by
  intro command membership
  have arrayMembership : command ∈
      ((ordinaryDecls encoding declarations).map
        (declaration encoding)).toArray :=
    Array.mem_toList_iff.mp membership
  have listMembership : command ∈
      (ordinaryDecls encoding declarations).map (declaration encoding) := by
    simpa using arrayMembership
  rcases List.mem_map.mp listMembership with ⟨declared, declaredMem, rfl⟩
  apply declaration_valid_with encoding target extra declared
  have filtered := List.mem_filter.mp declaredMem
  simpa using filtered.2

/-- Sort declarations are graph-independent. -/
theorem sortDeclarations_valid_with (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (sorts : List FO.FOSort) :
    modelWith encoding target extra ⊨ₛᶜ
      (sorts.filterMap (sortDeclaration? encoding)).toArray := by
  intro command membership
  have arrayMembership : command ∈
      (sorts.filterMap (sortDeclaration? encoding)).toArray :=
    Array.mem_toList_iff.mp membership
  have listMembership : command ∈
      sorts.filterMap (sortDeclaration? encoding) := by
    simpa using arrayMembership
  rcases List.mem_filterMap.mp listMembership with
    ⟨sort, sortMem, declarationEqual⟩
  unfold sortDeclaration? at declarationEqual
  split at declarationEqual <;> try contradiction
  split at declarationEqual <;> try contradiction
  cases declarationEqual
  trivial

/-- Low-level composition for a shared model carrying additional native derived
symbols. This is the extension point used by certified datatype guards; all
ordinary declarations and assertions retain their existing proofs. -/
theorem lift_with_extra (encoding : Encoding symbols)
    {source : FO.FamilyTheory symbols} {commands : Array Command}
    (representation : TheoryRepresentation encoding source commands)
    (target : FO.FamilyModel symbols) (valid : target ⊨ᵀ source)
    (extra : ExtraGraph encoding target)
    (nativeValid : modelWith encoding target extra ⊨ₛᶜ
      encoding.nativeCommands) :
    ∃ smtModel : Crush.SMT.Model, smtModel ⊨ₛᶜ commands := by
  rcases representation with ⟨declarations, same⟩
  refine ⟨modelWith encoding target extra,
    ((modelWith encoding target extra).satisfiesCommands_congr same).2 ?_⟩
  simp only [theory]
  rw [satisfiesCommands_append]
  refine ⟨nativeValid, ?_⟩
  simp only [theoryBody]
  rw [satisfiesCommands_append, satisfiesCommands_append]
  exact ⟨⟨sortDeclarations_valid_with encoding target extra _,
    declarations_valid_with encoding target extra declarations⟩,
    assertions_valid_with encoding target extra source valid⟩

/-- Low-level composition shared by every native component. Public soundness
below obtains `nativeValid` from the exact component representation. -/
theorem lift (encoding : Encoding symbols)
    {source : FO.FamilyTheory symbols} {commands : Array Command}
    (representation : TheoryRepresentation encoding source commands)
    (target : FO.FamilyModel symbols) (valid : target ⊨ᵀ source)
    (nativeValid : model encoding target ⊨ₛᶜ encoding.nativeCommands) :
    ∃ smtModel : Crush.SMT.Model, smtModel ⊨ₛᶜ commands := by
  rcases representation with ⟨declarations, same⟩
  refine ⟨model encoding target,
    ((model encoding target).satisfiesCommands_congr same).2 ?_⟩
  simp only [theory]
  rw [satisfiesCommands_append]
  refine ⟨nativeValid, ?_⟩
  simp only [theoryBody]
  rw [satisfiesCommands_append, satisfiesCommands_append]
  exact ⟨⟨sortDeclarations_valid encoding target _,
    declarations_valid encoding target declarations⟩,
    assertions_valid encoding target source valid⟩

/-- Single model-lifting theorem for the complete representation. Ordinary
sorts, ordinary symbols, assertions, and every SMT datatype block are all
validated in the same induced raw model. The empty datatype environment is the
ordinary case with no SMT datatype declarations. -/
theorem representation_sound {signature : Signature}
    (encoding : Encoding (Symbol signature))
    {env : Datatype.Env signature}
    (datatypes : Datatype.EnvRepresentation encoding env)
    {theory : FO.FamilyTheory (Symbol signature)} {commands : Array Command}
    (representation : TheoryRepresentation encoding theory commands)
    (source : Model signature) (freeDataModel : Datatype.Env.IsFreeDatatypeModel source env)
    (valid : canonicalModel source ⊨ᵀ theory) :
    ∃ smtModel : Crush.SMT.Model, smtModel ⊨ₛᶜ commands :=
  lift encoding representation (canonicalModel source) valid
    (datatypes.datatypeCommands_valid freeDataModel)

/-- Unsatisfiability of the complete represented command sequence reflects
through the same theorem to the free-datatype source semantics. -/
theorem commands_unsat_implies_source_unsat {signature : Signature}
    (encoding : Encoding (Symbol signature))
    {env : Datatype.Env signature}
    (datatypes : Datatype.EnvRepresentation encoding env)
    (formula : Sentence signature) {commands : Array Command}
    (representation : TheoryRepresentation encoding
      (translatedTheory formula) commands)
    (unsat : Crush.SMT.AbstractCommandsUnsatisfiable commands) :
    Datatype.Env.Unsatisfiable env formula := by
  intro source freeDataModel sourceValid
  obtain ⟨smtModel, commandsValid⟩ :=
    representation_sound encoding datatypes representation source freeDataModel
      (model_extension source formula sourceValid)
  exact unsat.noModel smtModel commandsValid

/-- Unsatisfiability of one represented command array reflects through
flattening and SMT encoding to the complete source theory under the
free-datatype model condition. -/
theorem commands_unsat_implies_source_theory_unsat {signature : Signature}
    (encoding : Encoding (Symbol signature))
    {env : Datatype.Env signature}
    (datatypes : Datatype.EnvRepresentation encoding env)
    (sourceTheory : Theory signature) {commands : Array Command}
    (representation : TheoryRepresentation encoding
      (translatedTheories sourceTheory) commands)
    (unsat : Crush.SMT.AbstractCommandsUnsatisfiable commands) :
    Datatype.Env.TheoryUnsatisfiable env sourceTheory := by
  intro source freeDataModel sourceValid
  obtain ⟨smtModel, commandsValid⟩ :=
    representation_sound encoding datatypes representation source freeDataModel
      (model_extension_theory source sourceTheory sourceValid)
  exact unsat.noModel smtModel commandsValid


end Crush.Metatheory.SMT
