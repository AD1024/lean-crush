import Crush.Metatheory.SMT.Representation

/-!
# Semantic soundness of FO-to-SMT representation

Every model of an intrinsically typed FO theory induces a model of its concrete
SMT representation.  Values from the FO model are tagged by their intrinsic
sort.  Raw values are used only for SMT sorts outside the representation image,
which preserves the standard nonemptiness requirement without confusing two
represented carriers.
-/

namespace Crush.Metatheory.SMT

open scoped Crush.Metatheory
open scoped Crush.SMT

variable {symbols : FO.SymbolFamily}

/-- Values in the induced untyped SMT universe. -/
inductive Value (target : FO.FamilyModel symbols) where
  | typed (sort : FO.FOSort) (value : sort.Denote target.carriers)
  | raw (sort : SSort)

/-- A canonical inhabitant of every intrinsic FO carrier. -/
noncomputable def defaultValue (carriers : FO.Carriers) :
    (sort : FO.FOSort) → sort.Denote carriers
  | .bool => True
  | .base sort => Classical.choice (carriers.baseNonempty sort)
  | .fn domain codomain => Classical.choice (carriers.fnNonempty domain codomain)

namespace Value

/-- Sort membership for the induced SMT universe.  A raw value can inhabit only
a sort outside the image of the typed encoding. -/
def InSort (encoding : Encoding symbols) {target : FO.FamilyModel symbols}
    (smtSort : SSort) : Value target → Prop
  | .typed sort _ => encoding.sort sort = smtSort
  | .raw rawSort => rawSort = smtSort ∧
      ∀ sort, encoding.sort sort ≠ rawSort

@[simp] theorem inSort_typed (encoding : Encoding symbols)
    {target : FO.FamilyModel symbols} (sort : FO.FOSort)
    (value : sort.Denote target.carriers) :
    InSort encoding (encoding.sort sort) (.typed sort value) := rfl

/-- Membership in a represented sort exposes a uniquely typed FO value. -/
theorem exists_typed_of_inSort (encoding : Encoding symbols)
    {target : FO.FamilyModel symbols} (sort : FO.FOSort)
    (value : Value target) (typed : InSort encoding (encoding.sort sort) value) :
    ∃ sourceValue, value = .typed sort sourceValue := by
  cases value with
  | typed other value =>
      simp only [InSort] at typed
      have equal := encoding.sort_injective typed
      subst other
      exact ⟨value, rfl⟩
  | raw rawSort =>
      simp only [InSort] at typed
      exact False.elim (typed.2 sort (typed.1.symm))

end Value

/-- Boolean embedding used by the induced SMT model. -/
def boolValue (target : FO.FamilyModel symbols) : Bool → Value target
  | false => .typed .bool False
  | true => .typed .bool True

/-- Decode an induced SMT value at an expected intrinsic sort.  Semantic term
evaluation reaches only the matching `typed` branch; the default cases make
symbol graphs total over every well-sorted SMT argument. -/
noncomputable def decode (target : FO.FamilyModel symbols)
    (sort : FO.FOSort) : Value target → sort.Denote target.carriers
  | .typed other value =>
      if equal : other = sort then equal ▸ value
      else defaultValue target.carriers sort
  | .raw _ => defaultValue target.carriers sort

@[simp] theorem decode_typed (target : FO.FamilyModel symbols)
    (sort : FO.FOSort) (value : sort.Denote target.carriers) :
    decode target sort (.typed sort value) = value := by
  simp [decode]

/-- Apply a curried typed symbol interpretation to an untyped value list. -/
noncomputable def applyValues (target : FO.FamilyModel symbols) :
    (sorts : List FO.FOSort) → {result : FO.FOSort} →
      FO.SymbolDenote target.carriers sorts result →
      List (Value target) → result.Denote target.carriers
  | [], _, function, _ => function
  | sort :: sorts, result, function, [] =>
      applyValues target sorts (result := result)
        (function (defaultValue target.carriers sort)) []
  | sort :: sorts, result, function, value :: values =>
      applyValues target sorts (result := result)
        (function (decode target sort value)) values

/-- Graph assigned to encoded user symbols in the induced SMT model. -/
def Applies (encoding : Encoding symbols) (target : FO.FamilyModel symbols)
    (identifier : Crush.SMT.Ident) (values : List (Value target))
    (output : Value target) : Prop :=
  ∃ (decl : FO.SymbolDecl) (symbol : symbols decl),
    identifier = .symb (encoding.name symbol) ∧
    output = .typed decl.result
      (applyValues target decl.args (target.symbol symbol) values)

/-- Interpretation of a non-Boolean literal at its concrete SMT sort. -/
noncomputable def otherLiteralValue (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (literal : Crush.SMT.Literal) : Value target := by
  classical
  exact if represented : ∃ sort, encoding.sort sort = literal.sort then
    let sort := Classical.choose represented
    .typed sort (defaultValue target.carriers sort)
  else
    .raw literal.sort

/-- Interpretation of literals.  If a non-Boolean literal's concrete sort is
already represented, choose that carrier's canonical inhabitant; otherwise
retain a raw value at the fresh SMT sort. -/
noncomputable def literalValue (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) : Crush.SMT.Literal → Value target
  | .bool value => boolValue target value
  | literal@(.str _) => otherLiteralValue encoding target literal
  | literal@(.num _) => otherLiteralValue encoding target literal
  | literal@(.bitvec _ _) => otherLiteralValue encoding target literal

/-- Concrete SMT model induced by an intrinsic FO family model. -/
noncomputable def model (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) : Crush.SMT.Model where
  Value := Value target
  inSort := Value.InSort encoding
  sortNonempty := fun smtSort => by
    classical
    by_cases represented : ∃ sort, encoding.sort sort = smtSort
    · let sort := Classical.choose represented
      have equality := Classical.choose_spec represented
      exact ⟨Value.typed sort (defaultValue target.carriers sort), equality⟩
    · exact ⟨Value.raw smtSort, rfl, by
        intro sort equality
        exact represented ⟨sort, equality⟩⟩
  bool := boolValue target
  boolTyped := fun value => by
    cases value <;> simpa [boolValue, Value.InSort] using encoding.bool_eq
  boolInjective := by
    intro left right equality
    cases left <;> cases right
    · rfl
    · have impossible : False = True := eq_of_heq (Value.typed.inj equality |>.2)
      exact False.elim (Eq.mpr impossible trivial)
    · have impossible : True = False := eq_of_heq (Value.typed.inj equality |>.2)
      exact False.elim (Eq.mp impossible trivial)
    · rfl
  literal := literalValue encoding target
  literalTyped := by
    intro literal
    cases literal with
    | bool value =>
        cases value <;> simpa [literalValue, Crush.SMT.Literal.sort, boolValue,
          Value.InSort] using encoding.bool_eq
    | str value | num value | bitvec width value =>
        classical
        rw [literalValue, otherLiteralValue]
        split
        next represented =>
          simp only [Value.InSort]
          exact Classical.choose_spec represented
        next notRepresented =>
          simp only [Value.InSort]
          constructor
          · trivial
          · intro sort equality
            exact notRepresented ⟨sort, equality⟩
  apply := Applies encoding target

/-- Each symbol declaration emitted by the pure encoder is satisfied by the
induced model. -/
theorem declaration_valid (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (declared : Declaration symbols) :
    (model encoding target).SatisfiesCommand (declaration encoding declared) := by
  rw [declaration]
  constructor
  · trivial
  · intro values valuesTyped
    let output := Value.typed declared.declaration.result
      (applyValues target declared.declaration.args
        (target.symbol declared.symbol) values)
    refine ⟨output, ?_, ?_, ?_⟩
    · dsimp only [output]
      exact Value.inSort_typed (target := target) encoding
        declared.declaration.result
        (applyValues target declared.declaration.args
          (target.symbol declared.symbol) values)
    · exact ⟨declared.declaration, declared.symbol, rfl, rfl⟩
    · intro other otherApplies
      rcases otherApplies with ⟨otherDecl, otherSymbol, nameEqual, outputEqual⟩
      have names : encoding.name declared.symbol = encoding.name otherSymbol := by
        simpa using congrArg id nameEqual
      have declEqual := encoding.name_decl_injective declared.symbol otherSymbol names
      subst otherDecl
      have symbolEqual := encoding.name_injective declared.symbol otherSymbol names
      subst otherSymbol
      exact outputEqual

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
      (.symbApp "and" #[left, right])
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
      (.symbApp "or" #[left, right])
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
      simpa only [term, FO.FamilyTerm.denote.eq_1] using
        Crush.SMT.Eval.bvar (related.lookup target ref))
    (symbol := fun symbol args argsIH => by
      intro valuation environment related
      have result : Crush.SMT.Eval (model encoding target) environment
          (.app (.symb (encoding.name symbol)) (arguments encoding args))
          (.typed _ (args.apply target valuation (target.symbol symbol))) := by
        apply Crush.SMT.Eval.symbol (encoding.name_fresh symbol)
          (argsIH valuation environment related)
        refine ⟨_, symbol, rfl, ?_⟩
        rw [applyValues_argumentValues]
      simpa only [term, FO.FamilyTerm.denote.eq_2] using result)
    (boolLit := fun value => by
      intro valuation environment related
      cases value <;> simpa only [term, FO.FamilyTerm.denote.eq_3,
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
      rw [arguments, Array.toList_append, List.singleton_append, argumentValues]
      change Crush.SMT.EvalList (model encoding target) environment
        (term encoding argument :: (arguments encoding rest).toList)
        (Value.typed _ ⟦argument⟧[target, valuation] ::
          argumentValues target valuation rest)
      exact Crush.SMT.EvalList.cons
        (argumentIH valuation environment related)
        (restIH valuation environment related))
    source

/-- Syntactically represented terms have the denotation established by
`term_eval`. -/
theorem term_representation_sound (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) (encoded : STerm)
    (representation : TermRepresentation encoding source encoded)
    (valuation : FO.FamilyValuation target context)
    (environment : List (Value target)) (related : Env target valuation environment) :
    Crush.SMT.Eval (model encoding target) environment encoded
      (.typed sort ⟦source⟧[target, valuation]) := by
  subst encoded
  exact term_eval encoding target source valuation environment related

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
  constructor
  · trivial
  · exact eval_true encoding target
      (term_eval encoding target formula
        (FO.Valuation.empty target.carriers) [] (Env.empty target))
      (valid formula formulaMem)

/-- Every emitted symbol declaration is valid in the induced relational
symbol graph. -/
theorem declarations_valid (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (declarations : List (Declaration symbols)) :
    model encoding target ⊨ₛᶜ
      (declarations.map (declaration encoding)).toArray := by
  intro command membership
  have arrayMembership : command ∈
      (declarations.map (declaration encoding)).toArray :=
    Array.mem_toList_iff.mp membership
  have listMembership : command ∈
      declarations.map (declaration encoding) := by
    simpa using arrayMembership
  rcases List.mem_map.mp listMembership with ⟨declared, declaredMem, rfl⟩
  exact declaration_valid encoding target declared

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

/-- Semantic soundness of the pure FO-to-SMT representation: any typed target
model lifts to a model of the exact represented command sequence. -/
theorem representation_sound (encoding : Encoding symbols)
    {source : FO.FamilyTheory symbols} {commands : Array Command}
    (representation : TheoryRepresentation encoding source commands)
    (target : FO.FamilyModel symbols) (valid : target ⊨ᵀ source) :
    ∃ smtModel : Crush.SMT.Model, smtModel ⊨ₛᶜ commands := by
  rcases representation with ⟨declarations, rfl⟩
  refine ⟨model encoding target, ?_⟩
  simp only [theory]
  rw [Crush.SMT.Model.satisfiesCommands_append,
    Crush.SMT.Model.satisfiesCommands_append]
  exact ⟨⟨sortDeclarations_valid encoding target _,
    declarations_valid encoding target declarations⟩,
    assertions_valid encoding target source valid⟩

/-- Concrete command unsatisfiability reflects to the represented typed FO
theory. -/
theorem commands_unsat_implies_theory_unsat (encoding : Encoding symbols)
    {source : FO.FamilyTheory symbols} {commands : Array Command}
    (representation : TheoryRepresentation encoding source commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    FO.FamilyTheoryUnsatisfiable source := by
  intro target valid
  obtain ⟨smtModel, commandsValid⟩ :=
    representation_sound encoding representation target valid
  exact unsat smtModel commandsValid


end Crush.Metatheory.SMT
