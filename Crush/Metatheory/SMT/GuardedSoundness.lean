import Crush.Metatheory.SMT.Soundness
import Crush.Metatheory.SMT.Guarded
import Crush.Metatheory.SMT.DatatypeGuard

/-!
# Soundness of guard-aware SMT terms

The syntax layer may restrict an enlarged SMT carrier at a quantifier. This
module gives that restriction one component-independent semantic contract and
proves the complete term encoder correct once. Datatype and `Nat` guards are
instances of the contract, not separate term soundness theorems.
-/

namespace Crush.Metatheory.SMT

open Defunctionalization.Flattened

variable {symbols : FO.SymbolFamily}

/-- Semantic contract for the guard syntax emitted at one bound variable.
Omitting syntax is allowed only when every target value is guarded. -/
structure GuardedEncoding.Semantics (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop) where
  omitted : ∀ sort value (environment : List (Value target)),
    guarding.guard sort (.bvar 0) = Option.none → guard sort value
  encoded : ∀ sort value (environment : List (Value target)) condition,
    guarding.guard sort (.bvar 0) = some condition →
      Crush.SMT.Eval (modelWith guarding.encoding target extra)
        (.typed sort value :: environment) condition
      (.typed .bool (guard sort value))

/-- Compositional guard semantics for an arbitrary already-evaluated raw term.
This is the form needed by datatype guards applied to selector terms. -/
structure GuardedEncoding.TermSemantics (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop) where
  omitted : ∀ sort value, guarding.guard sort value = Option.none →
    ∀ semantic, guard sort semantic
  encoded : ∀ sort raw value (environment : List (Value target)) condition,
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment raw
      (.typed sort value) →
    guarding.guard sort raw = some condition →
      Crush.SMT.Eval (modelWith guarding.encoding target extra)
        environment condition (.typed .bool (guard sort value))

/-- Pointwise-equivalent semantic predicates satisfy the same guard syntax
contract. This is the composition boundary between individual guard components
and the complete source-to-target carrier relation. -/
theorem GuardedEncoding.TermSemantics.congr {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {left right : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra left)
    (equal : ∀ sort value, left sort value ↔ right sort value) :
    guarding.TermSemantics target extra right where
  omitted := by
    intro sort raw omitted value
    exact (equal sort value).mp (semantics.omitted sort raw omitted value)
  encoded := by
    intro sort raw value environment condition rawEval encoded
    have evaluated := semantics.encoded sort raw value environment condition
      rawEval encoded
    have propositionEq : left sort value = right sort value :=
      propext (equal sort value)
    simpa only [propositionEq] using evaluated

/-- Bound-variable guard semantics is the immediate specialization of the
compositional contract. -/
theorem GuardedEncoding.TermSemantics.toSemantics {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard) :
    guarding.Semantics target extra guard where
  omitted := fun sort value environment omitted =>
    semantics.omitted sort (.bvar 0) omitted value
  encoded := by
    intro sort value environment condition encoded
    exact semantics.encoded sort (.bvar 0) value
      (.typed sort value :: environment) condition
      (Crush.SMT.Eval.bvar rfl) encoded

/-- The ordinary encoder satisfies the guarded contract with the trivial
predicate, so it remains the zero-cost specialization of the same semantics. -/
theorem GuardedEncoding.none_semantics (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target) :
    (GuardedEncoding.none encoding).Semantics target extra (fun _ _ => True) where
  omitted := by intros; trivial
  encoded := by
    intro sort value environment condition impossible
    simp [GuardedEncoding.none] at impossible

theorem GuardedEncoding.none_termSemantics (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target) :
    (GuardedEncoding.none encoding).TermSemantics target extra (fun _ _ => True) where
  omitted := by intros; trivial
  encoded := by
    intro sort raw value environment condition evaluated impossible
    simp [GuardedEncoding.none] at impossible

/-- One typed raw term to which a compositional guard may be applied. -/
structure GuardInput (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (environment : List (Value target)) where
  sort : FO.FOSort
  raw : Crush.SMT.Term
  value : sort.Denote target.carriers
  evaluated : Crush.SMT.Eval (modelWith guarding.encoding target extra)
    environment raw (.typed sort value)

namespace GuardInput

/-- Apply one encoded unary family symbol to an already evaluated argument. -/
def ofUnary {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)} {domain result : FO.FOSort}
    (symbol : symbols { args := [domain], result := result })
    (raw : Crush.SMT.Term) (value : domain.Denote target.carriers)
    (evaluated : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment raw
      (.typed domain value)) :
    GuardInput guarding target extra environment where
  sort := result
  raw := .app (guarding.encoding.ident symbol) #[raw]
  value := target.symbol symbol value
  evaluated := by
    apply Crush.SMT.Eval.symbol (guarding.encoding.ident_fresh symbol)
    · exact Crush.SMT.EvalList.cons evaluated .nil
    · apply Or.inl
      refine ⟨{ args := [domain], result := result }, symbol, rfl, ?_⟩
      simp [applyValues]

/-- Classical truth value used only to align relational Boolean evaluation
with a semantic proposition. -/
noncomputable def truth (proposition : Prop) : Bool :=
  by
    classical
    exact if proposition then true else false

@[simp] theorem truth_eq_true (proposition : Prop) :
    truth proposition = true ↔ proposition := by
  classical
  by_cases valid : proposition <;> simp [truth, valid]

@[simp] theorem truth_eq_false (proposition : Prop) :
    truth proposition = false ↔ ¬proposition := by
  classical
  by_cases valid : proposition <;> simp [truth, valid]

/-- Retain exactly the guard conditions emitted for a typed input list. -/
def terms {guarding : GuardedEncoding symbols} {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)}
    (inputs : List (GuardInput guarding target extra environment)) :
    Array Crush.SMT.Term :=
  (inputs.filterMap fun input =>
    guarding.guard input.sort input.raw).toArray

/-- Boolean denotations aligned with `terms`. -/
noncomputable def results {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)}
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    (inputs : List (GuardInput guarding target extra environment)) : List Bool := by
  exact inputs.filterMap fun input =>
    (guarding.guard input.sort input.raw).map fun _ =>
      truth (guard input.sort input.value)

private theorem typed_decide {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target} (proposition : Prop) :
    (Value.typed .bool proposition : Value target) =
      (modelWith guarding.encoding target extra).bool (truth proposition) := by
  classical
  by_cases valid : proposition
  · simp [modelWith_bool, boolValue, truth, valid]
  · simp [modelWith_bool, boolValue, truth, valid]

/-- Pointwise compositional guard semantics produces the exact Boolean list
used by `wfBody`. -/
theorem evals {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard)
    (inputs : List (GuardInput guarding target extra environment)) :
    Datatype.BoolEvals (modelWith guarding.encoding target extra) environment
      (terms inputs) (results guard inputs) := by
  classical
  induction inputs with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons input inputs ih =>
      cases conditionEq : guarding.guard input.sort input.raw with
      | none => simpa [terms, results, conditionEq] using ih
      | some condition =>
          rcases ih with ⟨values, termsEval, booleans⟩
          let result := truth (guard input.sort input.value)
          refine ⟨(modelWith guarding.encoding target extra).bool result :: values,
            ?_, ?_⟩
          have evaluated := semantics.encoded input.sort input.raw input.value
            environment condition input.evaluated conditionEq
          rw [typed_decide (guarding := guarding) (extra := extra)
            (guard input.sort input.value)] at evaluated
          simpa [terms, results, conditionEq, result] using
            Crush.SMT.EvalList.cons evaluated termsEval
          simpa [results, conditionEq, result] using
            (Crush.SMT.BoolValues.cons booleans)

/-- Filtering omitted guards does not weaken the semantic conjunction because
the compositional contract requires every omitted guard to be total. -/
theorem results_all {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard)
    (inputs : List (GuardInput guarding target extra environment)) :
    (results guard inputs).all id = true ↔
      ∀ input ∈ inputs, guard input.sort input.value := by
  induction inputs with
  | nil => simp [results]
  | cons input inputs ih =>
      cases conditionEq : guarding.guard input.sort input.raw with
      | none =>
          have head := semantics.omitted input.sort input.raw conditionEq input.value
          have resultEq : results guard (input :: inputs) = results guard inputs := by
            simp [results, conditionEq]
          rw [resultEq, ih]
          simp [head]
      | some condition =>
          have resultEq : results guard (input :: inputs) =
              truth (guard input.sort input.value) :: results guard inputs := by
            simp [results, conditionEq]
          rw [resultEq]
          simp only [List.all_cons, Bool.and_eq_true, ih]
          simp

@[simp] theorem results_length {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)}
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    (inputs : List (GuardInput guarding target extra environment)) :
    (results guard inputs).length = (terms inputs).size := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      classical
      unfold results terms at ih
      unfold results terms
      cases conditionEq : guarding.guard input.sort input.raw <;>
        simp [conditionEq, ih]

end GuardInput

/-- Assemble one exact `wfBody` clause from a tester proposition and the
compositional guards on its selector inputs. -/
theorem Datatype.ClauseRuns.ofInputs {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard)
    {ctor : String} {valueTerm : Crush.SMT.Term} {tester : Prop}
    (testerEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment
      (.app (.indexed "is" #[.inl ctor]) #[valueTerm])
      (.typed .bool tester))
    (inputs : List (GuardInput guarding target extra environment)) :
    Datatype.ClauseRuns (modelWith guarding.encoding target extra) environment
      ctor (GuardInput.terms inputs) valueTerm
      (!GuardInput.truth tester || (GuardInput.results guard inputs).all id) := by
  let testerBool := GuardInput.truth tester
  let fieldBools := GuardInput.results guard inputs
  refine ⟨testerBool, fieldBools, ?_, GuardInput.evals semantics inputs, rfl⟩
  rw [GuardInput.typed_decide (guarding := guarding) (extra := extra) tester]
    at testerEval
  exact testerEval

/-- One constructor clause assembled from its tester and typed selector inputs. -/
structure GuardPart (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (environment : List (Value target)) (valueTerm : Crush.SMT.Term) where
  name : String
  tester : Prop
  testerEval : Crush.SMT.Eval
    (modelWith guarding.encoding target extra) environment
    (.app (.indexed "is" #[.inl name]) #[valueTerm]) (.typed .bool tester)
  fields : List (GuardInput guarding target extra environment)

namespace GuardPart

/-- Semantic tester-implies-field contract represented by a clause list. -/
def Holds {guarding : GuardedEncoding symbols} {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)} {valueTerm : Crush.SMT.Term}
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    (clauses : List (GuardPart guarding target extra environment valueTerm)) : Prop :=
  ∀ clause ∈ clauses, clause.tester →
    ∀ input ∈ clause.fields, guard input.sort input.value

def parts {guarding : GuardedEncoding symbols} {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)} {valueTerm : Crush.SMT.Term}
    (clauses : List (GuardPart guarding target extra environment valueTerm)) :
    Array (String × Array Crush.SMT.Term) :=
  (clauses.map fun clause =>
    (clause.name, GuardInput.terms clause.fields)).toArray

noncomputable def results {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)} {valueTerm : Crush.SMT.Term}
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    (clauses : List (GuardPart guarding target extra environment valueTerm)) :
    List Bool :=
  clauses.filterMap fun clause =>
    let fields := GuardInput.terms clause.fields
    if fields.isEmpty then none
    else some (!GuardInput.truth clause.tester ||
      (GuardInput.results guard clause.fields).all id)

/-- Constructor clauses produce the `PartsRun` expected by the exact body
evaluator, with the same empty-field filtering as the Crush translator. -/
theorem runs {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)} {valueTerm : Crush.SMT.Term}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard)
    (clauses : List (GuardPart guarding target extra environment valueTerm)) :
    Datatype.PartsRun (modelWith guarding.encoding target extra)
      environment valueTerm (parts clauses).toList (results guard clauses) := by
  induction clauses with
  | nil => exact .nil
  | cons clause clauses ih =>
      cases emptyEq : (GuardInput.terms clause.fields).isEmpty with
      | true =>
          have fieldsEq : GuardInput.terms clause.fields = #[] := by
            simpa using emptyEq
          simpa [parts, results, emptyEq, fieldsEq] using
            (Datatype.PartsRun.skip (ctor := clause.name) emptyEq ih)
      | false =>
          have fieldsNe : GuardInput.terms clause.fields ≠ #[] := by
            simpa using emptyEq
          let head := Datatype.ClauseRuns.ofInputs semantics clause.testerEval
            clause.fields
          simpa [parts, results, emptyEq, fieldsNe] using
            (Datatype.PartsRun.cons emptyEq head ih)

/-- The retained Boolean outcomes are true exactly when every constructor
tester implies all semantic field guards. Clauses omitted because every field
guard is total are recovered through `TermSemantics.omitted`. -/
theorem results_all {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)} {valueTerm : Crush.SMT.Term}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard)
    (clauses : List (GuardPart guarding target extra environment valueTerm)) :
    (results guard clauses).all id = true ↔
      ∀ clause ∈ clauses, clause.tester →
        ∀ input ∈ clause.fields, guard input.sort input.value := by
  induction clauses with
  | nil => simp [results]
  | cons clause clauses ih =>
      cases emptyEq : (GuardInput.terms clause.fields).isEmpty with
      | true =>
          have sizeEq : (GuardInput.terms clause.fields).size = 0 := by
            simpa using emptyEq
          have lengthEq : (GuardInput.results guard clause.fields).length = 0 := by
            rw [GuardInput.results_length, sizeEq]
          have fieldsEq : GuardInput.results guard clause.fields = [] :=
            List.length_eq_zero_iff.mp lengthEq
          have everyField : ∀ input ∈ clause.fields,
              guard input.sort input.value :=
            (GuardInput.results_all semantics clause.fields).mp (by
              simp [fieldsEq])
          have rawEq : GuardInput.terms clause.fields = #[] := by
            simpa using emptyEq
          rw [show results guard (clause :: clauses) = results guard clauses by
            simp [results, rawEq]]
          rw [ih]
          constructor
          · intro tail current member tested input inputMem
            rcases List.mem_cons.mp member with equal | member
            · subst current
              exact everyField input inputMem
            · exact tail current member tested input inputMem
          · intro all current member tested input inputMem
            exact all current (by simp [member]) tested input inputMem
      | false =>
          have rawNe : GuardInput.terms clause.fields ≠ #[] := by
            simpa using emptyEq
          rw [show results guard (clause :: clauses) =
              (!GuardInput.truth clause.tester ||
                (GuardInput.results guard clause.fields).all id) ::
                results guard clauses by
            simp [results, rawNe]]
          have fields := GuardInput.results_all semantics clause.fields
          have headIff :
              (!GuardInput.truth clause.tester ||
                  (GuardInput.results guard clause.fields).all id) = true ↔
                clause.tester → ∀ input ∈ clause.fields,
                  guard input.sort input.value := by
            by_cases tested : clause.tester
            · simp [GuardInput.truth, tested, fields]
            · simp [GuardInput.truth, tested]
          simp only [List.all_cons, id_eq, Bool.and_eq_true]
          rw [headIff, ih]
          constructor
          · intro both current member tested input inputMem
            rcases List.mem_cons.mp member with equal | member
            · subst current
              exact both.1 tested input inputMem
            · exact both.2 current member tested input inputMem
          · intro all
            constructor
            · exact all clause (by simp)
            · intro current member
              exact all current (by simp [member])

/-- The exact emitted `wfBody` evaluates to the semantic
tester-implies-field proposition. -/
theorem eval {guarding : GuardedEncoding symbols}
    {target : FO.FamilyModel symbols}
    {extra : ExtraGraph guarding.encoding target}
    {environment : List (Value target)} {valueTerm : Crush.SMT.Term}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (semantics : guarding.TermSemantics target extra guard)
    (clauses : List (GuardPart guarding target extra environment valueTerm)) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment
      (Datatype.wfBody (parts clauses) valueTerm)
      (.typed .bool (Holds guard clauses)) := by
  have evaluated := Datatype.eval_wfBody_eq (runs semantics clauses)
  have valid := results_all semantics clauses
  let outcome := (results guard clauses).all id
  have outcomeEq : outcome = GuardInput.truth (Holds guard clauses) := by
    by_cases holds : Holds guard clauses
    · have trueEq : outcome = true := valid.mpr holds
      simp [outcome, trueEq, GuardInput.truth, holds]
    · have falseEq : outcome = false := by
        cases equal : outcome
        · rfl
        · exact False.elim (holds (valid.mp equal))
      simp [outcome, falseEq, GuardInput.truth, holds]
  change Crush.SMT.Eval _ _ _
    ((modelWith guarding.encoding target extra).bool outcome) at evaluated
  rw [outcomeEq] at evaluated
  rw [← GuardInput.typed_decide (guarding := guarding) (extra := extra)
    (Holds guard clauses)] at evaluated
  exact evaluated

end GuardPart

/-- Generic graph-equation theorem for an emitted unary recursive
definition. It deliberately knows nothing about how the symbol graph or its
body were assembled; interpreted arithmetic and datatype predicates can
therefore share the same final model and the same command theorem. -/
theorem wfDef_holds_core {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    (extra : ExtraGraph encoding target)
    (functional : Crush.SMT.ApplyUnique (modelWith encoding target extra))
    {sort : FO.FOSort} {name binder : String}
    {guard : sort.Denote target.carriers → Prop}
    (hasType : Crush.SMT.SymbolHasType
      (modelWith encoding target extra) (.symb name)
      [encoding.sort sort] (encoding.sort .bool))
    (applies : ∀ value output,
      (modelWith encoding target extra).apply (.symb name)
          [.typed sort value] output ↔
        output = .typed .bool (guard value))
    (parts : Array (String × Array Crush.SMT.Term))
    (bodyEval : ∀ value : sort.Denote target.carriers,
      Crush.SMT.Eval (modelWith encoding target extra)
        [.typed sort value] (Datatype.wfBody parts)
        (.typed .bool (guard value))) :
    (Datatype.wfDef name binder (encoding.sort sort) parts).Holds
      (modelWith encoding target extra) := by
  constructor
  · simpa [Datatype.wfDef, encoding.bool_eq, Crush.SMT.boolSort] using hasType
  · intro values typed output
    cases typed with
    | cons head tail =>
        cases tail
        obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
          encoding sort _ (by simpa only [modelWith_inSort] using head)
        simpa [Datatype.wfDef] using
          (applies value output).trans
            ((bodyEval value).iff_eq functional).symm

/-- A family of fresh unary predicates selecting guarded values. This is the
shared graph shape used by recursive datatype `wf_T` symbols. Whether a sort
without such a predicate has a total guard is a property of a particular syntax
component, not of the graph: interpreted components such as integer `>=` may
guard the omitted sort instead. -/
structure UnaryGuards (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop) where
  ident : FO.FOSort → Option Crush.SMT.Ident
  ident_injective : ∀ {left right identifier},
    ident left = some identifier → ident right = some identifier →
      left = right
  notBuiltin : ∀ sort identifier, ident sort = some identifier →
    Crush.SMT.NotBuiltin identifier
  sourceFresh : ∀ sort identifier, ident sort = some identifier →
    ∀ {decl : FO.SymbolDecl} (symbol : symbols decl),
      identifier ≠ encoding.ident symbol

namespace UnaryGuards

/-- Exact guard syntax selected by a unary-guard family. -/
def guarding {encoding : Encoding symbols} {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard) : GuardedEncoding symbols where
  encoding
  guard := fun sort value => guards.ident sort |>.map fun identifier =>
    .app identifier #[value]

/-- Canonical graph of the fresh unary guard predicates. -/
noncomputable def extra {encoding : Encoding symbols} {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard) : ExtraGraph encoding target where
  apply := fun identifier values output =>
    ∃ sort value, guards.ident sort = some identifier ∧
      values = [.typed sort value] ∧
      output = .typed .bool (guard sort value)
  source_fresh := by
    intro decl symbol values output applied
    rcases applied with ⟨sort, value, identEq, valuesEq, outputEq⟩
    exact guards.sourceFresh sort _ identEq symbol rfl
  literal := literalValue encoding target
  literal_typed := literalValue_typed encoding target

/-- A pre-existing native component does not own any allocated unary guard
identifier. This is the only cross-component premise needed to combine their
graphs. -/
def Fresh {encoding : Encoding symbols} {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (base : ExtraGraph encoding target) : Prop :=
  ∀ {sort identifier}, guards.ident sort = some identifier →
    ∀ values output, ¬base.apply identifier values output

/-- Install unary predicates over an existing native component while keeping
that component's literal interpretation. -/
noncomputable def over {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (base : ExtraGraph encoding target) : ExtraGraph encoding target where
  apply := fun identifier values output =>
    base.apply identifier values output ∨ guards.extra.apply identifier values output
  source_fresh := by
    intro decl symbol values output applied
    rcases applied with baseApplied | guardApplied
    · exact base.source_fresh symbol values output baseApplied
    · exact guards.extra.source_fresh symbol values output guardApplied
  literal := base.literal
  literal_typed := base.literal_typed

/-- Adding a fresh unary family preserves global graph functionality. -/
theorem applyUnique_over {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (base : ExtraGraph encoding target)
    (baseUnique : Crush.SMT.ApplyUnique (modelWith encoding target base))
    (fresh : guards.Fresh base) :
    Crush.SMT.ApplyUnique (modelWith encoding target (guards.over base)) := by
  intro identifier values left right leftApply rightApply
  rcases leftApply with leftOrdinary | leftExtra <;>
    rcases rightApply with rightOrdinary | rightExtra
  · exact baseUnique identifier values left right
      (Or.inl leftOrdinary) (Or.inl rightOrdinary)
  · rcases rightExtra with rightBase | rightGuard
    · exact baseUnique identifier values left right
        (Or.inl leftOrdinary) (Or.inr rightBase)
    · rcases leftOrdinary with ⟨decl, symbol, identEq, outputEq⟩
      rw [identEq] at rightGuard
      exact False.elim (guards.extra.source_fresh symbol values right rightGuard)
  · rcases leftExtra with leftBase | leftGuard
    · exact baseUnique identifier values left right
        (Or.inr leftBase) (Or.inl rightOrdinary)
    · rcases rightOrdinary with ⟨decl, symbol, identEq, outputEq⟩
      rw [identEq] at leftGuard
      exact False.elim (guards.extra.source_fresh symbol values left leftGuard)
  · rcases leftExtra with leftBase | leftGuard <;>
      rcases rightExtra with rightBase | rightGuard
    · exact baseUnique identifier values left right
        (Or.inr leftBase) (Or.inr rightBase)
    · rcases rightGuard with
        ⟨sort, value, identEq, valuesEq, outputEq⟩
      exact False.elim (fresh identEq values left leftBase)
    · rcases leftGuard with
        ⟨sort, value, identEq, valuesEq, outputEq⟩
      exact False.elim (fresh identEq values right rightBase)
    · rcases leftGuard with
        ⟨leftSort, leftValue, leftIdent, leftValues, leftEq⟩
      rcases rightGuard with
        ⟨rightSort, rightValue, rightIdent, rightValues, rightEq⟩
      have sortEq : leftSort = rightSort :=
        guards.ident_injective leftIdent rightIdent
      subst rightSort
      rw [leftValues] at rightValues
      injection rightValues with typedEq
      have valueEq : leftValue = rightValue :=
        eq_of_heq (Value.typed.inj typedEq).2
      subst rightValue
      exact leftEq.trans rightEq.symm

/-- Evaluation of an allocated unary guard does not depend on how omitted sorts
are handled by other syntax components. -/
theorem encoded_over {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (base : ExtraGraph encoding target)
    {sort : FO.FOSort} {raw : Crush.SMT.Term}
    {value : sort.Denote target.carriers} {environment : List (Value target)}
    {condition : Crush.SMT.Term}
    (rawEval : Crush.SMT.Eval (modelWith encoding target (guards.over base))
      environment raw (.typed sort value))
    (guardEq : guards.guarding.guard sort raw = some condition) :
    Crush.SMT.Eval (modelWith encoding target (guards.over base)) environment
      condition (.typed .bool (guard sort value)) := by
  unfold guarding at guardEq
  cases identEq : guards.ident sort with
  | none => simp [identEq] at guardEq
  | some identifier =>
      simp only [identEq, Option.map_some] at guardEq
      cases guardEq
      apply Crush.SMT.Eval.symbol (guards.notBuiltin sort identifier identEq)
      · exact Crush.SMT.EvalList.cons rawEval .nil
      · exact Or.inr (Or.inr ⟨sort, value, identEq, rfl, rfl⟩)

/-- Unary syntax keeps its denotation when installed over another component,
provided sorts omitted by this component really have a total guard. -/
theorem termSemantics_over {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (base : ExtraGraph encoding target)
    (omitted : ∀ sort, guards.ident sort = none →
      ∀ value, guard sort value) :
    guards.guarding.TermSemantics target (guards.over base) guard where
  omitted := by
    intro sort raw guardEq value
    unfold guarding at guardEq
    cases identEq : guards.ident sort with
    | none => exact omitted sort identEq value
    | some identifier => simp [identEq] at guardEq
  encoded := by
    intro sort raw value environment condition rawEval guardEq
    exact guards.encoded_over base rawEval guardEq

/-- Every unary symbol remains typed over a fresh base component. -/
theorem hasType_over {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (base : ExtraGraph encoding target)
    (baseUnique : Crush.SMT.ApplyUnique (modelWith encoding target base))
    (fresh : guards.Fresh base)
    {sort : FO.FOSort} {identifier : Crush.SMT.Ident}
    (identEq : guards.ident sort = some identifier) :
    Crush.SMT.SymbolHasType (modelWith encoding target (guards.over base))
      identifier [encoding.sort sort] (encoding.sort .bool) := by
  intro values typed
  cases typed with
  | cons head tail =>
      cases tail
      obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
        encoding sort _ (by simpa only [modelWith_inSort] using head)
      let output : Value target := .typed .bool (guard sort value)
      refine ⟨output, Value.inSort_typed (target := target) encoding .bool
        (guard sort value), ?_, ?_⟩
      · exact Or.inr (Or.inr ⟨sort, value, identEq, rfl, rfl⟩)
      · intro other applied
        exact guards.applyUnique_over base baseUnique fresh identifier
          [.typed sort value] other output applied
          (Or.inr (Or.inr ⟨sort, value, identEq, rfl, rfl⟩))

/-- Application of an allocated unary symbol remains its exact predicate over
a fresh base component. -/
theorem applies_iff_over {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (base : ExtraGraph encoding target) (fresh : guards.Fresh base)
    {sort : FO.FOSort} {identifier : Crush.SMT.Ident}
    (identEq : guards.ident sort = some identifier)
    (value : sort.Denote target.carriers) (output : Value target) :
    (modelWith encoding target (guards.over base)).apply identifier
        [.typed sort value] output ↔
      output = .typed .bool (guard sort value) := by
  constructor
  · intro applied
    rcases applied with ordinary | native
    · rcases ordinary with ⟨decl, symbol, encoded, outputEq⟩
      exact False.elim
        (guards.sourceFresh sort identifier identEq symbol encoded)
    · rcases native with baseApplied | guardApplied
      · exact False.elim (fresh identEq _ _ baseApplied)
      · rcases guardApplied with
          ⟨otherSort, otherValue, otherIdent, valuesEq, outputEq⟩
        have sortEq : otherSort = sort :=
          guards.ident_injective otherIdent identEq
        subst otherSort
        cases valuesEq
        exact outputEq
  · intro outputEq
    subst output
    exact Or.inr (Or.inr ⟨sort, value, identEq, rfl, rfl⟩)

/-- The combined ordinary/guard graph is globally single-valued. Freshness
separates the two graph components, while identifier injectivity separates
distinct guard sorts. -/
theorem applyUnique {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard) :
    Crush.SMT.ApplyUnique (modelWith encoding target guards.extra) := by
  intro identifier values left right leftApply rightApply
  rcases leftApply with leftOrdinary | leftGuard <;>
    rcases rightApply with rightOrdinary | rightGuard
  · rcases leftOrdinary with
      ⟨leftDecl, leftSymbol, leftIdent, leftEq⟩
    rcases rightOrdinary with
      ⟨rightDecl, rightSymbol, rightIdent, rightEq⟩
    have identEq : encoding.ident leftSymbol = encoding.ident rightSymbol :=
      leftIdent.symm.trans rightIdent
    have declEq := encoding.ident_decl_injective leftSymbol rightSymbol identEq
    subst rightDecl
    have symbolEq := encoding.ident_injective leftSymbol rightSymbol identEq
    subst rightSymbol
    exact leftEq.trans rightEq.symm
  · rcases leftOrdinary with ⟨decl, symbol, identEq, outputEq⟩
    rw [identEq] at rightGuard
    exact False.elim (guards.extra.source_fresh symbol values right rightGuard)
  · rcases rightOrdinary with ⟨decl, symbol, identEq, outputEq⟩
    rw [identEq] at leftGuard
    exact False.elim (guards.extra.source_fresh symbol values left leftGuard)
  · rcases leftGuard with
      ⟨leftSort, leftValue, leftIdent, leftValues, leftEq⟩
    rcases rightGuard with
      ⟨rightSort, rightValue, rightIdent, rightValues, rightEq⟩
    have sortEq : leftSort = rightSort :=
      guards.ident_injective leftIdent rightIdent
    subst rightSort
    rw [leftValues] at rightValues
    injection rightValues with typedEq
    have valueEq : leftValue = rightValue :=
      eq_of_heq (Value.typed.inj typedEq).2
    subst rightValue
    exact leftEq.trans rightEq.symm

/-- Fresh unary guard syntax composes with every typed raw term evaluation when
the unary component is responsible for every nontrivial guard. -/
theorem termSemantics {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (omitted : ∀ sort, guards.ident sort = none →
      ∀ value, guard sort value) :
    guards.guarding.TermSemantics target guards.extra guard where
  omitted := by
    intro sort raw guardEq value
    unfold guarding at guardEq
    cases identEq : guards.ident sort with
    | none => exact omitted sort identEq value
    | some identifier => simp [identEq] at guardEq
  encoded := by
    intro sort raw value environment condition rawEval guardEq
    unfold guarding at guardEq
    cases identEq : guards.ident sort with
    | none => simp [identEq] at guardEq
    | some identifier =>
        simp only [identEq, Option.map_some] at guardEq
        cases guardEq
        apply Crush.SMT.Eval.symbol (guards.notBuiltin sort identifier identEq)
        · exact Crush.SMT.EvalList.cons rawEval .nil
        · exact Or.inr ⟨sort, value, identEq, rfl, rfl⟩

/-- Fresh unary predicate syntax denotes exactly its associated semantic
guard in the canonical extension graph. -/
theorem semantics {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    (omitted : ∀ sort, guards.ident sort = none →
      ∀ value, guard sort value) :
    guards.guarding.Semantics target guards.extra guard :=
  (guards.termSemantics omitted).toSemantics

/-- Every allocated unary guard is a total, functional Boolean symbol in the
extended graph. Identifier injectivity is what prevents two sort guards from
assigning different outputs to one raw symbol. -/
theorem hasType {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    {sort : FO.FOSort} {identifier : Crush.SMT.Ident}
    (identEq : guards.ident sort = some identifier) :
    Crush.SMT.SymbolHasType (modelWith encoding target guards.extra)
      identifier [encoding.sort sort] (encoding.sort .bool) := by
  intro values typed
  cases typed with
  | cons head tail =>
      cases tail
      obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
        encoding sort _ (by simpa only [modelWith_inSort] using head)
      let output : Value target := .typed .bool (guard sort value)
      refine ⟨output, ?_, ?_, ?_⟩
      · dsimp only [output]
        exact Value.inSort_typed (target := target) encoding .bool
          (guard sort value)
      · exact Or.inr ⟨sort, value, identEq, rfl, rfl⟩
      · intro other applied
        rcases applied with ordinary | native
        · rcases ordinary with ⟨decl, symbol, encoded, otherEq⟩
          exact False.elim
            (guards.sourceFresh sort identifier identEq symbol encoded)
        · rcases native with
            ⟨otherSort, otherValue, otherIdent, valuesEq, otherEq⟩
          have sortEq : otherSort = sort :=
            guards.ident_injective otherIdent identEq
          subst otherSort
          cases valuesEq
          exact otherEq

/-- Application of an allocated guard identifier is exactly its semantic
predicate graph. -/
theorem applies_iff {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    {sort : FO.FOSort} {identifier : Crush.SMT.Ident}
    (identEq : guards.ident sort = some identifier)
    (value : sort.Denote target.carriers) (output : Value target) :
    (modelWith encoding target guards.extra).apply identifier
        [.typed sort value] output ↔
      output = .typed .bool (guard sort value) := by
  constructor
  · intro applied
    rcases applied with ordinary | native
    · rcases ordinary with ⟨decl, symbol, encoded, outputEq⟩
      exact False.elim
        (guards.sourceFresh sort identifier identEq symbol encoded)
    · rcases native with
        ⟨otherSort, otherValue, otherIdent, valuesEq, outputEq⟩
      have sortEq : otherSort = sort :=
        guards.ident_injective otherIdent identEq
      subst otherSort
      cases valuesEq
      exact outputEq
  · intro outputEq
    subst output
    exact Or.inr ⟨sort, value, identEq, rfl, rfl⟩

/-- Generic graph-equation theorem for the exact unary recursive-definition
syntax shared with the Crush translator. A component only has to identify the denotation
of its `wfBody`; allocation, typing, and graph functionality are discharged
once here. -/
theorem wfDef_holds {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols}
    {guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop}
    (guards : UnaryGuards encoding target guard)
    {sort : FO.FOSort} {name binder : String}
    (identEq : guards.ident sort = some (.symb name))
    (parts : Array (String × Array Crush.SMT.Term))
    (bodyEval : ∀ value : sort.Denote target.carriers,
      Crush.SMT.Eval (modelWith encoding target guards.extra)
        [.typed sort value] (Datatype.wfBody parts)
        (.typed .bool (guard sort value))) :
    (Datatype.wfDef name binder (encoding.sort sort) parts).Holds
      (modelWith encoding target guards.extra) := by
  exact wfDef_holds_core guards.extra guards.applyUnique
    (guards.hasType identEq) (guards.applies_iff identEq) parts bodyEval

end UnaryGuards

/-- Semantic argument values in the same order as guarded SMT argument terms. -/
def guardArgValues (target : FO.FamilyModel symbols)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    {context : FO.Context} (valuation : FO.FamilyValuation target context) :
    {sorts : List FO.FOSort} → FO.FamilyArgs symbols context sorts →
      List (Value target)
  | [], .nil => []
  | _ :: _, .cons (sort := sort) argument rest =>
      .typed sort (argument.guardDenote target guard valuation) ::
        guardArgValues target guard valuation rest

/-- Decoding guarded argument values recovers guarded curried application. -/
theorem applyValues_guardArgValues (target : FO.FamilyModel symbols)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    {context : FO.Context} (valuation : FO.FamilyValuation target context)
    {sorts : List FO.FOSort} (args : FO.FamilyArgs symbols context sorts)
    {result : FO.FOSort}
    (function : FO.SymbolDenote target.carriers sorts result) :
    applyValues target sorts function
        (guardArgValues target guard valuation args) =
      args.guardApply target guard valuation function := by
  exact FO.FamilyArgs.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun context sorts args =>
      ∀ (valuation : FO.FamilyValuation target context) {result : FO.FOSort}
        (function : FO.SymbolDenote target.carriers sorts result),
        applyValues target sorts function
            (guardArgValues target guard valuation args) =
          args.guardApply target guard valuation function)
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
    (nil := by intros; rfl)
    (cons := fun argument rest argumentIH restIH => by
      intro valuation result function
      simp only [guardArgValues, applyValues, decode_typed,
        FO.FamilyArgs.guardApply.eq_2]
      exact restIH valuation _)
    args valuation function

private theorem asTrue (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    {environment : List (Value target)} {term : STerm} {proposition : Prop}
    (evaluated : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment term
      (.typed .bool proposition)) (valid : proposition) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment term
      ((modelWith guarding.encoding target extra).bool true) := by
  have equal : proposition = True := propext ⟨fun _ => trivial, fun _ => valid⟩
  simpa only [modelWith_bool, boolValue, equal] using evaluated

private theorem asFalse (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    {environment : List (Value target)} {term : STerm} {proposition : Prop}
    (evaluated : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment term
      (.typed .bool proposition)) (invalid : ¬proposition) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment term
      ((modelWith guarding.encoding target extra).bool false) := by
  have equal : proposition = False := propext ⟨invalid, False.elim⟩
  simpa only [modelWith_bool, boolValue, equal] using evaluated

private theorem boolNe (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target) :
    (modelWith guarding.encoding target extra).bool true ≠
      (modelWith guarding.encoding target extra).bool false := by
  exact fun equal => Bool.noConfusion
    ((modelWith guarding.encoding target extra).boolInjective equal)

private theorem evalNot (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    {environment : List (Value target)} {term : STerm} {body : Prop}
    (evaluated : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment term
      (.typed .bool body)) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment
      (smt| (not $term)) (.typed .bool (¬body)) := by
  by_cases valid : body
  · have result := Crush.SMT.Eval.not
      (asTrue guarding target extra evaluated valid)
    simpa [modelWith_bool, boolValue, valid] using result
  · have result := Crush.SMT.Eval.not
      (asFalse guarding target extra evaluated valid)
    simpa [modelWith_bool, boolValue, valid] using result

private theorem evalAnd (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    {environment : List (Value target)} {left right : STerm}
    {leftValue rightValue : Prop}
    (leftEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment left
      (.typed .bool leftValue))
    (rightEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment right
      (.typed .bool rightValue)) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment
      (smt| (and $left $right)) (.typed .bool (leftValue ∧ rightValue)) := by
  by_cases leftValid : leftValue <;> by_cases rightValid : rightValue
  all_goals
    first
    | have result := Crush.SMT.Eval.and
        (Crush.SMT.EvalList.cons
          (asTrue guarding target extra leftEval leftValid)
          (Crush.SMT.EvalList.cons
            (asTrue guarding target extra rightEval rightValid) .nil))
        (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))
    | have result := Crush.SMT.Eval.and
        (Crush.SMT.EvalList.cons
          (asTrue guarding target extra leftEval leftValid)
          (Crush.SMT.EvalList.cons
            (asFalse guarding target extra rightEval rightValid) .nil))
        (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))
    | have result := Crush.SMT.Eval.and
        (Crush.SMT.EvalList.cons
          (asFalse guarding target extra leftEval leftValid)
          (Crush.SMT.EvalList.cons
            (asTrue guarding target extra rightEval rightValid) .nil))
        (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))
    | have result := Crush.SMT.Eval.and
        (Crush.SMT.EvalList.cons
          (asFalse guarding target extra leftEval leftValid)
          (Crush.SMT.EvalList.cons
            (asFalse guarding target extra rightEval rightValid) .nil))
        (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))
  all_goals simpa [modelWith_bool, boolValue, leftValid, rightValid] using result

private theorem evalOr (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    {environment : List (Value target)} {left right : STerm}
    {leftValue rightValue : Prop}
    (leftEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment left
      (.typed .bool leftValue))
    (rightEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment right
      (.typed .bool rightValue)) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment
      (smt| (or $left $right)) (.typed .bool (leftValue ∨ rightValue)) := by
  by_cases leftValid : leftValue <;> by_cases rightValid : rightValue
  all_goals
    first
    | have result := Crush.SMT.Eval.or
        (Crush.SMT.EvalList.cons
          (asTrue guarding target extra leftEval leftValid)
          (Crush.SMT.EvalList.cons
            (asTrue guarding target extra rightEval rightValid) .nil))
        (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))
    | have result := Crush.SMT.Eval.or
        (Crush.SMT.EvalList.cons
          (asTrue guarding target extra leftEval leftValid)
          (Crush.SMT.EvalList.cons
            (asFalse guarding target extra rightEval rightValid) .nil))
        (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))
    | have result := Crush.SMT.Eval.or
        (Crush.SMT.EvalList.cons
          (asFalse guarding target extra leftEval leftValid)
          (Crush.SMT.EvalList.cons
            (asTrue guarding target extra rightEval rightValid) .nil))
        (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))
    | have result := Crush.SMT.Eval.or
        (Crush.SMT.EvalList.cons
          (asFalse guarding target extra leftEval leftValid)
          (Crush.SMT.EvalList.cons
            (asFalse guarding target extra rightEval rightValid) .nil))
        (Crush.SMT.BoolValues.cons (Crush.SMT.BoolValues.cons .nil))
  all_goals simpa [modelWith_bool, boolValue, leftValid, rightValid] using result

private theorem evalImp (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    {environment : List (Value target)} {left right : STerm}
    {leftValue rightValue : Prop}
    (leftEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment left
      (.typed .bool leftValue))
    (rightEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment right
      (.typed .bool rightValue)) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment
      (smt| (=> $left $right)) (.typed .bool (leftValue → rightValue)) := by
  by_cases leftValid : leftValue <;> by_cases rightValid : rightValue
  all_goals
    first
    | have result := Crush.SMT.Eval.imp
        (asTrue guarding target extra leftEval leftValid)
        (asTrue guarding target extra rightEval rightValid)
    | have result := Crush.SMT.Eval.imp
        (asTrue guarding target extra leftEval leftValid)
        (asFalse guarding target extra rightEval rightValid)
    | have result := Crush.SMT.Eval.imp
        (asFalse guarding target extra leftEval leftValid)
        (asTrue guarding target extra rightEval rightValid)
    | have result := Crush.SMT.Eval.imp
        (asFalse guarding target extra leftEval leftValid)
        (asFalse guarding target extra rightEval rightValid)
  all_goals simpa [modelWith_bool, boolValue, leftValid, rightValid] using result

private theorem evalIff (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    {environment : List (Value target)} {left right : STerm}
    {leftValue rightValue : Prop}
    (leftEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment left
      (.typed .bool leftValue))
    (rightEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra) environment right
      (.typed .bool rightValue)) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment
      (smt| (= $left $right)) (.typed .bool (leftValue ↔ rightValue)) := by
  by_cases leftValid : leftValue <;> by_cases rightValid : rightValue
  · have result := Crush.SMT.Eval.eqTrue
      (asTrue guarding target extra leftEval leftValid)
      (asTrue guarding target extra rightEval rightValid) rfl
    simpa [modelWith_bool, boolValue, leftValid, rightValid] using result
  · have result := Crush.SMT.Eval.eqFalse
      (asTrue guarding target extra leftEval leftValid)
      (asFalse guarding target extra rightEval rightValid)
      (boolNe guarding target extra)
    simpa [modelWith_bool, boolValue, leftValid, rightValid] using result
  · have result := Crush.SMT.Eval.eqFalse
      (asFalse guarding target extra leftEval leftValid)
      (asTrue guarding target extra rightEval rightValid)
      (boolNe guarding target extra).symm
    simpa [modelWith_bool, boolValue, leftValid, rightValid] using result
  · have result := Crush.SMT.Eval.eqTrue
      (asFalse guarding target extra leftEval leftValid)
      (asFalse guarding target extra rightEval rightValid) rfl
    simpa [modelWith_bool, boolValue, leftValid, rightValid] using result

private theorem guardImpEval (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    (semantics : guarding.Semantics target extra guard)
    {sort : FO.FOSort} (value : sort.Denote target.carriers)
    (environment : List (Value target)) (body : STerm) {proposition : Prop}
    (bodyEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra)
      (.typed sort value :: environment) body (.typed .bool proposition)) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra)
      (.typed sort value :: environment)
      (match guarding.guard sort (.bvar 0) with
        | none => body
        | some condition => (smt| (=> $condition $body)))
      (.typed .bool (guard sort value → proposition)) := by
  generalize guardEq : guarding.guard sort (.bvar 0) = condition
  cases condition with
  | none =>
      have guarded := semantics.omitted sort value environment guardEq
      have equal : (guard sort value → proposition) = proposition :=
        propext ⟨fun implication => implication guarded, fun valid _ => valid⟩
      simpa only [guardEq, equal] using bodyEval
  | some condition =>
      exact evalImp guarding target extra
        (semantics.encoded sort value environment condition guardEq) bodyEval

private theorem guardAndEval (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    (semantics : guarding.Semantics target extra guard)
    {sort : FO.FOSort} (value : sort.Denote target.carriers)
    (environment : List (Value target)) (body : STerm) {proposition : Prop}
    (bodyEval : Crush.SMT.Eval
      (modelWith guarding.encoding target extra)
      (.typed sort value :: environment) body (.typed .bool proposition)) :
    Crush.SMT.Eval (modelWith guarding.encoding target extra)
      (.typed sort value :: environment)
      (match guarding.guard sort (.bvar 0) with
        | none => body
        | some condition => (smt| (and $condition $body)))
      (.typed .bool (guard sort value ∧ proposition)) := by
  generalize guardEq : guarding.guard sort (.bvar 0) = condition
  cases condition with
  | none =>
      have guarded := semantics.omitted sort value environment guardEq
      have equal : (guard sort value ∧ proposition) = proposition :=
        propext ⟨And.right, fun valid => ⟨guarded, valid⟩⟩
      simpa only [guardEq, equal] using bodyEval
  | some condition =>
      exact evalAnd guarding target extra
        (semantics.encoded sort value environment condition guardEq) bodyEval

private def GuardTermValid (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) : Prop :=
  ∀ (valuation : FO.FamilyValuation target context)
    (environment : List (Value target)), Env target valuation environment →
    Crush.SMT.Eval (modelWith guarding.encoding target extra) environment
      (guarding.term source)
      (.typed sort (source.guardDenote target guard valuation))

private def GuardArgsValid (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    {context : FO.Context} {sorts : List FO.FOSort}
    (source : FO.FamilyArgs symbols context sorts) : Prop :=
  ∀ (valuation : FO.FamilyValuation target context)
    (environment : List (Value target)), Env target valuation environment →
    Crush.SMT.EvalList (modelWith guarding.encoding target extra) environment
      (guarding.arguments source).toList
      (guardArgValues target guard valuation source)

/-- The exact guarded SMT term evaluates to its guard-restricted typed FO
denotation in the shared extended model. -/
theorem guardTerm_eval (guarding : GuardedEncoding symbols)
    (target : FO.FamilyModel symbols)
    (extra : ExtraGraph guarding.encoding target)
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop)
    (semantics : guarding.Semantics target extra guard)
    {context : FO.Context} {sort : FO.FOSort}
    (source : FO.FamilyTerm symbols context sort) :
    GuardTermValid guarding target extra guard source := by
  classical
  exact FO.FamilyTerm.rec
    (motive_1 := fun _ _ source =>
      GuardTermValid guarding target extra guard source)
    (motive_2 := fun _ _ args =>
      GuardArgsValid guarding target extra guard args)
    (var := fun ref valuation environment related => by
      simpa only [GuardedEncoding.term, encodeTerm,
        FO.FamilyTerm.guardDenote.eq_1] using
        Crush.SMT.Eval.bvar (related.lookup target ref))
    (symbol := fun symbol args argsIH valuation environment related => by
      apply Crush.SMT.Eval.symbol (guarding.encoding.ident_fresh symbol)
        (argsIH valuation environment related)
      apply Or.inl
      refine ⟨_, symbol, rfl, ?_⟩
      rw [applyValues_guardArgValues]
      rfl)
    (boolLit := fun value valuation environment related => by
      cases value <;> simpa only [GuardedEncoding.term, encodeTerm,
        FO.FamilyTerm.guardDenote.eq_3, FO.FamilyTerm.guardDenote.eq_4,
        modelWith_bool, boolValue] using
          (Crush.SMT.Eval.boolLit
            (model := modelWith guarding.encoding target extra)
            (environment := environment) _))
    (not := fun body bodyIH valuation environment related =>
      evalNot guarding target extra (bodyIH valuation environment related))
    (and := fun left right leftIH rightIH valuation environment related =>
      evalAnd guarding target extra
        (leftIH valuation environment related)
        (rightIH valuation environment related))
    (or := fun left right leftIH rightIH valuation environment related =>
      evalOr guarding target extra
        (leftIH valuation environment related)
        (rightIH valuation environment related))
    (imp := fun left right leftIH rightIH valuation environment related =>
      evalImp guarding target extra
        (leftIH valuation environment related)
        (rightIH valuation environment related))
    (iff := fun left right leftIH rightIH valuation environment related =>
      evalIff guarding target extra
        (leftIH valuation environment related)
        (rightIH valuation environment related))
    (eq := fun left right leftIH rightIH valuation environment related => by
      let leftEval := leftIH valuation environment related
      let rightEval := rightIH valuation environment related
      by_cases equal : left.guardDenote target guard valuation =
          right.guardDenote target guard valuation
      · have result := Crush.SMT.Eval.eqTrue leftEval rightEval
          (congrArg (Value.typed _) equal)
        simpa [GuardedEncoding.term, FO.FamilyTerm.guardDenote.eq_10,
          modelWith_bool, boolValue, equal] using result
      · have unequal :
          Value.typed _ (left.guardDenote target guard valuation) ≠
            Value.typed _ (right.guardDenote target guard valuation) := by
          intro equality
          exact equal (Value.typed.inj equality |>.2 |> eq_of_heq)
        have result := Crush.SMT.Eval.eqFalse leftEval rightEval unequal
        simpa [GuardedEncoding.term, FO.FamilyTerm.guardDenote.eq_10,
          modelWith_bool, boolValue, equal] using result)
    (forallE := fun body bodyIH valuation environment related => by
      let proposition := ∀ value,
        guard _ value → body.guardDenote target guard (valuation.extend value)
      change Crush.SMT.Eval (modelWith guarding.encoding target extra)
        environment (guarding.term (.forallE body)) (.typed .bool proposition)
      by_cases valid : proposition
      · have result := Crush.SMT.Eval.forallTrue
          (model := modelWith guarding.encoding target extra)
          (binders := #[("x", guarding.encoding.sort _)])
          (body := match guarding.guard _ (.bvar 0) with
            | none => guarding.term body
            | some condition => (smt| (=> $condition $(guarding.term body))))
          (by
            intro values typed
            cases typed with
            | cons headTyped tailTyped =>
              cases tailTyped
              obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
                guarding.encoding _ _ headTyped
              exact asTrue guarding target extra
                (guardImpEval guarding target extra guard semantics value
                  environment (guarding.term body)
                  (bodyIH (valuation.extend value) _
                    (Env.cons target related value)))
                (valid value))
        have equal : proposition = True :=
          propext ⟨fun _ => trivial, fun _ => valid⟩
        rw [equal]
        exact result
      · obtain ⟨value, invalid⟩ := Classical.not_forall.mp valid
        have result := Crush.SMT.Eval.forallFalse
          (model := modelWith guarding.encoding target extra)
          (environment := environment)
          (binders := #[("x", guarding.encoding.sort _)])
          (body := match guarding.guard _ (.bvar 0) with
            | none => guarding.term body
            | some condition => (smt| (=> $condition $(guarding.term body))))
          (values := [.typed _ value])
          (Crush.SMT.ValuesTyped.cons
            (Value.inSort_typed (target := target) guarding.encoding _ value) .nil)
          (asFalse guarding target extra
            (guardImpEval guarding target extra guard semantics value
              environment (guarding.term body)
              (bodyIH (valuation.extend value) _
                (Env.cons target related value))) invalid)
        have equal : proposition = False :=
          propext ⟨valid, False.elim⟩
        rw [equal]
        exact result)
    (existsE := fun body bodyIH valuation environment related => by
      let proposition := ∃ value,
        guard _ value ∧ body.guardDenote target guard (valuation.extend value)
      change Crush.SMT.Eval (modelWith guarding.encoding target extra)
        environment (guarding.term (.existsE body)) (.typed .bool proposition)
      by_cases valid : proposition
      · have existsValid := valid
        obtain ⟨value, guarded, bodyValid⟩ := valid
        have result := Crush.SMT.Eval.existsTrue
          (model := modelWith guarding.encoding target extra)
          (environment := environment)
          (binders := #[("x", guarding.encoding.sort _)])
          (body := match guarding.guard _ (.bvar 0) with
            | none => guarding.term body
            | some condition => (smt| (and $condition $(guarding.term body))))
          (values := [.typed _ value])
          (Crush.SMT.ValuesTyped.cons
            (Value.inSort_typed (target := target) guarding.encoding _ value) .nil)
          (asTrue guarding target extra
            (guardAndEval guarding target extra guard semantics value
              environment (guarding.term body)
              (bodyIH (valuation.extend value) _
                (Env.cons target related value))) ⟨guarded, bodyValid⟩)
        have equal : proposition = True :=
          propext ⟨fun _ => trivial, fun _ => existsValid⟩
        rw [equal]
        exact result
      · have invalidAt : ∀ value,
            ¬(guard _ value ∧
              body.guardDenote target guard (valuation.extend value)) := by
          exact not_exists.mp valid
        have result := Crush.SMT.Eval.existsFalse
          (model := modelWith guarding.encoding target extra)
          (binders := #[("x", guarding.encoding.sort _)])
          (body := match guarding.guard _ (.bvar 0) with
            | none => guarding.term body
            | some condition => (smt| (and $condition $(guarding.term body))))
          (by
            intro values typed
            cases typed with
            | cons headTyped tailTyped =>
              cases tailTyped
              obtain ⟨value, rfl⟩ := Value.exists_typed_of_inSort
                guarding.encoding _ _ headTyped
              exact asFalse guarding target extra
                (guardAndEval guarding target extra guard semantics value
                  environment (guarding.term body)
                  (bodyIH (valuation.extend value) _
                    (Env.cons target related value))) (invalidAt value))
        have equal : proposition = False :=
          propext ⟨valid, False.elim⟩
        rw [equal]
        exact result)
    (nil := fun {_} valuation environment related => Crush.SMT.EvalList.nil)
    (cons := fun argument rest argumentIH restIH valuation environment related => by
      rw [GuardedEncoding.arguments, encodeArguments, Array.toList_append,
        List.singleton_append, guardArgValues]
      exact Crush.SMT.EvalList.cons
        (argumentIH valuation environment related)
        (restIH valuation environment related))
    source

/-- Combining model-relative FO preservation with raw guarded evaluation: a
source term evaluates to its encoded denotation in any symbol-related target
model. This is the uniform entry point for ordinary and native components. -/
theorem guardTerm_rel_eval (guarding : GuardedEncoding symbols)
    (source target : FO.FamilyModel symbols)
    (relation : FO.CarrierRel source.carriers target.carriers)
    (models : FO.ModelRel source target relation)
    (extra : ExtraGraph guarding.encoding target)
    (semantics : guarding.Semantics target extra
      (fun sort => (relation sort).guard))
    {context : FO.Context} {sort : FO.FOSort}
    (term : FO.FamilyTerm symbols context sort)
    (valuation : FO.FamilyValuation source context)
    (environment : List (Value target))
    (related : Env target
      (valuation.lift relation) environment) :
    Crush.SMT.Eval
      (modelWith guarding.encoding target extra)
      environment (guarding.term term)
      (.typed sort ((relation sort).encode (term.denote source valuation))) := by
  rw [← term.guardDenote_rel source target relation models valuation]
  exact guardTerm_eval guarding target extra _ semantics
    term (valuation.lift relation) environment related

/-- Generic symbol lifting is the ordinary specialization of the same raw
guarded theorem. -/
theorem guardTerm_lift_eval (guarding : GuardedEncoding symbols)
    (source : FO.FamilyModel symbols) (target : FO.Carriers)
    (relation : FO.CarrierRel source.carriers target)
    (extra : ExtraGraph guarding.encoding (source.lift target relation))
    (semantics : guarding.Semantics (source.lift target relation) extra
      (fun sort => (relation sort).guard))
    {context : FO.Context} {sort : FO.FOSort}
    (term : FO.FamilyTerm symbols context sort)
    (valuation : FO.FamilyValuation source context)
    (environment : List (Value (source.lift target relation)))
    (related : Env (source.lift target relation)
      (valuation.lift relation) environment) :
    Crush.SMT.Eval
      (modelWith guarding.encoding (source.lift target relation) extra)
      environment (guarding.term term)
      (.typed sort ((relation sort).encode (term.denote source valuation))) :=
  guardTerm_rel_eval guarding source (source.lift target relation) relation
    (source.lift_rel target relation) extra semantics term valuation
    environment related

/-! ## Whole guarded theories -/

/-- Every guarded assertion reflects a valid formula in the related source
model. Quantifier guards are discharged by the same carrier relation used for
symbol arguments and results. -/
theorem guardedAssertions_valid (guarding : GuardedEncoding symbols)
    (source target : FO.FamilyModel symbols)
    (relation : FO.CarrierRel source.carriers target.carriers)
    (models : FO.ModelRel source target relation)
    (extra : ExtraGraph guarding.encoding target)
    (semantics : guarding.Semantics target extra
      (fun sort => (relation sort).guard))
    (theory : FO.FamilyTheory symbols) (valid : source.SatisfiesTheory theory) :
    (modelWith guarding.encoding target extra).SatisfiesCommands
      (guarding.assertions theory) := by
  intro command membership
  have arrayMembership : command ∈ guarding.assertions theory :=
    Array.mem_toList_iff.mp membership
  have listMembership : command ∈
      theory.map fun formula =>
        Crush.SMT.Command.assert (guarding.term formula) := by
    simpa [GuardedEncoding.assertions] using arrayMembership
  rcases List.mem_map.mp listMembership with ⟨formula, formulaMem, rfl⟩
  have emptyRel : Env target
      (FO.FamilyValuation.lift relation
        (FO.Valuation.empty source.carriers)) [] := by
    intro sort ref
    nomatch ref
  have evaluated := guardTerm_rel_eval guarding source target relation models
    extra semantics formula (FO.Valuation.empty source.carriers) [] emptyRel
  have formulaValid :
      formula.denote source (FO.Valuation.empty source.carriers) :=
    valid formula formulaMem
  have truthEq :
      formula.denote source (FO.Valuation.empty source.carriers) = True :=
    propext ⟨fun _ => trivial, fun _ => formulaValid⟩
  simp only [FO.CarrierRel.get, Guarded.SubsetRepresentation.refl, id_eq] at evaluated
  rw [truthEq] at evaluated
  change Crush.SMT.Eval (modelWith guarding.encoding target extra) []
    (guarding.term formula) (.typed .bool True)
  exact evaluated

/-- Native datatype commands, exact certified derived definitions, ordinary
declarations, and guarded assertions all hold in the one explicitly induced
SMT model. Keeping the witness visible lets later layers attach additional
properties, such as standard integer semantics, without reconstructing this
proof. -/
theorem guarded_valid (guarding : GuardedEncoding symbols)
    {derived : Array Command} {theory : FO.FamilyTheory symbols}
    {commands : Array Command}
    (represented : GuardedTheoryRepresentation guarding derived theory commands)
    (source target : FO.FamilyModel symbols)
    (relation : FO.CarrierRel source.carriers target.carriers)
    (models : FO.ModelRel source target relation)
    (valid : source.SatisfiesTheory theory)
    (extra : ExtraGraph guarding.encoding target)
    (semantics : guarding.Semantics target extra
      (fun sort => (relation sort).guard))
    (nativeValid : (modelWith guarding.encoding target extra).SatisfiesCommands
      guarding.encoding.nativeCommands)
    (derivedValid : (modelWith guarding.encoding target extra).SatisfiesCommands
      derived) :
    (modelWith guarding.encoding target extra).SatisfiesCommands commands := by
  rcases represented with ⟨declarations, same⟩
  apply ((modelWith guarding.encoding target extra).satisfiesCommands_congr same).2
  simp only [GuardedEncoding.theory]
  rw [Crush.SMT.Model.satisfiesCommands_append,
    Crush.SMT.Model.satisfiesCommands_append]
  refine ⟨nativeValid, derivedValid, ?_⟩
  simp only [GuardedEncoding.theoryBody]
  rw [Crush.SMT.Model.satisfiesCommands_append,
    Crush.SMT.Model.satisfiesCommands_append]
  exact ⟨⟨sortDeclarations_valid_with guarding.encoding target extra _,
    declarations_valid_with guarding.encoding target extra declarations⟩,
    guardedAssertions_valid guarding source target relation models extra
      semantics theory valid⟩

/-- Existential packaging of `guarded_valid` for callers that need only a
countermodel and not its concrete construction. -/
theorem guarded_lift (guarding : GuardedEncoding symbols)
    {derived : Array Command} {theory : FO.FamilyTheory symbols}
    {commands : Array Command}
    (represented : GuardedTheoryRepresentation guarding derived theory commands)
    (source target : FO.FamilyModel symbols)
    (relation : FO.CarrierRel source.carriers target.carriers)
    (models : FO.ModelRel source target relation)
    (valid : source.SatisfiesTheory theory)
    (extra : ExtraGraph guarding.encoding target)
    (semantics : guarding.Semantics target extra
      (fun sort => (relation sort).guard))
    (nativeValid : (modelWith guarding.encoding target extra).SatisfiesCommands
      guarding.encoding.nativeCommands)
    (derivedValid : (modelWith guarding.encoding target extra).SatisfiesCommands
      derived) :
    ∃ smtModel : Crush.SMT.Model, smtModel.SatisfiesCommands commands :=
  ⟨modelWith guarding.encoding target extra,
    guarded_valid guarding represented source target relation models valid extra
      semantics nativeValid derivedValid⟩

end Crush.Metatheory.SMT
