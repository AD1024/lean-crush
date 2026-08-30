import Crush.Metatheory.SMT.Datatype
import Crush.Metatheory.SMT.Semantics

/-!
# Semantics of production-shaped datatype guards

The syntax builder lives in `SMT.Datatype`; this module proves how those exact
raw terms evaluate. The final production certificate supplies the
component-specific evidence that each selector guard evaluates to the typed
`FieldDecl.WF` proposition.
-/

namespace Crush.Metatheory.SMT.Datatype

open scoped Crush.SMT

/-- Raw terms evaluated pointwise to Boolean values in source order. Keeping
both existing relational judgments avoids introducing a second evaluator. -/
def BoolEvals (model : Crush.SMT.Model)
    (environment : List model.Value) (terms : Array Crush.SMT.Term)
    (booleans : List Bool) : Prop :=
  ∃ values : List model.Value,
    Crush.SMT.EvalList model environment terms.toList values ∧
    Crush.SMT.BoolValues model values booleans

private theorem evalList_true (model : Crush.SMT.Model)
    (environment : List model.Value) (terms : List Crush.SMT.Term)
    (valid : ∀ term ∈ terms,
      Crush.SMT.Eval model environment term (model.bool true)) :
    Crush.SMT.EvalList model environment terms
      (terms.map fun _ => model.bool true) := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih =>
      exact .cons (valid term (by simp))
        (ih fun candidate member => valid candidate (by simp [member]))

private theorem boolValues_true (model : Crush.SMT.Model)
    (terms : List Crush.SMT.Term) :
    Crush.SMT.BoolValues model (terms.map fun _ => model.bool true)
      (terms.map fun _ => true) := by
  induction terms with
  | nil => exact .nil
  | cons _ _ ih => exact .cons ih

/-- A list of terms all known to hold has the corresponding all-`true`
pointwise Boolean evaluation. -/
theorem boolEvals_true (model : Crush.SMT.Model)
    (environment : List model.Value) (terms : Array Crush.SMT.Term)
    (valid : ∀ term ∈ terms.toList,
      Crush.SMT.Eval model environment term (model.bool true)) :
    BoolEvals model environment terms (terms.toList.map fun _ => true) := by
  exact ⟨_, evalList_true model environment terms.toList valid,
    boolValues_true model terms.toList⟩

/-- `andAll` evaluates to the conjunction of the Boolean values of its exact
input array, including its empty and singleton compact forms. -/
theorem eval_andAll {model : Crush.SMT.Model}
    {environment : List model.Value} {terms : Array Crush.SMT.Term}
    {booleans : List Bool} (evaluated : BoolEvals model environment terms booleans) :
    Crush.SMT.Eval model environment (andAll terms)
      (model.bool (booleans.all id)) := by
  obtain ⟨items⟩ := terms
  rcases evaluated with ⟨values, termsEval, boolValues⟩
  cases items with
  | nil =>
      cases termsEval
      cases boolValues
      exact Crush.SMT.Eval.boolLit true
  | cons first rest =>
      cases rest with
      | nil =>
          cases termsEval with
          | cons firstEval restEval =>
              cases restEval
              cases boolValues with
              | cons tail =>
                  cases tail
                  simpa [andAll] using firstEval
      | cons second rest =>
          simpa [andAll] using Crush.SMT.Eval.and termsEval boolValues

/-- Semantic evidence for one production tester/selector clause. Selector
guards must have Boolean denotations even on a nonmatching constructor because
SMT evaluation is strict; only a matching tester requires their conjunction to
be true. -/
def ClauseEvals (model : Crush.SMT.Model)
    (environment : List model.Value) (ctor : String)
    (fields : Array Crush.SMT.Term) (value : Crush.SMT.Term) : Prop :=
  ∃ tester fieldValues,
    Crush.SMT.Eval model environment
      (.app (.indexed "is" #[.inl ctor]) #[value]) (model.bool tester) ∧
    BoolEvals model environment fields fieldValues ∧
    (tester = true → fieldValues.all id = true)

/-- Exact Boolean result of one tester/selector clause. Unlike `ClauseEvals`,
this relation also describes values outside the guarded image, which is needed
to prove the graph equation of the emitted recursive definition. -/
def ClauseRuns (model : Crush.SMT.Model)
    (environment : List model.Value) (ctor : String)
    (fields : Array Crush.SMT.Term) (value : Crush.SMT.Term)
    (result : Bool) : Prop :=
  ∃ tester fieldValues,
    Crush.SMT.Eval model environment
      (.app (.indexed "is" #[.inl ctor]) #[value]) (model.bool tester) ∧
    BoolEvals model environment fields fieldValues ∧
    result = (!tester || fieldValues.all id)

/-- Clause evidence restricted to a well-formed value has Boolean result
`true`. -/
theorem ClauseEvals.runs {model : Crush.SMT.Model}
    {environment : List model.Value} {ctor : String}
    {fields : Array Crush.SMT.Term} {value : Crush.SMT.Term}
    (evaluated : ClauseEvals model environment ctor fields value) :
    ClauseRuns model environment ctor fields value true := by
  rcases evaluated with
    ⟨tester, fieldValues, testerEval, fieldsEval, guarded⟩
  refine ⟨tester, fieldValues, testerEval, fieldsEval, ?_⟩
  cases tester <;> simp_all

/-- Evaluation of a retained clause returns its exact tester-implies-fields
Boolean value. -/
theorem eval_wfClause_eq {model : Crush.SMT.Model}
    {environment : List model.Value} {ctor : String}
    {fields : Array Crush.SMT.Term} {value : Crush.SMT.Term} {result : Bool}
    (nonempty : fields.isEmpty = false)
    (evaluated : ClauseRuns model environment ctor fields value result) :
    Crush.SMT.Eval model environment
      (Option.get (wfClause? ctor fields value) (by simp [wfClause?, nonempty]))
      (model.bool result) := by
  rcases evaluated with
    ⟨tester, fieldValues, testerEval, fieldsEvaluated, resultEq⟩
  have fieldsEval := eval_andAll fieldsEvaluated
  rw [resultEq]
  simpa [wfClause?, nonempty] using Crush.SMT.Eval.imp testerEval fieldsEval

/-- Pointwise evaluation of the clauses retained by `wfBody`. The Boolean list
has exactly the same filtering and order as the syntax builder. -/
inductive PartsRun (model : Crush.SMT.Model)
    (environment : List model.Value) (value : Crush.SMT.Term) :
    List (String × Array Crush.SMT.Term) → List Bool → Prop where
  | nil : PartsRun model environment value [] []
  | skip {ctor fields rest results}
      (empty : fields.isEmpty = true)
      (tail : PartsRun model environment value rest results) :
      PartsRun model environment value ((ctor, fields) :: rest) results
  | cons {ctor fields rest result results}
      (nonempty : fields.isEmpty = false)
      (head : ClauseRuns model environment ctor fields value result)
      (tail : PartsRun model environment value rest results) :
      PartsRun model environment value ((ctor, fields) :: rest)
        (result :: results)

/-- `PartsRun` is the semantic counterpart of the exact `filterMap` performed
by the production syntax builder. -/
theorem PartsRun.evals {model : Crush.SMT.Model}
    {environment : List model.Value} {value : Crush.SMT.Term}
    {parts : List (String × Array Crush.SMT.Term)} {results : List Bool}
    (runs : PartsRun model environment value parts results) :
    BoolEvals model environment
      (parts.toArray.filterMap fun part => wfClause? part.1 part.2 value)
      results := by
  induction runs with
  | nil => exact ⟨[], .nil, .nil⟩
  | @skip ctor fields rest results empty tail ih =>
      have fieldsEq : fields = #[] := by simpa using empty
      subst fields
      simpa [Array.toList_filterMap, wfClause?] using ih
  | @cons ctor fields rest result results nonempty head tail ih =>
      rcases ih with ⟨tailValues, tailEval, tailBools⟩
      refine ⟨model.bool result :: tailValues, ?_, .cons tailBools⟩
      have fieldsNe : fields ≠ #[] := by simpa using nonempty
      have headEval : Crush.SMT.Eval model environment
          (smt| (=> $((.app (.indexed "is" #[.inl ctor]) #[value] :
            Crush.SMT.Term)) $(andAll fields))) (model.bool result) := by
        simpa [wfClause?, nonempty] using eval_wfClause_eq nonempty head
      simpa [Array.toList_filterMap, wfClause?, nonempty, fieldsNe] using
        Crush.SMT.EvalList.cons headEval tailEval

/-- The exact production body evaluates to the conjunction recorded by
`PartsRun`, including values outside the guarded image. -/
theorem eval_wfBody_eq {model : Crush.SMT.Model}
    {environment : List model.Value}
    {parts : Array (String × Array Crush.SMT.Term)}
    {value : Crush.SMT.Term} {results : List Bool}
    (runs : PartsRun model environment value parts.toList results) :
    Crush.SMT.Eval model environment (wfBody parts value)
      (model.bool (results.all id)) := by
  exact eval_andAll (by
    simpa [wfBody] using runs.evals)

/-- One nonempty production clause evaluates to true under precisely its typed
tester-implies-selector-guards obligation. -/
theorem eval_wfClause {model : Crush.SMT.Model}
    {environment : List model.Value} {ctor : String}
    {fields : Array Crush.SMT.Term} {value : Crush.SMT.Term}
    (nonempty : fields.isEmpty = false)
    (evaluated : ClauseEvals model environment ctor fields value) :
    Crush.SMT.Eval model environment
      (Option.get (wfClause? ctor fields value) (by simp [wfClause?, nonempty]))
      (model.bool true) := by
  exact eval_wfClause_eq nonempty evaluated.runs

/-- The exact body shared with production evaluates to true when every retained
constructor clause has the tester/selector evidence described above. -/
theorem eval_wfBody {model : Crush.SMT.Model}
    {environment : List model.Value}
    {parts : Array (String × Array Crush.SMT.Term)}
    {value : Crush.SMT.Term}
    (valid : ∀ ctor fields, (ctor, fields) ∈ parts.toList →
      fields.isEmpty = false →
      ClauseEvals model environment ctor fields value) :
    Crush.SMT.Eval model environment (wfBody parts value) (model.bool true) := by
  let clauses := parts.filterMap fun part => wfClause? part.1 part.2 value
  have every : ∀ clause ∈ clauses.toList,
      Crush.SMT.Eval model environment clause (model.bool true) := by
    intro clause member
    simp only [clauses, Array.toList_filterMap] at member
    rcases List.mem_filterMap.mp member with ⟨part, partMem, equal⟩
    by_cases empty : part.2.isEmpty = true
    · simp [wfClause?, empty] at equal
    · have nonempty : part.2.isEmpty = false := by
        cases equalEmpty : part.2.isEmpty <;> simp_all
      have evaluated := eval_wfClause nonempty
        (valid part.1 part.2 partMem nonempty)
      simp [wfClause?, nonempty] at equal evaluated
      simpa [equal] using evaluated
  have evaluated := eval_andAll
    (boolEvals_true model environment clauses every)
  have allTrue : (clauses.toList.map fun _ => true).all id = true := by simp
  rw [allTrue] at evaluated
  change Crush.SMT.Eval model environment (andAll clauses) (model.bool true)
  exact evaluated

end Crush.Metatheory.SMT.Datatype
