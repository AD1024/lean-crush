import Crush

/-!
Tests for proof-producing ground term instantiation.

The constants are deliberately uninterpreted: this exercises the general forward
chain rather than arithmetic, lists, or any Cashmere-specific encoding.
-/

open Lean Meta
open Crush

set_option crush.trust "reconstruct"

namespace GroundInstantiation

axiom R : Int → Int → Prop
axiom P : Int → Prop
axiom Q : Int → Prop
axiom next : Int → Int

axiom step : ∀ x, R x (next x)
axiom lift : ∀ x y, R x y → P y
axiom project : ∀ x y, R x y → Q y
axiom grow : ∀ x, P x → P (next x)
axiom Accepts : (Int → Bool) → Int → Prop
axiom functionLift : ∀ f x, Accepts f x → P x

axiom NonEmptyList : List Nat → Prop
axiom ListMarker : List Nat → Prop
axiom Guard : Int → Prop
axiom HiddenResult : Int → Prop
axiom tailLength :
  ∀ xs : List Nat, NonEmptyList xs → xs.tail.length < xs.length
axiom listSumWitness (x : Int) :
  x < (([Int.toNat (x + 1)] : List Nat).sum : Int)
axiom reflexive (x : Int) : x = x
axiom nestedGuarded :
  Guard 0 → ∀ x, Guard x → ∀ y, Guard y → R x y

def listCode : List Nat → Nat
  | [] => 0
  | _ :: _ => 1

axiom listCodeOne :
  ∀ xs : List Nat, NonEmptyList xs → listCode xs = 1

private def reportQuery (x : Int) : Prop :=
  ∃ y, R x y ∧ P y

private def anyRelation : Prop :=
  ∃ x y, R x y

-- Pin the preprocessing result independently of solver trigger heuristics.
run_meta do
  let stepProof ← mkConstWithFreshMVarLevels ``step
  let liftProof ← mkConstWithFreshMVarLevels ``lift
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let query ← mkAppM ``reportQuery #[x]
    let facts : Array Fact := #[
      {
        prop := ← inferType stepProof
        proof := some stepProof
        descr := "step"
        instantiateTerms := true
      },
      {
        prop := ← inferType liftProof
        proof := some liftProof
        descr := "lift"
        instantiateTerms := true
      },
      {
        prop := mkNot query
        proof := none
        descr := "negated query"
        negated := true
      }
    ]
    let report ← instantiateGroundFacts
      ({ instFuel := 16, instRounds := 3 } : Crush.Config) facts
    unless report.generated == 2 && !report.exhausted do
      throwError "expected two ground instances and a fixpoint, got \
        {report.generated} instance(s) (exhausted: {report.exhausted})"

-- Data binders after proposition premises are specialized without assuming the
-- premises. The generated proof retains them as implications:
-- `fun h0 hx hy => nestedGuarded h0 x hx y hy`.
run_meta do
  let nestedProof ← mkConstWithFreshMVarLevels ``nestedGuarded
  withLocalDeclD `x (mkConst ``Int) fun x => do
    withLocalDeclD `y (mkConst ``Int) fun y => do
      let relation ← mkAppM ``R #[x, y]
      let report ← instantiateGroundFacts
        ({ instFuel := 8, instRounds := 2 } : Crush.Config) #[
          {
            prop := ← inferType nestedProof
            proof := some nestedProof
            descr := "nestedGuarded"
            instantiateTerms := true
          },
          {
            prop := mkNot relation
            proof := none
            descr := "negated query"
            negated := true
          }
        ]
      unless report.generated == 1 && !report.exhausted do
        throwError "expected one nested guarded instance, got \
          {report.generated} instance(s) (exhausted: {report.exhausted})"
      let some generated := report.facts.find? (·.descr == "nestedGuarded@ground")
        | throwError "missing nested guarded ground instance"
      let some proof := generated.proof
        | throwError "nested guarded ground instance has no proof"
      check proof
      unless ← isDefEq (← inferType proof) generated.prop do
        throwError "nested guarded instance proof does not prove its proposition"

-- Swept hypotheses enter eager instantiation only when the caller explicitly
-- opts in, as the `crush [*]` frontend does.
run_meta do
  let nestedProof ← mkConstWithFreshMVarLevels ``nestedGuarded
  let nestedTy ← inferType nestedProof
  withLocalDeclD `h nestedTy fun h => do
    let target ← mkAppM ``R #[mkIntLit 1, mkIntLit 2]
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    let eager ← collectFactsWithRewrite goal.mvarId! {
      allHyps := true
      instantiateHyps := true
    }
    unless eager.facts.any fun fact =>
        fact.proof == some h && fact.instantiateTerms do
      throwError "explicitly swept local hypothesis was not marked for instantiation"
    let lazy ← collectFactsWithRewrite goal.mvarId! { allHyps := true }
    if lazy.facts.any fun fact =>
        fact.proof == some h && fact.instantiateTerms then
      throwError "bare local-hypothesis sweep unexpectedly enabled instantiation"

-- A nontrivially simplified instance is used in the ground-first query, while
-- the complete fallback retains the quantified template.
run_meta do
  let tailProof ← mkConstWithFreshMVarLevels ``tailLength
  let empty : Expr :=
    mkApp (mkConst ``List.nil [.zero]) (mkConst ``Nat)
  let marker ← mkAppM ``ListMarker #[empty]
  let expected := mkNot (← mkAppM ``NonEmptyList #[empty])
  let facts : Array Fact := #[
    {
      prop := ← inferType tailProof
      proof := some tailProof
      descr := "tailLength"
      instantiateTerms := true
    },
    {
      prop := mkNot marker
      proof := none
      descr := "negated query"
      negated := true
    }
  ]
  let report ← instantiateGroundFacts
    ({ instFuel := 8, instRounds := 2 } : Crush.Config) facts
  unless report.generated == 1 && !report.exhausted do
    throwError "expected one simplified ground instance, got \
      {report.generated} instance(s) (exhausted: {report.exhausted})"
  unless report.facts.any (fun fact => fact.descr == "tailLength") do
    throwError "complete fallback lost the quantified template"
  unless report.facts.any (fun fact =>
      fact.descr == "tailLength@ground" && fact.prop == expected) do
    throwError "expected the simplified consequence `¬ NonEmptyList []`"
  let some groundFacts := report.groundFacts
    | throwError "expected a ground-first query"
  if groundFacts.any (fun fact => fact.descr == "tailLength") then
    throwError "ground-first query retained the instantiated template"

-- The complete fallback retains its quantified parent even when generated
-- instances simplify differently.
run_meta do
  let codeProof ← mkConstWithFreshMVarLevels ``listCodeOne
  let listNat : Expr :=
    mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
  let empty : Expr :=
    mkApp (mkConst ``List.nil [.zero]) (mkConst ``Nat)
  withLocalDeclD `xs listNat fun xs => do
    let emptyMarker ← mkAppM ``ListMarker #[empty]
    let variableMarker ← mkAppM ``ListMarker #[xs]
    let query ← mkAppM ``And #[emptyMarker, variableMarker]
    let report ← instantiateGroundFacts
      ({ instFuel := 8, instRounds := 2 } : Crush.Config) #[
        {
          prop := ← inferType codeProof
          proof := some codeProof
          descr := "listCodeOne"
          instantiateTerms := true
        },
        {
          prop := mkNot query
          proof := none
          descr := "negated query"
          negated := true
        }
      ]
    unless report.generated == 2 &&
        report.facts.any (fun fact => fact.descr == "listCodeOne") do
      throwError "unchanged mixed instance did not retain the quantified fallback; \
        generated {report.generated}, facts: {report.facts.map (·.descr)}"
    if report.groundFacts.isNone then
      throwError "retained quantified parent did not produce a ground-first query"

-- A template with no ground evidence remains quantified so the solver can still
-- instantiate it directly.
run_meta do
  let tailProof ← mkConstWithFreshMVarLevels ``tailLength
  let original := ← inferType tailProof
  let report ← instantiateGroundFacts
    ({ instFuel := 8, instRounds := 2 } : Crush.Config) #[{
      prop := original
      proof := some tailProof
      descr := "tailLength"
      instantiateTerms := true
    }]
  unless report.generated == 0 && !report.exhausted &&
      report.facts.any (fun fact =>
        fact.descr == "tailLength" && fact.prop == original) do
    throwError "unmatched quantified template was not retained"

-- Fuel exhaustion disables the ground-first query: generated instances may be
-- incomplete, so the solver receives the complete quantified fallback.
run_meta do
  let tailProof ← mkConstWithFreshMVarLevels ``tailLength
  let listNat : Expr :=
    mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
  let empty : Expr :=
    mkApp (mkConst ``List.nil [.zero]) (mkConst ``Nat)
  withLocalDeclD `xs listNat fun xs => do
    let emptyMarker ← mkAppM ``ListMarker #[empty]
    let variableMarker ← mkAppM ``ListMarker #[xs]
    let query ← mkAppM ``And #[emptyMarker, variableMarker]
    let report ← instantiateGroundFacts
      ({ instFuel := 1, instRounds := 2 } : Crush.Config) #[
        {
          prop := ← inferType tailProof
          proof := some tailProof
          descr := "tailLength"
          instantiateTerms := true
        },
        {
          prop := mkNot query
          proof := none
          descr := "negated query"
          negated := true
        }
      ]
    unless report.exhausted &&
        report.facts.any (fun fact => fact.descr == "tailLength") do
      throwError "fuel exhaustion removed a truncated template's quantified fallback"
    if report.groundFacts.isSome then
      throwError "fuel exhaustion offered an incomplete ground-first query"

-- Simplifying this instance would erase the constructed list that can witness an
-- existential. Keep both the unsimplified instance and its quantified fallback.
run_meta do
  let witnessProof ← mkConstWithFreshMVarLevels ``listSumWitness
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let query ← mkAppM ``P #[x]
    let report ← instantiateGroundFacts
      ({ instFuel := 8, instRounds := 2 } : Crush.Config) #[
        {
          prop := ← inferType witnessProof
          proof := some witnessProof
          descr := "listSumWitness"
          instantiateTerms := true
        },
        {
          prop := mkNot query
          proof := none
          descr := "negated query"
          negated := true
        }
      ]
    unless report.generated == 1 && !report.exhausted do
      throwError "expected one constructor-bearing ground instance, got \
        {report.generated} instance(s) (exhausted: {report.exhausted})"
    unless report.facts.any (fun fact => fact.descr == "listSumWitness") do
      throwError "constructor-erasing simplification removed the quantified fallback"
    unless report.facts.any (fun fact =>
        fact.descr == "listSumWitness@ground" &&
          fact.prop.getUsedConstants.contains ``List.cons) do
      throwError "generated instance lost its constructor-shaped witness"

-- Simplification to `True` must not replace either the useful ground equality or
-- its quantified parent.
run_meta do
  let reflexiveProof ← mkConstWithFreshMVarLevels ``reflexive
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let query ← mkAppM ``P #[x]
    let report ← instantiateGroundFacts
      ({ instFuel := 8, instRounds := 2 } : Crush.Config) #[
        {
          prop := ← inferType reflexiveProof
          proof := some reflexiveProof
          descr := "reflexive"
          instantiateTerms := true
        },
        {
          prop := mkNot query
          proof := none
          descr := "negated query"
          negated := true
        }
      ]
    unless report.generated == 1 &&
        report.facts.any (fun fact => fact.descr == "reflexive") &&
        report.facts.any (fun fact =>
          fact.descr == "reflexive@ground" && !fact.prop.isConstOf ``True) do
      throwError "tautological simplification discarded a useful quantified fact"

-- A named ground hypothesis is not a template, but its terms must still seed a
-- genuinely quantified hint. This also prevents ground selected premises from
-- entering every template-matching round.
run_meta do
  let stepProof ← mkConstWithFreshMVarLevels ``step
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let px ← mkAppM ``P #[x]
    withLocalDeclD `h px fun h => do
      let query ← mkAppM ``anyRelation #[]
      let facts : Array Fact := #[
        {
          prop := px
          proof := some h
          descr := "ground hint"
          instantiateTerms := true
        },
        {
          prop := ← inferType stepProof
          proof := some stepProof
          descr := "step"
          instantiateTerms := true
        },
        {
          prop := mkNot query
          proof := none
          descr := "negated query"
          negated := true
        }
      ]
      let report ← instantiateGroundFacts
        ({ instFuel := 8, instRounds := 2 } : Crush.Config) facts
      unless report.generated == 1 && !report.exhausted do
        throwError "expected the ground hint to seed one instance, got \
          {report.generated} instance(s) (exhausted: {report.exhausted})"

-- Rigid-head indexing must ignore large unrelated occurrence classes before
-- invoking symbolic matching on the one relevant relation occurrence.
run_meta do
  let liftProof ← mkConstWithFreshMVarLevels ``lift
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let nextX ← mkAppM ``next #[x]
    let relation ← mkAppM ``R #[x, nextX]
    let mut facts : Array Fact := #[{
      prop := ← inferType liftProof
      proof := some liftProof
      descr := "lift"
      instantiateTerms := true
    }, {
      prop := relation
      proof := none
      descr := "relevant occurrence"
    }]
    for i in [0:256] do
      facts := facts.push {
        prop := ← mkEq (mkIntLit i) (mkIntLit i)
        proof := none
        descr := "irrelevant equality"
      }
    facts := facts.push {
      prop := mkNot (← mkAppM ``P #[nextX])
      proof := none
      descr := "negated query"
      negated := true
    }
    let report ← instantiateGroundFacts
      ({ instFuel := 8, instRounds := 2 } : Crush.Config) facts
    unless report.generated == 1 && !report.exhausted do
      throwError "expected one indexed relation instance, got \
        {report.generated} instance(s) (exhausted: {report.exhausted})"

-- `step x` creates the term that determines both binders of `lift`. SMT
-- E-matching cannot invent that term from the existential goal by itself.
theorem forward_chain_builds_witness (x : Int) :
    ∃ y, R x y ∧ P y := by
  crush [step, lift]

-- Trigger evidence may occur inside a compound proposition, just as it may in
-- an SMT assertion. The matcher must not be limited to whole facts.
theorem nested_atom_triggers (x y : Int) (h : R x y ∧ P x) : Q y := by
  crush [project, *]

-- Function-valued binders are instantiated only from exact pattern evidence;
-- they never enter fallback candidate enumeration.
theorem function_binder_pattern (x : Int)
    (h : Accepts (fun _ => true) x) : P x := by
  crush [functionLift, *]

-- The quantified rule's witness is absent from its conclusion, so direct backward
-- application cannot infer it. Ground matching anchors the witness at `hidden`; the
-- solver selects that checked instance and reconstruction replays it from the core.
set_option crush.trust "reconstruct" in
theorem hidden_rule_parameter (oldValue : Int → Int) (hidden updated target : Int)
    (rule : ∀ witness, oldValue witness = 1 → HiddenResult target)
    (updatedRead : (if hidden = updated then 0 else oldValue hidden) = 1)
    (hne : hidden ≠ updated) :
    HiddenResult target := by
  crush [*]

/-- info: 'GroundInstantiation.hidden_rule_parameter' depends on axioms: [propext, Classical.choice, HiddenResult, Quot.sound] -/
#guard_msgs in
#print axioms hidden_rule_parameter

-- A recursive template may use an initial fact but must not consume occurrences
-- causally produced by its own instances and grow `next (next ...)` until a bound.
#guard_msgs in
theorem recursive_template_reaches_fixpoint (x : Int) (h : P x) : P (next x) := by
  crush [grow, *]

-- Generated instances remain ordinary consequences: they cannot turn an
-- inconsistent witness requirement into a theorem.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem instances_do_not_strengthen (x : Int) :
    ∃ y, R x y ∧ ¬R x y := by
  crush [step]

end GroundInstantiation
