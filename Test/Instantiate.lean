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
