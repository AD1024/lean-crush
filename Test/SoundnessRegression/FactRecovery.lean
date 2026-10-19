import Crush

/-!
Unsupported premises may be omitted only after rolling back commands, evidence,
caches, and metavariable assignments. An unsupported negated goal remains fatal.
Retained proofs must resolve unused universe arguments and preserve their dependencies;
the public unary trust-axiom application must also remain available.
-/

open Lean Meta Crush

namespace SoundnessFactRecovery

set_option linter.unusedVariables false

example (y : Int) (h : y > 2) : y > 1 := by
  let v : Fin 3 := 1
  crush

example (y : Int) (h : y > 2) : y > 1 := by
  let F : Type → Type := List
  crush

structure Pt where
  x : Int
  y : Int

example (pts : List Pt) (h : 0 < pts.length) (q : Pt → Prop)
    (hx : q pts[0]) (n : Int) (hn : n > 3) : n > 2 := by
  crush

run_meta do
  let goalType ← withLocalDeclD `x (mkApp (mkConst ``Fin) (mkNatLit 3)) fun x => do
    mkAppM ``Exists #[← mkLambdaFVars #[x] (← mkEq x x)]
  let negative : Fact := {
    prop := mkNot goalType
    proof := none
    descr := "negated goal"
    negated := true }
  let failed ← try
    discard <| buildScript {} #[negative]
    pure false
  catch _ => pure true
  unless failed do throwError "an unsupported goal was discarded"

-- Deliberately mutate every relevant state component before failing.
def rollbackFact (_n : Int) : Prop := True

@[crush_lower rollbackFact]
def rollbackLowering : LoweringHandler := fun ctx => do
  let argument := ctx.args[0]!
  argument.mvarId!.assign (← mkAppM ``Int.ofNat #[mkNatLit 0])
  TranslateM.emitCommand (.assert (.const "false"))
  discard <| TranslateM.recordEncodingEvidence (mkConst ``True) (mkConst ``True.intro)
  modify fun state => { state with
    nonemptyCarriers := state.nonemptyCarriers.insert (mkConst ``Empty) true }
  throwError "deliberate unsupported fact"

run_meta do
  let argument ← mkFreshExprMVar (mkConst ``Int)
  let (_, state) ← buildScript {} #[
    { prop := mkApp (mkConst ``rollbackFact) argument, proof := none, descr := "failed fact" },
    { prop := mkNot (mkConst ``False), proof := none, descr := "negated goal", negated := true }]
  if ← argument.mvarId!.isAssigned then
    throwError "a failed fact retained a metavariable assignment"
  unless state.encodingEvidence.isEmpty && state.nonemptyCarriers.isEmpty &&
      state.facts.size == 1 && state.facts[0]!.id == 0 && state.commands.size == 1 do
    throwError "a failed fact retained translation state"
  unless SMT.commandToString state.commands[0]! == "(assert (! (not false) :named crush_fact_0))" do
    throwError "a failed fact retained logical commands"

universe u
axiom universeHint : (PUnit.{u+1} = PUnit.{u+1}) ∧ (0 : Int) = 1

theorem retainedUniverseHint : False := by crush [universeHint]

run_meta do
  let axioms ← collectAxioms ``retainedUniverseHint
  unless axioms.contains ``universeHint && axioms.contains ``Crush.crushSorry do
    throwError "resolving universe arguments lost the hint dependency"

-- Exercise the public unary trust-axiom API.
open Elab Tactic in
elab "legacyTrustApplication" : tactic => do
  let goal ← getMainGoal
  goal.assign (mkApp (mkConst ``Crush.crushSorry) (← goal.getType))
  replaceMainGoal []

theorem legacyApi : True := by legacyTrustApplication

end SoundnessFactRecovery
