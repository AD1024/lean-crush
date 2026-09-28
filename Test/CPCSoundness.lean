import Crush.Solver.CPC

open Lean Meta Elab Tactic
open Crush Crush.SMT

namespace CPCSoundnessTests

elab "cpc_must_decline " source:str : tactic => do
  let raw := parseSexps source.getString
  let .ok proof := CPC.parseProofSexps raw
    | throwError "soundness test certificate did not parse"
  let saved ← saveState
  let result ← Replay.replay proof raw {} {} .cpc
  restoreState saved
  if result.toOption.isSome then
    throwError "CPC replay manufactured a proof from untrusted assumptions"

-- Top-level certificate assumptions cannot introduce new Lean hypotheses.
example (unselected : False) : True := by
  cpc_must_decline "((assume h false)
    (step done false :rule arbitrary :premises (h)))"
  trivial

-- A checked local contradiction proves only an implication outside its scope.
example (unselected : False) : True := by
  cpc_must_decline "((assume-push h false)
    (step local_false false :rule scope_body :premises (h))
    (step-pop closed :rule scope :premises (local_false))
    (step escape false :rule arbitrary :premises (closed)))"
  trivial

-- Neither the conclusion nor the rule name supplies a proof.
example : True := by
  cpc_must_decline "((step done false :rule refl :args (false)))"
  trivial

@[crush_replay_rule CPC "invalid_handler"]
private def invalidHandler : ReplayRuleHandler := fun _ =>
  return some (mkConst ``True.intro)

elab "cpc_reject_invalid_handler" : tactic => do
  let target := mkConst ``False
  let registry ← getReplayRuleHandlers .cpc
  let context : ReplayRuleContext := {
    format := .cpc, stepId := "invalid", rule := "invalid_handler"
    target, targetLiterals := #[], premises := #[], args := #[]
    decodeTerm := fun _ => return none
    decodeSort := fun _ => return none
    toProp := pure }
  let mut rejected := false
  try
    discard <| runReplayRuleHandlers registry context
  catch _ => rejected := true
  unless rejected do throwError "CPC accepted a handler proof of the wrong proposition"

example : True := by
  cpc_reject_invalid_handler
  trivial

end CPCSoundnessTests
