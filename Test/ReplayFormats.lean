import Crush.Solver.Replay.Attr

open Lean Meta Elab Tactic
open Crush Crush.SMT

namespace ReplayFormatTests

register_replay_rule Alethe << (format_specific (nat n)) => by exact Nat.le_refl n >>
register_replay_rule CPC << (format_specific (nat n)) => by exact Nat.le_succ n >>
register_replay_rule Alethe | CPC << (shared_format ..) => by trivial >>
register_crush_replay rule << (legacy_alethe ..) => by trivial >>
register_replay_rule CPC low << (format_priority ..) => by trivial >>
register_replay_rule CPC high << (format_priority ..) => by trivial >>
register_replay_rule CPC << (isolated_context ..) => by assumption >>

@[crush_replay_rule CPC "cpc_attribute"]
def fromAttribute : ReplayRuleHandler := fun ctx => do
  if ctx.format == .cpc then ctx.runTactic (← `(tactic| trivial)) else pure none

@[crush_replay_rule CPC]
def cpcWildcard : ReplayRuleHandler := fun _ => pure none

run_meta do
  let alethe ← getReplayRuleHandlers .alethe
  let cpc ← getReplayRuleHandlers .cpc
  unless alethe.contains "legacy_alethe" && !cpc.contains "legacy_alethe" &&
      cpc.contains "cpc_attribute" && !alethe.contains "cpc_attribute" do
    throwError "format-specific replay registrations leaked between formats"
  unless alethe.contains "shared_format" && cpc.contains "shared_format" do
    throwError "shared replay rule did not register for both formats"
  let priorities := (cpc.getD "format_priority" #[]).map (·.priority)
  unless priorities.size == 2 && priorities[0]! > priorities[1]! do
    throwError "CPC handler priorities were not preserved"

elab "test_replay_format " format:str rule:str : tactic => do
  let format := if format.getString == "CPC" then ReplayFormat.cpc else .alethe
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let registry ← getReplayRuleHandlers format
    let result ← runReplayRuleHandlers registry {
      format, stepId := "test", rule := rule.getString
      target, targetLiterals := #[target], premises := #[], args := #[.atom "3"]
      decodeTerm := fun _ => return none
      decodeSort := fun _ => return none
      toProp := pure }
    if rule.getString == "isolated_context" then
      if result.isSome then throwError "CPC handler used an unselected hypothesis"
    else
      let some proof := result | throwError "format-specific rule declined"
      goal.assign proof
      replaceMainGoal []

example : 3 ≤ 3 := by test_replay_format "Alethe" "format_specific"
example : 3 ≤ 4 := by test_replay_format "CPC" "format_specific"
example : True := by test_replay_format "CPC" "cpc_attribute"
example (h : False) : False := by
  test_replay_format "CPC" "isolated_context"
  exact h

end ReplayFormatTests
