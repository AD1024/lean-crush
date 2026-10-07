import Crush

open Lean Meta Elab Tactic Crush

namespace SoundnessRuntimeFallback

private def leakName : Name := `SoundnessRuntimeFallback.leakedDeclaration

-- Mutate both the environment and metavariable state before failing. Recovery
-- must restore both, even when a finisher assigned a goal before its exception.
private def mutateBeforeFailure (goal : MVarId) : TacticM Unit := do
  addDecl <| .axiomDecl {
    name := leakName
    levelParams := []
    type := mkConst ``True
    isUnsafe := false }
  goal.assign (mkConst ``True.intro)

elab "runtime_depth_failure" : tactic => do
  mutateBeforeFailure (← getMainGoal)
  throwMaxRecDepthAt (← getRef)

elab "runtime_heartbeat_failure" : tactic => do
  mutateBeforeFailure (← getMainGoal)
  Core.throwMaxHeartbeat `runtimeTest `maxHeartbeats 1000

private def checkNoLeak : TacticM Unit := do
  if (← getEnv).contains leakName then
    throwError "a declined runtime attempt leaked an environment declaration"

private def runTacticTest (test : TacticM Unit) : MetaM Unit := do
  let goal ← mkFreshExprMVar (mkConst ``True)
  discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! test

-- Both the user finisher and every ladder rung must recover resource failures.
run_meta runTacticTest do
  for failing in #[← `(tactic| runtime_depth_failure),
                   ← `(tactic| runtime_heartbeat_failure)] do
    let succeeds ← `(tactic| exact True.intro)
    let manualGoal ← mkFreshExprMVar (mkConst ``True)
    unless ← tryReconstruct manualGoal.mvarId! #[] #[succeeds] (some failing) do
      throwError "a runtime failure in the manual finisher prevented fallback"
    checkNoLeak
    let ladderGoal ← mkFreshExprMVar (mkConst ``True)
    unless ← tryReconstruct ladderGoal.mvarId! #[] #[failing, succeeds] do
      throwError "a runtime failure in a ladder rung prevented the next finisher"
    checkNoLeak
    let declinedGoal ← mkFreshExprMVar (mkConst ``False)
    if ← tryReconstruct declinedGoal.mvarId! #[] #[failing] then
      throwError "a failed runtime attempt unexpectedly proved False"
    if ← declinedGoal.mvarId!.isAssigned then
      throwError "runtime recovery left the original goal assigned"
    checkNoLeak

private def replayContext : ReplayRuleContext := {
  stepId := "runtime-test"
  rule := "runtime-test"
  target := mkConst ``True
  targetLiterals := #[mkConst ``True]
  premises := #[]
  args := #[]
  decodeTerm := fun _ => pure none
  decodeSort := fun _ => pure none
  toProp := pure }

-- Isolated replay tactics and metaprograms decline cleanly, so their caller can
-- try another replay procedure after a local resource limit.
run_meta runTacticTest do
  for failing in #[← `(tactic| runtime_depth_failure),
                   ← `(tactic| runtime_heartbeat_failure)] do
    if (← replayContext.runTactic failing).isSome then
      throwError "failed replay tactic returned a proof"
    checkNoLeak
    unless (← replayContext.runTactic (← `(tactic| exact True.intro))).isSome do
      throwError "failed replay tactic prevented a subsequent replay"
  if (← replayContext.runMeta fun goal => do
      mutateBeforeFailure goal
      throwMaxRecDepthAt (← getRef)).isSome then
    throwError "failed replay metaprogram returned a proof"
  checkNoLeak
  unless (← replayContext.runMeta fun goal => do
      goal.assign (mkConst ``True.intro)
      pure true).isSome do
    throwError "failed replay metaprogram prevented a subsequent replay"

-- A certificate handler can fail before it reaches an isolated tactic. The
-- complete replay attempt must still decline and restore its environment.
@[crush_replay_rule "runtime-failure"]
def failingCertificateHandler : ReplayRuleHandler := fun _ => do
  let goal ← mkFreshExprMVar (mkConst ``True)
  mutateBeforeFailure goal.mvarId!
  throwMaxRecDepthAt (← getRef)

run_meta runTacticTest do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let certificate := "unsat ((step runtime (cl false) :rule runtime-failure))"
  let cfg : Crush.Config := { trust := .reconstruct, reconstruct := .auto }
  let some parsed := Alethe.parseProof certificate | throwError "bad test certificate"
  let saved ← saveState
  let reachesRuntimeFailure ← tryCatchRuntimeEx (do
    discard <| Alethe.replay parsed (SMT.parseSexps certificate) {} {}
    pure false
  ) fun exception => pure exception.isMaxRecDepth
  restoreState saved
  unless reachesRuntimeFailure do
    throwError "the test certificate did not exercise the runtime failure"
  discard <| tryProofReplay goal.mvarId! cfg { cfg } (SMT.parseSexps certificate)
  if ← goal.mvarId!.isAssigned then
    throwError "declined replay left the original goal assigned"
  checkNoLeak
  unless ← tryReconstruct goal.mvarId! #[] #[← `(tactic| exact True.intro)] do
    throwError "runtime replay failure prevented core fallback"

-- Check the actual cancellation exception outside CoreM: ordinary elaborator
-- catches deliberately rethrow it, so observing the EIO result is essential.
run_meta do
  let action : CoreM Unit := do
    MetaM.run' <| runTacticTest do
      discard <| replayContext.runMeta fun _ => throwInterruptException
  let context ← readThe Core.Context
  let state ← getThe Core.State
  match ← (action.run context state).toBaseIO with
  | .error exception =>
    unless exception.isInterrupt do
      throwError "unexpected exception while testing cancellation"
  | .ok _ => throwError "runtime recovery swallowed cancellation"

end SoundnessRuntimeFallback
