import Crush

/-!
Invalid or unfinished hints must fail before any proof shortcut or solver call,
even on independently trivial goals. Valid polymorphic hints retain the metavariables
needed by abstraction and monomorphization.
-/

open Lean Meta Elab Tactic Crush

private def expectHintError (tactic : TSyntax `tactic) : MetaM Unit := do
  let goal ← mkFreshExprMVar (mkConst ``True)
  discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
    let rejected ← try
      Tactic.withSuppressedMessages <| evalTactic tactic
      pure false
    catch exception =>
      let message ← exception.toMessageData.toString
      pure (message.startsWith "Unknown identifier" ||
        message.startsWith "crush: hint elaboration failed")
    unless rejected do
      throwError "crush continued after a hint failed to elaborate"
    if ← goal.mvarId!.isAssigned then
      throwError "an invalid hint assigned the original goal"

run_meta do
  expectHintError (← `(tactic| crush [(nonexistent_soundness_hint : True)]))
  expectHintError (← `(tactic| crush [(by exact nonexistent_soundness_hint : True)]))
  expectHintError (← `(tactic| crush [(by skip : False)]))

set_option crush.trust "reconstruct" in
run_meta do
  expectHintError (← `(tactic| crush with [(nonexistent_soundness_hint : True)]))
  expectHintError (← `(tactic| crush with [(by exact nonexistent_soundness_hint : True)]))
  expectHintError (← `(tactic| crush with [(by skip : False)]))

example (xs ys zs : List Int) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  crush [List.append_assoc]
