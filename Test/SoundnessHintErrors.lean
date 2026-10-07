import Crush

open Lean Meta Elab Tactic Crush

-- Elaborating an invalid hint must throw before any successful proof path or
-- solver call, including when the goal itself is independently trivial.
private def expectHintError (tactic : TSyntax `tactic) : MetaM Unit := do
  let goal ← mkFreshExprMVar (mkConst ``True)
  discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
    let rejected ← try
      Tactic.withSuppressedMessages <| evalTactic tactic
      pure false
    catch exception =>
      pure ((← exception.toMessageData.toString).startsWith "Unknown identifier")
    unless rejected do
      throwError "crush continued after a hint failed to elaborate"
    if ← goal.mvarId!.isAssigned then
      throwError "an invalid hint assigned the original goal"

run_meta do
  expectHintError (← `(tactic| crush [(nonexistent_soundness_hint : True)]))
  expectHintError (← `(tactic| crush [(by exact nonexistent_soundness_hint : True)]))

set_option crush.trust "reconstruct" in
run_meta do
  expectHintError (← `(tactic| crush with [(nonexistent_soundness_hint : True)]))
  expectHintError (← `(tactic| crush with [(by exact nonexistent_soundness_hint : True)]))

-- Valid polymorphic hints still elaborate with their remaining metavariables
-- available for the ordinary abstraction and monomorphization passes.
example (xs ys zs : List Int) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  crush [List.append_assoc]
