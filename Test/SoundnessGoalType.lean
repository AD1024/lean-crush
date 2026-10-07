import Crush

open Lean Meta Crush

/-- error: crush: expected a proposition, but the goal has type `Nat` -/
#guard_msgs(error, substring := true) in
def rejectsDataGoal : Nat := by crush

-- Reject a function-valued data goal before introducing its argument.
/-- error: crush: expected a proposition, but the goal has type `Int → Int` -/
#guard_msgs(error, substring := true) in
def rejectsFunctionDataGoal : Int → Int := by crush

-- The collection API must enforce the same boundary for direct metaprogram users.
run_meta do
  let goal ← mkFreshExprMVar (mkConst ``Nat)
  let rejected ← try
    discard <| collectFacts goal.mvarId!
    pure false
  catch exception =>
    pure ((← exception.toMessageData.toString).startsWith
      "crush: expected a proposition")
  unless rejected do
    throwError "fact collection accepted a non-propositional goal"
  if ← goal.mvarId!.isAssigned then
    throwError "rejecting a non-propositional goal assigned it"

-- Propositional forall-goals still introduce their arguments normally.
example : ∀ x : Int, x + 0 = x := by crush
