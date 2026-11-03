import Crush

/-!
Only propositional goals may enter collection and proof automation. Reject data
goals before introducing function arguments, while preserving propositional forall-goals.
-/

open Lean Meta Crush

/-- error: crush: expected a proposition, but the goal has type `Nat` -/
#guard_msgs(error, substring := true) in
def rejectsDataGoal : Nat := by crush

/-- error: crush: expected a proposition, but the goal has type `Int → Int` -/
#guard_msgs(error, substring := true) in
def rejectsFunctionDataGoal : Int → Int := by crush

-- Exercise the collection API directly.
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

example : ∀ x : Int, x + 0 = x := by crush
