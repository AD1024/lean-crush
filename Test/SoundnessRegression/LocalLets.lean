import Crush.Frontend.Collect

/-!
Visible local lets contribute defining equalities with kernel-checked proofs,
subject to explicit hypothesis selection. Hidden nondependent values remain opaque;
local type aliases are reduced by Lean rather than asserted as data equalities.
-/

open Lean Meta
open Crush

namespace SoundnessLocalLets

run_meta do
  withLocalDeclD `y (mkConst ``Int) fun y => do
    let value := mkApp2 (mkConst ``Int.add) y (mkIntLit 1)
    withLetDecl `x (mkConst ``Int) value fun x => do
      let target ← mkEq x (mkIntLit 0)
      let goal ← mkFreshExprMVar target
      let facts ← collectFacts goal.mvarId! {} false
      let definitions := facts.filter fun fact => fact.descr == "let x"
      unless definitions.size == 1 do
        throwError "collector omitted the visible local let's defining equality"
      let fact := definitions[0]!
      unless fact.prop == (← mkEq x value) do
        throwError "local let equality has the wrong endpoints"
      let some proof := fact.proof | throwError "local let equality has no proof"
      match Kernel.check (← getEnv) (← getLCtx)
          (mkApp2 (mkConst ``id [0]) fact.prop proof) with
      | .ok _ => pure ()
      | .error _ => throwError "local let equality's proof is invalid"
      -- An explicit [] continues to omit unselected local facts.
      let restricted ← collectFacts goal.mvarId! { allHyps := false } false
      unless restricted.size == 1 && restricted[0]!.negated do
        throwError "strict hints unexpectedly included a local let equation"

run_meta do
  withLetDecl `x (mkConst ``Int) (mkIntLit 1) (nondep := true) fun x => do
    let goal ← mkFreshExprMVar (← mkEq x (mkIntLit 0))
    let facts ← collectFacts goal.mvarId! {} false
    unless facts.size == 1 && facts[0]!.negated do
      throwError "collector exposed the hidden value of a nondependent local"

run_meta do
  withLetDecl `T (mkSort (.succ .zero)) (mkConst ``Nat) fun _ => do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let facts ← collectFacts goal.mvarId! {} false
    unless facts.size == 1 && facts[0]!.negated do
      throwError "collector asserted an unsupported equality between types"

end SoundnessLocalLets
