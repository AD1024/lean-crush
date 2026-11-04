import Crush

/-!
Encoding eligibility checks must not specialize caller metavariables, even
temporarily. Unresolved dictionaries and carriers cannot gain canonical-instance
semantics or lose validity guards through speculative matching.
-/

open Lean Meta Crush

run_meta do
  let dictionary ← mkFreshExprMVar (mkApp (mkConst ``NatCast [.zero]) (mkConst ``Int))
  if ← isDefEqRigid dictionary (mkConst ``instNatCastInt) then
    throwError "unresolved dictionary was accepted as the library instance"
  if ← dictionary.mvarId!.isAssigned then
    throwError "read-only instance comparison assigned its input"
  unless ← isDefEqReadOnly dictionary (mkConst ``instNatCastInt) do
    throwError "pattern matching lost its ability to test an instantiation"
  if ← dictionary.mvarId!.isAssigned then
    throwError "speculative pattern comparison retained its assignment"

-- A local Int cannot witness an unresolved carrier.
run_meta do
  let carrier ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `n (mkConst ``Int) fun _ => do
    let (guard, _) ← TranslateM.run {} do
      discard <| emitSort carrier
      wfCondition carrier (.const "value")
    if guard.isNone then throwError "unresolved carrier lost its validity predicate"
    if ← carrier.mvarId!.isAssigned then
      throwError "inhabitation check specialized the unresolved carrier"

-- An unresolved local type cannot witness Empty.
run_meta do
  let carrier ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `x carrier fun _ => do
    let (guard, _) ← TranslateM.run {} do
      wfCondition (mkConst ``Empty) (.const "value")
    if guard.isNone then throwError "unresolved local value was used to inhabit Empty"
    if ← carrier.mvarId!.isAssigned then
      throwError "inhabitation check specialized a local value's type"
