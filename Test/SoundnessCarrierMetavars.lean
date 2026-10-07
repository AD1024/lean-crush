import Crush

open Lean Meta Crush

-- A read-only instance comparison must not accept a specialization and then
-- discard the assignment that made that comparison valid.
run_meta do
  let dictionary ← mkFreshExprMVar (mkApp (mkConst ``NatCast [.zero]) (mkConst ``Int))
  if ← isDefEqReadOnly dictionary (mkConst ``instNatCastInt) then
    throwError "unresolved dictionary was accepted as the library instance"
  if ← dictionary.mvarId!.isAssigned then
    throwError "read-only instance comparison assigned its input"

-- A query-local Int must not turn an unresolved carrier into an unguarded sort.
run_meta do
  let carrier ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `n (mkConst ``Int) fun _ => do
    let (guard, _) ← TranslateM.run {} do
      discard <| emitSort carrier
      wfCondition carrier (.const "value")
    if guard.isNone then throwError "unresolved carrier lost its validity predicate"
    if ← carrier.mvarId!.isAssigned then
      throwError "inhabitation check specialized the unresolved carrier"

-- Likewise, an unresolved type of a local value does not witness Empty.
run_meta do
  let carrier ← mkFreshExprMVar (mkSort (.succ .zero))
  withLocalDeclD `x carrier fun _ => do
    let (guard, _) ← TranslateM.run {} do
      wfCondition (mkConst ``Empty) (.const "value")
    if guard.isNone then throwError "unresolved local value was used to inhabit Empty"
    if ← carrier.mvarId!.isAssigned then
      throwError "inhabitation check specialized a local value's type"
