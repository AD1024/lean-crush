import Crush

open Lean Meta Crush

-- Inhabited defunctionalized function spaces need no padding functions. Their
-- application axioms must still confine results to the valid codomain.
run_meta do
  let natArrow ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let ((guard, needsGuard), state) ← TranslateM.run {} do
    discard <| emitSort natArrow
    return (← wfCondition natArrow (.const "f"), ← needsWFGuard natArrow)
  unless guard.isNone && !needsGuard do
    throwError "inhabited defunctionalized arrow retained a function guard"
  unless state.commands.any (fun command => match command with
    | .assert (.forallE binders (.app (.symb "=>") _)) => binders.size == 2
    | _ => false) do
    throwError "function application lost its guarded result axiom"
  let optionArrow := mkApp (mkConst ``Option [.zero]) natArrow
  let (guard, _) ← TranslateM.run {} do
    discard <| emitSort optionArrow
    wfCondition optionArrow (.const "optionalFunction")
  unless guard.isNone do
    throwError "inhabited function field introduced a datatype guard"

-- A known nonempty result supplies a constant function even when the domain is
-- abstract and has no inhabitant or matching projection argument.
run_meta do
  withLocalDeclD `A (mkSort (.succ .zero)) fun a => do
    let arrow ← mkArrow a (mkConst ``Nat)
    let (guard, _) ← TranslateM.run {} do
      wfCondition arrow (.const "f")
    unless guard.isNone do
      throwError "nonempty codomain did not establish function inhabitation"

-- Projection witnesses work without assuming the projected type is inhabited.
-- In particular, Empty → Empty is inhabited but its argument guard is essential.
run_meta do
  let empty := mkConst ``Empty
  let identity ← mkArrow empty empty
  let projection ← mkArrow (mkConst ``Int) identity
  for arrow in #[identity, projection] do
    let ((guard, needsGuard), state) ← TranslateM.run {} do
      discard <| emitSort arrow
      return (← wfCondition arrow (.const "f"), ← needsWFGuard arrow)
    unless guard.isNone && !needsGuard do
      throwError "projection function space retained a validity predicate"
    unless state.commands.any (fun command => match command with
      | .assert (.forallE _ (.app (.symb "=>") _)) => true
      | _ => false) do
      throwError "projection application lost its Empty argument guard"

-- A function in the original context is also an inhabitation witness, even when
-- neither its domain nor its codomain has a separate inhabitant.
run_meta do
  withLocalDeclD `A (mkSort (.succ .zero)) fun a => do
    withLocalDeclD `B (mkSort (.succ .zero)) fun b => do
      let arrow ← mkArrow a b
      withLocalDeclD `f arrow fun _ => do
        let (guard, _) ← TranslateM.run {} do
          wfCondition arrow (.const "f")
        unless guard.isNone do
          throwError "local function witness did not establish inhabitation"

-- Unknown-empty spaces must retain padding, and speculative projection matching
-- must not specialize a metavariable to turn an unknown arrow into an identity.
run_meta do
  let carrier ← mkFreshExprMVar (mkSort (.succ .zero))
  for domain in #[mkConst ``Int, carrier] do
    let arrow ← mkArrow domain (mkConst ``Empty)
    let (guard, _) ← TranslateM.run {} do
      wfCondition arrow (.const "f")
    unless guard.isSome do
      throwError "possibly empty function space lost its validity predicate"
  if ← carrier.mvarId!.isAssigned then
    throwError "projection matching specialized an unresolved carrier"

-- Native function sorts contain invalid functions even when the Lean function
-- space is inhabited; neither result validity nor canonical extension may go.
run_meta do
  for base in #[mkConst ``Nat, mkConst ``Empty] do
    let arrow ← mkArrow base base
    let ((guard, needsGuard), _) ← TranslateM.run { hoMode := .native } do
      return (← wfCondition arrow (.const "f"), ← needsWFGuard arrow)
    unless guard.isSome && needsGuard do
      throwError "native function space lost its validity predicate"

set_option crush.timeout 2

example : True := by
  fail_if_success have : ∃ x : Empty, x = x := by crush
  fail_if_success have : ∃ f : Int → Empty, f = f := by crush
  trivial

example : ¬ ∃ f : Nat → Nat, f 0 < 0 := by crush
example (f g : Empty → Empty) : f = g := by crush
