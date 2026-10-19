import Crush

/-!
Inhabited defunctionalized function spaces need no padding, but application axioms
must retain domain and result guards. Constant functions, projections, and original
local values supply witnesses without specializing metavariables. Native function
sorts still require validity and canonical-extension constraints.
-/

open Lean Meta Crush

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

-- An inhabited codomain supplies a constant function over an abstract domain.
run_meta do
  withLocalDeclD `A (mkSort (.succ .zero)) fun a => do
    let arrow ← mkArrow a (mkConst ``Nat)
    let (guard, _) ← TranslateM.run {} do
      wfCondition arrow (.const "f")
    unless guard.isNone do
      throwError "nonempty codomain did not establish function inhabitation"

-- Empty → Empty is inhabited, but its application still needs the argument guard.
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

-- A local function witnesses inhabitation without separate domain or codomain witnesses.
run_meta do
  withLocalDeclD `A (mkSort (.succ .zero)) fun a => do
    withLocalDeclD `B (mkSort (.succ .zero)) fun b => do
      let arrow ← mkArrow a b
      withLocalDeclD `f arrow fun _ => do
        let (guard, _) ← TranslateM.run {} do
          wfCondition arrow (.const "f")
        unless guard.isNone do
          throwError "local function witness did not establish inhabitation"

-- Projection matching must not specialize an unknown arrow into an inhabited identity.
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

-- Native function sorts still contain invalid functions when the Lean space is inhabited.
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
