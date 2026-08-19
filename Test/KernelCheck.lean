import Crush.Solver.Reconstruct

open Lean Meta Elab Tactic
open Crush

private def expectKernelRejection (action : MetaM Unit) : MetaM Unit := do
  let accepted ←
    try
      action
      pure true
    catch _ =>
      pure false
  if accepted then
    throwError "kernel validation unexpectedly accepted the proof"

private def malformedDecideProof : MetaM (Expr × Expr) := do
  let one := mkIntLit 1
  let proposition ← mkEq one one
  let expected ← mkEq proposition (mkConst ``False)
  let decision ← mkDecide proposition
  let proof := mkApp3 (mkConst ``eq_false_of_decide) proposition decision.appArg!
    eagerReflBoolFalse
  return (expected, proof)

run_meta do
  let snapshot ← KernelCheckSnapshot.capture
  discard <| kernelCheckProof snapshot (mkConst ``True) (mkConst ``True.intro)
  let expected ← mkFreshExprMVar (mkSort Level.zero)
  expected.mvarId!.assign (mkConst ``True)
  discard <| kernelCheckProof snapshot expected (mkConst ``True.intro)
  expectKernelRejection do
    discard <| kernelCheckProof snapshot (mkConst ``False) (mkConst ``True.intro)
  let (expected, malformed) ← malformedDecideProof
  expectKernelRejection do
    discard <| kernelCheckProof snapshot expected malformed

run_meta do
  withLocalDeclD `α (mkSort (.succ .zero)) fun α =>
    withLocalDeclD `x α fun x =>
      withLocalDeclD `unused (mkConst ``False) fun _ =>
        withLetDecl `y α x fun y => do
          let params ← collectProofParams #[y]
          unless params.map (·.fvarId!) == #[α.fvarId!, x.fvarId!, y.fvarId!] do
            throwError "proof parameter closure omitted a dependent type or visible let value"
  withLocalDeclD `excluded (mkConst ``False) fun excluded =>
    let value := mkApp2 (mkConst ``False.elim [Level.zero]) (mkConst ``Nat) excluded
    withLetDecl `opaqueValue (mkConst ``Nat) value (nondep := true) fun opaqueValue => do
      let params ← collectProofParams #[opaqueValue]
      unless params.map (·.fvarId!) == #[opaqueValue.fvarId!] do
        throwError "a nondependent let value leaked an excluded hypothesis"

run_meta do
  let saved ← Lean.Meta.saveState
  try
    let snapshot ← KernelCheckSnapshot.capture
    let first ← mkAuxTheorem (mkConst ``True) (mkConst ``True.intro)
      (kind? := some `crushKernelCheck) (cache := false)
    let second ← mkAuxTheorem (mkConst ``True) first
      (kind? := some `crushKernelCheck) (cache := false)
    discard <| kernelCheckProof snapshot (mkConst ``True) second
  finally
    saved.restore

elab "close_with_generated_axiom" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    let name ← mkAuxDeclName `crushKernelCheckBad
    addDecl <| .axiomDecl {
      name
      levelParams := []
      type
      isUnsafe := false
    }
    goal.assign (mkConst name)
    replaceMainGoal []

elab "close_with_malformed_decide" : tactic => do
  let goal ← getMainGoal
  let (_, proof) ← malformedDecideProof
  goal.assign proof
  replaceMainGoal []

elab "close_with_generated_malformed_decide" : tactic => do
  let goal ← getMainGoal
  let (expected, malformed) ← malformedDecideProof
  let proof ← mkAuxTheorem expected malformed
    (kind? := some `crushKernelCheckBad) (cache := false)
  goal.assign proof
  replaceMainGoal []

run_meta do
  let (expected, _) ← malformedDecideProof
  let goal ← mkFreshExprMVar expected
  let accepted ← IO.mkRef true
  discard <| Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Tactic.run goal.mvarId! do
    accepted.set (← tryReconstruct goal.mvarId! #[] #[
      (← `(tactic| close_with_malformed_decide))])
  if ← accepted.get then
    throwError "reconstruction accepted the malformed `decide` proof"
  if ← goal.mvarId!.isAssigned then
    throwError "declined reconstruction left the original goal assigned"

run_meta do
  let (expected, _) ← malformedDecideProof
  let goal ← mkFreshExprMVar expected
  let accepted ← IO.mkRef true
  discard <| Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Tactic.run goal.mvarId! do
    accepted.set (← tryReconstruct goal.mvarId! #[] #[
      (← `(tactic| close_with_generated_malformed_decide))])
  if ← accepted.get then
    throwError "reconstruction accepted a malformed generated declaration"
  if ← goal.mvarId!.isAssigned then
    throwError "declined reconstruction left the original goal assigned"

run_meta do
  let value := mkNatLit 1
  let expected ← mkEq value value
  let goal ← mkFreshExprMVar expected
  let accepted ← IO.mkRef true
  discard <| Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Tactic.run goal.mvarId! do
    accepted.set (← tryReconstruct goal.mvarId! #[] #[
      (← `(tactic| native_decide))])
  if ← accepted.get then
    throwError "strict reconstruction accepted a native-decision axiom"
  if ← goal.mvarId!.isAssigned then
    throwError "declined native reconstruction left the original goal assigned"

run_meta do
  let goal ← mkFreshExprMVar (mkConst ``False)
  let accepted ← IO.mkRef true
  discard <| Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Tactic.run goal.mvarId! do
    accepted.set (← tryReconstruct goal.mvarId! #[] #[
      (← `(tactic| close_with_generated_axiom))])
  if ← accepted.get then
    throwError "reconstruction accepted a proof backed by a generated axiom"
  if ← goal.mvarId!.isAssigned then
    throwError "declined reconstruction left the original goal assigned"

set_option crush.reconstruct.trustNativeDecide true in
run_meta do
  let goal ← mkFreshExprMVar (mkConst ``False)
  let accepted ← IO.mkRef true
  discard <| Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Tactic.run goal.mvarId! do
    accepted.set (← tryReconstruct goal.mvarId! #[] #[
      (← `(tactic| close_with_generated_axiom))])
  if ← accepted.get then
    throwError "native trust accepted an unrelated generated axiom"
  if ← goal.mvarId!.isAssigned then
    throwError "declined reconstruction left the original goal assigned"

run_meta do
  let saved ← Lean.Meta.saveState
  try
    let snapshot ← KernelCheckSnapshot.capture
    let axiomName ← mkAuxDeclName `crushKernelCheckBad
    addDecl <| .axiomDecl {
      name := axiomName
      levelParams := []
      type := mkConst ``False
      isUnsafe := false
    }
    let wrapper ← mkAuxTheorem (mkConst ``False) (mkConst axiomName)
      (kind? := some `crushKernelCheck) (cache := false)
    expectKernelRejection do
      discard <| kernelCheckProof snapshot (mkConst ``False) wrapper
  finally
    saved.restore
