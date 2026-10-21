import Crush.Solver.Reconstruct
import Lean.Meta.Native

/-!
Native axiom names and Boolean-equality types do not establish a valid computation.
Check generated and pre-existing dependencies, accept genuine native decisions, and
reject substituted computations even with bit-vector trust enabled. The standard
checker must also reject substituted inputs hidden behind ordinary definitions.
-/

open Lean Meta Elab Tactic
open Crush

namespace SoundnessNativeProvenance

private def expectNativeRejection (snapshot : KernelCheckSnapshot)
    (type proof : Expr) : MetaM Unit := do
  let accepted ← try
    discard <| kernelCheckProof snapshot type proof
    pure true
  catch _ => pure false
  if accepted then
    throwError "native trust accepted a forged evaluation axiom"

-- Forge matching names and types on both sides of the snapshot boundary.
set_option crush.reconstruct.trustBvDecide true in
set_option crush.reconstruct.trustNativeDecide true in
run_meta do
  let saved ← saveState
  try
    for tacticName in #[`bv_decide, `native_decide, `decide] do
      for existing in #[false, true] do
        let before ← KernelCheckSnapshot.capture
        let assertion ←
          if tacticName == `bv_decide then pure (mkConst ``Bool.false)
          else mkDecide (mkConst ``False)
        let type ← mkEq assertion (mkConst ``Bool.true)
        let name ← mkAuxDeclName (`_native ++ tacticName ++ `ax)
        addDecl <| .axiomDecl { name, levelParams := [], type, isUnsafe := false }
        let snapshot ← if existing then KernelCheckSnapshot.capture else pure before
        expectNativeRejection snapshot type (mkConst name)
  finally
    saved.restore

-- Positive controls include the `decide +native` naming convention.
set_option crush.reconstruct.trustBvDecide true in
set_option crush.reconstruct.trustNativeDecide true in
run_meta do
  let saved ← saveState
  try
    for tacticName in #[`native_decide, `decide] do
      let snapshot ← KernelCheckSnapshot.capture
      let assertion ← mkDecide (mkConst ``True)
      let .success proof ← nativeEqTrue tacticName assertion
        | throwError "native evaluation of true unexpectedly failed"
      discard <| kernelCheckProof snapshot (← inferType proof) proof
  finally
    saved.restore

set_option crush.reconstruct.trustNativeDecide true in
run_meta do
  let goal ← mkFreshExprMVar (← mkEq (mkNatLit 2) (mkNatLit 2))
  let accepted ← IO.mkRef false
  discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
    accepted.set (← tryReconstruct goal.mvarId! #[]
      #[(← `(tactic| decide +native))])
  unless ← accepted.get do
    throwError "checked reconstruction rejected a real `decide +native` proof"

def trueImpl : Bool := true
@[implemented_by trueImpl] def falseAtKernel : Bool := false

elab "forge_bv_native_proof" : tactic => do
  let goal ← getMainGoal
  let .success proof ← nativeEqTrue `bv_decide (mkConst ``falseAtKernel)
    | throwError "forged native evaluation unexpectedly failed"
  let proof ← mkExpectedTypeHint proof
    (← mkEq (mkConst ``Bool.false) (mkConst ``Bool.true))
  let contradiction := mkApp (← mkAppM ``Bool.false_ne_true #[]) proof
  goal.assign (← mkAppOptM ``False.elim #[← goal.getType, contradiction])
  replaceMainGoal []

-- Reject implementation substitution under both policies and restore the goal.
run_meta do
  for trustBv in #[false, true] do
    withOptions (crush.reconstruct.trustBvDecide.set · trustBv) do
      let goal ← mkFreshExprMVar (mkConst ``False)
      let accepted ← IO.mkRef true
      discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
        accepted.set (← tryReconstruct goal.mvarId! #[]
          #[(← `(tactic| forge_bv_native_proof))])
      if ← accepted.get then
        throwError "bit-vector native trust accepted an arbitrary native computation"
      if ← goal.mvarId!.isAssigned then
        throwError "declined native reconstruction left the original goal assigned"

-- Hide a substituted certificate under an ordinary definition.
theorem certificateControl (a b : BitVec 8) :
    (a &&& b) + (a ^^^ b) = a ||| b := by bv_decide

set_option crush.reconstruct.trustBvDecide true in
run_meta do
  let saved ← saveState
  try
    let axioms ← collectAxioms ``certificateControl
    let some axiomName := axioms.find? (·.toString.contains "._native.bv_decide.ax")
      | throwError "bit-vector control did not produce a native certificate axiom"
    let originalAssertion := (← getConstInfo axiomName).type.getAppArgs[1]!
    let originalArguments := originalAssertion.getAppArgs
    let certificateName := originalArguments[1]!.constName!
    for existing in #[false, true] do
      let before ← KernelCheckSnapshot.capture
      let substitutedName ← mkAuxDeclName `substitutedCertificate
      addDecl <| .defnDecl {
        name := substitutedName
        levelParams := []
        type := mkConst ``String
        value := toExpr "invalid"
        hints := .abbrev
        safety := .safe }
      setImplementedBy substitutedName certificateName
      let wrapperName ← mkAuxDeclName `wrappedCertificate
      addAndCompile <| .defnDecl {
        name := wrapperName
        levelParams := []
        type := mkConst ``String
        value := mkConst substitutedName
        hints := .abbrev
        safety := .safe }
      let assertion := mkApp2 (mkConst ``Std.Tactic.BVDecide.Reflect.verifyBVExpr)
        originalArguments[0]! (mkConst wrapperName)
      let .success proof ← nativeEqTrue `bv_decide assertion
        | throwError "substituted certificate did not reproduce native evaluation bypass"
      let snapshot ← if existing then KernelCheckSnapshot.capture else pure before
      expectNativeRejection snapshot (← inferType proof) proof
  finally
    saved.restore

end SoundnessNativeProvenance
