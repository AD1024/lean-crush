import Crush
import Lean.Meta.Native

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

-- Check both new declarations and declarations already present at snapshot time.
-- Matching the name and Bool-equality shape does not justify the false assertion.
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

-- Real computations still pass, including the `decide +native` naming convention.
set_option crush.reconstruct.trustBvDecide true in
set_option crush.reconstruct.trustNativeDecide true in
run_meta do
  let saved ← saveState
  try
    for tacticName in #[`bv_decide, `native_decide, `decide] do
      let snapshot ← KernelCheckSnapshot.capture
      let assertion ←
        if tacticName == `bv_decide then pure (mkConst ``Bool.true)
        else mkDecide (mkConst ``True)
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

end SoundnessNativeProvenance
