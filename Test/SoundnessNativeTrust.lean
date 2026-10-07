import Crush
import Lean.Meta.Native

open Lean Meta Elab Tactic
open Crush

namespace SoundnessNativeTrust

-- The legacy reflection axioms remain supported by Lean and must obey our policy.
set_option linter.deprecated false

theorem compilerProof : True := Lean.trustCompiler
theorem boolReflection (a b : Bool) (h : Lean.reduceBool a = b) : a = b :=
  Lean.ofReduceBool a b h
theorem natReflection (a b : Nat) (h : Lean.reduceNat a = b) : a = b :=
  Lean.ofReduceNat a b h
theorem nativeProof : 1 + 1 = 2 := by native_decide
theorem decideNativeProof : 1 + 1 = 2 := by decide +native

-- Generate a real native-evaluation axiom with the bit-vector provenance tag
-- without requiring an external SAT solver in this policy test.
elab "native_bool_for_policy_test" : tactic => do
  let goal ← getMainGoal
  let .success proof ← nativeEqTrue `bv_decide (mkConst ``Bool.true)
    | throwError "native Boolean evaluation unexpectedly failed"
  goal.assign proof
  replaceMainGoal []

theorem bvProof : Bool.true = Bool.true := by native_bool_for_policy_test

private def checkProof (name : Name) (expectedAcceptance : Bool) : MetaM Unit := do
  let snapshot ← KernelCheckSnapshot.capture
  let proof := mkConst name
  let accepted ← try
    discard <| kernelCheckProof snapshot (← inferType proof) proof
    pure true
  catch _ => pure false
  unless accepted == expectedAcceptance do
    throwError "unexpected native trust result for `{name}`: accepted={accepted}"

-- All candidates predate the snapshots and all have valid kernel types.
run_meta do
  for name in #[``compilerProof, ``boolReflection, ``natReflection,
      ``nativeProof, ``decideNativeProof, ``bvProof] do
    checkProof name false

set_option crush.reconstruct.trustBvDecide true in
run_meta do
  checkProof ``bvProof true
  for name in #[``compilerProof, ``boolReflection, ``natReflection,
      ``nativeProof, ``decideNativeProof] do
    checkProof name false

set_option crush.reconstruct.trustNativeDecide true in
run_meta do
  for name in #[``compilerProof, ``boolReflection, ``natReflection,
      ``nativeProof, ``decideNativeProof] do
    checkProof name true
  checkProof ``bvProof false

end SoundnessNativeTrust
