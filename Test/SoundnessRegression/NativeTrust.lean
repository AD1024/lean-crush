import Crush.Solver.Reconstruct
import Lean.Meta.Native

/-!
General native reflection and bit-vector certificate checking have separate trust
policies, including for proofs predating the snapshot. A bv_decide provenance tag
alone cannot authorize arbitrary Boolean evaluation. Explicit configurations replace
the native policy without changing the snapshot's declaration boundary.
-/

open Lean Meta Elab Tactic
open Crush

namespace SoundnessNativeTrust

set_option linter.deprecated false

theorem compilerProof : True := Lean.trustCompiler
theorem boolReflection (a b : Bool) (h : Lean.reduceBool a = b) : a = b :=
  Lean.ofReduceBool a b h
theorem natReflection (a b : Nat) (h : Lean.reduceNat a = b) : a = b :=
  Lean.ofReduceNat a b h
theorem nativeProof : 1 + 1 = 2 := by native_decide
theorem decideNativeProof : 1 + 1 = 2 := by decide +native

-- Tag an arbitrary true assertion as bv_decide.
elab "native_bool_for_policy_test" : tactic => do
  let goal ← getMainGoal
  let .success proof ← nativeEqTrue `bv_decide (mkConst ``Bool.true)
    | throwError "native Boolean evaluation unexpectedly failed"
  goal.assign proof
  replaceMainGoal []

theorem bvTaggedTrue : Bool.true = Bool.true := by native_bool_for_policy_test

theorem bvProof (a b : BitVec 8) :
    (a &&& b) + (a ^^^ b) = a ||| b := by bv_decide

theorem bvLiteralProof (a : BitVec 8) :
    (a &&& 15) + (a ^^^ 15) = a ||| 15 := by bv_decide

private def checkProof (name : Name) (expectedAcceptance : Bool)
    (snapshot? : Option KernelCheckSnapshot := none) : MetaM Unit := do
  let snapshot ← snapshot?.getDM KernelCheckSnapshot.capture
  let proof := mkConst name
  let accepted ← try
    discard <| kernelCheckProof snapshot (← inferType proof) proof
    pure true
  catch ex =>
    if expectedAcceptance then throw ex else pure false
  unless accepted == expectedAcceptance do
    throwError "unexpected native trust result for `{name}`: accepted={accepted}"

run_meta do
  for name in #[``compilerProof, ``boolReflection, ``natReflection,
      ``nativeProof, ``decideNativeProof, ``bvProof, ``bvLiteralProof, ``bvTaggedTrue] do
    checkProof name false

set_option crush.reconstruct.trustBvDecide true in
run_meta do
  checkProof ``bvProof true
  checkProof ``bvLiteralProof true
  for name in #[``compilerProof, ``boolReflection, ``natReflection,
      ``nativeProof, ``decideNativeProof, ``bvTaggedTrue] do
    checkProof name false

set_option crush.reconstruct.trustNativeDecide true in
run_meta do
  for name in #[``compilerProof, ``boolReflection, ``natReflection,
      ``nativeProof, ``decideNativeProof] do
    checkProof name true
  checkProof ``bvProof false
  checkProof ``bvLiteralProof false
  checkProof ``bvTaggedTrue false

-- Override captured policies in both directions.
set_option crush.reconstruct.trustBvDecide true in
set_option crush.reconstruct.trustNativeDecide true in
run_meta do
  let snapshot := (← KernelCheckSnapshot.capture).withConfig {}
  checkProof ``bvProof false snapshot
  checkProof ``nativeProof false snapshot

run_meta do
  let snapshot := (← KernelCheckSnapshot.capture).withConfig
    { trustBvDecide := true, trustNativeDecide := true }
  checkProof ``bvProof true snapshot
  checkProof ``nativeProof true snapshot

end SoundnessNativeTrust
