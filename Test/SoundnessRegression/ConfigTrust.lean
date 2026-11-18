import Crush
import Test.SoundnessRegression.NativeTrust

/-!
A direct caller's configuration controls native trust and higher-order fallback
warnings even when ambient options or a supplied snapshot disagree.
-/

open Lean Meta Elab Tactic Crush

namespace SoundnessConfigTrust

private def runWithConfig (name : Name) (cfg : Crush.Config) : MetaM Expr := do
  let fact := mkConst name
  let target ← inferType fact
  let goal ← mkFreshExprMVar target
  let snapshot ← KernelCheckSnapshot.capture
  discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
    runCrush goal.mvarId! cfg
      { terms := #[(fact, "native premise")], allHyps := false,
        allowPremiseSelection := false }
      (snapshot? := some snapshot)
  unless ← goal.mvarId!.isAssigned do throwError "direct configuration call left its goal open"
  instantiateMVars goal

set_option crush.reconstruct.trustNativeDecide true in
set_option crush.reconstruct.trustBvDecide true in
run_meta do
  let proof ← runWithConfig ``SoundnessNativeTrust.nativeProof { trust := .reconstruct }
  let strict := (← KernelCheckSnapshot.capture).withConfig {}
  discard <| kernelCheckProof strict (← inferType proof) proof

-- Explicit opt-ins override disabled ambient options.
run_meta do
  for (name, cfg) in #[
      (``SoundnessNativeTrust.nativeProof,
        { trust := .reconstruct, trustNativeDecide := true : Crush.Config }),
      (``SoundnessNativeTrust.bvProof,
        { trust := .reconstruct, trustBvDecide := true : Crush.Config })] do
    let proof ← runWithConfig name cfg
    unless proof.getUsedConstants.contains name do
      throwError "direct configuration ignored its explicit native opt-in"

/-- warning: crush: `crush.ho.mode native` requires a higher-order capable backend (cvc5); `z3` is first-order only. Falling back to `defunctionalize`. -/
#guard_msgs in
set_option crush.ho.mode "defunctionalize" in
run_meta do
  discard <| runWithConfig ``True.intro
    { backend := .z3, hoMode := .native, trust := .reconstruct }

#guard_msgs in
set_option crush.ho.mode "native" in
run_meta do
  discard <| runWithConfig ``True.intro
    { backend := .z3, hoMode := .defunctionalize, trust := .reconstruct }

#guard_msgs in
run_meta do
  discard <| runWithConfig ``True.intro
    { backend := .cvc5, hoMode := .native, trust := .reconstruct }

end SoundnessConfigTrust

/-! ## `crush.reconstruct "alethe"` is checked only where it is used (review round 3, C6)

Under trust the reconstruct mode is never consulted, and backend `none` runs no
solver; a reconstructing policy still needs cvc5. -/

namespace SoundnessConfigTrustAlethe

set_option crush.reconstruct "alethe" in
example (x : Int) (h : x > 2) : x > 1 := by crush

set_option crush.reconstruct "alethe" in
set_option crush.backend "none" in
set_option crush.trust "reconstruct" in
example (x : Int) (h : x > 2) : x > 1 := by
  crush
  omega

/-- error: crush: `crush.reconstruct alethe` requires the cvc5 backend -/
#guard_msgs(error, substring := true) in
set_option crush.reconstruct "alethe" in
set_option crush.trust "reconstruct" in
example (x : Int) (h : x > 2) : x > 1 := by crush

end SoundnessConfigTrustAlethe
