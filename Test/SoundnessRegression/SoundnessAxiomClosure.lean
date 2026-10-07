import Crush

open Lean Meta Elab Tactic
open Crush

namespace SoundnessAxiomClosure

axiom P : Prop
axiom ordinaryProof : P

theorem trustedProof : P := Crush.crushSorry P True.intro
theorem trustedWrapper : P := trustedProof

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem admittedProof : P := by sorry
theorem admittedWrapper : P := admittedProof

private def expectRejection (action : MetaM Unit) : MetaM Unit := do
  let accepted ← try
    action
    pure true
  catch _ => pure false
  if accepted then
    throwError "checked reconstruction accepted an admitted theorem"

-- These declarations all predate the snapshot. A kernel check alone accepts them,
-- so checking only declarations generated after the snapshot misses the admission.
run_meta do
  let snapshot ← KernelCheckSnapshot.capture
  for name in #[``trustedProof, ``trustedWrapper, ``admittedProof, ``admittedWrapper] do
    expectRejection do
      discard <| kernelCheckProof snapshot (mkConst ``P) (mkConst name)
  -- Existing user axioms are allowed and remain visible to Lean's axiom tracking.
  discard <| kernelCheckProof snapshot (mkConst ``P) (mkConst ``ordinaryProof)

-- Closing the local context must include visible let values in the axiom audit.
run_meta do
  let snapshot ← KernelCheckSnapshot.capture
  withLetDecl `h (mkConst ``P) (mkConst ``trustedWrapper) fun h => do
    expectRejection do
      discard <| kernelCheckProof snapshot (mkConst ``P) h

-- A manual finisher cannot hide an admission behind an existing lemma either.
run_meta do
  let goal ← mkFreshExprMVar (mkConst ``P)
  let accepted ← IO.mkRef true
  discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
    accepted.set (← tryReconstruct goal.mvarId! #[] #[]
      (some (← `(tactic| exact trustedWrapper))))
  if ← accepted.get then
    throwError "manual reconstruction accepted a transitively trusted proof"
  if ← goal.mvarId!.isAssigned then
    throwError "rejected reconstruction left the goal assigned"

-- Intentionally ignore Config.filter to exercise the collector's second check.
@[library_suggestions]
meta def taintedSuggestions : LibrarySuggestions.Selector := fun _ _ =>
  return #[
    { name := ``trustedWrapper, score := 3.0 },
    { name := ``admittedWrapper, score := 2.0 },
    { name := ``ordinaryProof, score := 1.0 }
  ]

run_meta do
  let goal ← mkFreshExprMVar (mkConst ``P)
  let result ← collectFactsWithRewrite goal.mvarId! {} false 1
  unless result.selectedPremises == 1 do
    throwError "premise selection failed to retain the ordinary user axiom"
  let proofs := result.facts.filterMap (·.proof)
  unless proofs == #[mkConst ``ordinaryProof] do
    throwError "premise selection retained an admitted theorem or dropped a user axiom"

end SoundnessAxiomClosure
