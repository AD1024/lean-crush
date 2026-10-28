import Test.SoundnessRegression.AxiomClosure

/-!
Reconstruction diagnoses admissions in the goal and in used hypotheses, even when
speculative proof search restores its state. Trusted fallback reports the rejected
dependency. Unrelated admitted declarations do not taint a successful checked proof.
-/

open Lean Meta Elab Tactic Crush

namespace SoundnessGoalDependencies

def admittedNat : Nat :=
  (fun _ : SoundnessAxiomClosure.P => 0) SoundnessAxiomClosure.admittedProof

def trustedNat : Nat := False.elim (Crush.crushSorry False)

set_option crush.trust "reconstruct"
set_option crush.timeout 3

/-- error: crush: reconstructed goal type depends on forbidden axiom `sorryAx` through `SoundnessGoalDependencies.admittedNat` -/
#guard_msgs(error, substring := true) in
example : admittedNat + 0 = admittedNat := by crush

/-- error: crush: reconstructed goal type depends on forbidden axiom `Crush.crushSorry` through `SoundnessGoalDependencies.trustedNat` -/
#guard_msgs(error, substring := true) in
example : trustedNat + 0 = trustedNat := by crush

-- The target itself is clean; the admitted definition occurs only in the facts
-- needed to relate x to three. The terminal error must retain the rejected proof's
-- dependency diagnostic instead of merely reporting failed proof search.
/-- error: crush: solver reported `unsat`, but checked reconstruction rejected a proof: reconstructed goal type depends on forbidden axiom `sorryAx` through `SoundnessGoalDependencies.admittedNat` -/
#guard_msgs(error, substring := true) in
example (x : Nat) (h : admittedNat = 3) (hx : x = admittedNat) : x = 3 := by
  crush [h, hx]

/-- error: crush: solver reported `unsat`, but checked reconstruction rejected a proof: reconstructed goal type depends on forbidden axiom `Crush.crushSorry` through `SoundnessGoalDependencies.trustedNat` -/
#guard_msgs(error, substring := true) in
example (h : trustedNat ≠ trustedNat) : False := by crush [h]

set_option crush.trust "reconstructOrTrust" in
/-- warning: crush: solver reported `unsat`, but checked reconstruction rejected a proof: reconstructed goal type depends on forbidden axiom `sorryAx` through `SoundnessGoalDependencies.admittedNat` -/
#guard_msgs(warning, substring := true) in
theorem fallbackHypothesis (x : Nat) (h : admittedNat = 0) (hx : x = admittedNat) :
    x = 0 := by crush [h, hx]

-- A trusted termination argument becomes part of the definition's axiom closure.
-- A trivial theorem mentioning that definition is still subject to strict policy.
set_option crush.trust "trust" in
def halve (n : Nat) : Nat :=
  if n < 2 then n else halve (n / 2)
termination_by n
decreasing_by crush

/-- error: crush: reconstructed goal type depends on forbidden axiom `Crush.crushSorry` through `SoundnessGoalDependencies.halve` -/
#guard_msgs(error, substring := true) in
example (n : Nat) : halve n + 0 = halve n := by crush

set_option crush.trust "reconstructOrTrust" in
/-- warning: crush: solver reported `unsat`, but checked reconstruction rejected a proof: reconstructed goal type depends on forbidden axiom `Crush.crushSorry` through `SoundnessGoalDependencies.halve` -/
#guard_msgs(warning, substring := true) in
theorem fallbackHalve (n : Nat) : halve n + 0 = halve n := by crush

run_meta do
  unless (← collectAxioms ``halve).contains ``Crush.crushSorry do
    throwError "termination fixture did not use trusted discharge"
  let axioms ← collectAxioms ``fallbackHypothesis
  unless axioms.contains ``sorryAx && axioms.contains ``Crush.crushSorry do
    throwError "trusted fallback lost the original admission or trust axiom"
  unless (← collectAxioms ``fallbackHalve).contains ``Crush.crushSorry do
    throwError "recursive-definition fallback lost its trust dependency"

theorem unrelatedAdmission (_unused : Fin admittedNat) : True := by
  crush []

theorem omittedAdmission (x : Nat) (h : x = 0) (_unused : Fin admittedNat) : x = 0 := by
  crush [h]

-- An irrelevant selected fact may also be absent from the solver's core. A
-- successful proof must not be rejected just because an earlier attempt failed.
theorem unusedSelectedAdmission (x : Nat) (h : x = 0)
    (_unused : admittedNat = admittedNat) : x + 1 = 1 := by
  crush

/-- error: crush: solver reported `unsat`, but checked reconstruction rejected a proof: reconstructed goal type depends on forbidden axiom `sorryAx` through `SoundnessGoalDependencies.admittedNat` -/
#guard_msgs(error, substring := true) in
example (x : Nat) (h : x = admittedNat) : x = 0 := by
  let n := admittedNat
  let m := n
  have hx : x = m := h
  have hm : m = 0 := rfl
  crush [hx, hm]

-- Exercise the same manual-finisher path as `using`: its admitted global is not
-- among the supplied core facts. Keep the diagnostic through restoration, then
-- allow a later finisher using an ordinary user axiom to succeed.
run_meta do
  let snapshot ← KernelCheckSnapshot.capture
  let target := mkConst ``SoundnessAxiomClosure.P
  let goal ← mkFreshExprMVar target
  let accepted ← IO.mkRef false
  discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
    let manual ← `(tactic| exact SoundnessAxiomClosure.admittedWrapper)
    let checked ← `(tactic| exact SoundnessAxiomClosure.ordinaryProof)
    accepted.set (← tryReconstruct goal.mvarId! #[] #[checked]
      (some manual) (some snapshot))
  unless ← accepted.get do
    throwError "an earlier admitted candidate prevented a later checked proof"
  let some diagnostic ← snapshot.axiomFailure?
    | throwError "manual finisher's rejection diagnostic was lost"
  unless (← diagnostic.toString).contains
      "forbidden axiom `sorryAx` through `SoundnessAxiomClosure.admittedWrapper`" do
    throwError "manual finisher rejection reported the wrong dependency: {diagnostic}"
  discard <| kernelCheckProof snapshot target (← instantiateMVars goal)

run_meta do
  withLetDecl `n (mkConst ``Nat) (mkConst ``trustedNat) fun n => do
    let failed ← try
      checkReconstructionGoalAxioms (← mkEq n n)
      pure false
    catch ex =>
      unless (← ex.toMessageData.toString).contains
          "forbidden axiom `Crush.crushSorry` through `SoundnessGoalDependencies.trustedNat`" do
        throw ex
      pure true
    unless failed do throwError "goal auditing omitted a visible let dependency"

end SoundnessGoalDependencies
