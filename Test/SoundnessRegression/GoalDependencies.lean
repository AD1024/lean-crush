import Test.SoundnessRegression.AxiomClosure

/-!
Reconstruction diagnoses admissions in the goal before speculative proof search
can swallow the cause. Unrelated admitted declarations in the context do not taint
an otherwise checked goal.
-/

open Lean Meta Crush

namespace SoundnessGoalDependencies

def admittedNat : Nat :=
  (fun _ : SoundnessAxiomClosure.P => 0) SoundnessAxiomClosure.admittedProof

def trustedNat : Nat := False.elim (Crush.crushSorry False)

set_option crush.trust "reconstruct"

/-- error: crush: reconstructed goal type depends on forbidden axiom `sorryAx` through `SoundnessGoalDependencies.admittedNat` -/
#guard_msgs(error, substring := true) in
example : admittedNat + 0 = admittedNat := by crush

/-- error: crush: reconstructed goal type depends on forbidden axiom `Crush.crushSorry` through `SoundnessGoalDependencies.trustedNat` -/
#guard_msgs(error, substring := true) in
example : trustedNat + 0 = trustedNat := by crush

theorem unrelatedAdmission (_unused : Fin admittedNat) : True := by
  crush []

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
