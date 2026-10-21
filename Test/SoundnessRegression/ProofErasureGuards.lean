import Crush

/-!
Binder-dependent proof arguments carry no symbol identity, but erasing a hypothetical
proof cannot justify an unconditional value of a possibly empty type. Translation
must preserve that guard and expose captured lets even when metadata wraps the term
or its application head.
-/

open Lean Meta Crush

set_option crush.timeout 2

namespace SoundnessProofErasureGuards

-- Check translation directly so premise recovery cannot hide a refusal.
example (h : ∀ n : Nat, (List.replicate (n + 1) (0 : Int))[0]'(by simp) = 0)
    (n : Nat) : (List.replicate (n + 1) (0 : Int))[0]'(by simp) = 0 := by
  crush

private theorem replicateZero (n : Nat) :
    (List.replicate (n + 1) (0 : Int))[0]'(by simp) = 0 := by simp

run_meta do
  let fact ← inferType (mkConst ``replicateZero)
  discard <| TranslateM.run {} <| emitTerm fact

def impossible (n : Int) (h : n ≠ n) : Empty := False.elim (h rfl)

private theorem impossibleNe (n : Int) (h : n ≠ n) :
    impossible n h ≠ impossible n h := (h rfl).elim

-- A hypothetical impossible proof does not witness Empty.
example : True := by
  have h : ∀ n (h : n ≠ n), impossible n h ≠ impossible n h :=
    fun n h => (h rfl).elim
  fail_if_success have : False := by crush
  trivial

/-- error: crush: cannot translate a possibly empty result type after erasing proof arguments: Empty -/
#guard_msgs(error, substring := true) in
run_meta do
  let fact ← inferType (mkConst ``impossibleNe)
  discard <| TranslateM.run {} <| emitTerm fact

-- Wrap both a let term and a let application head in metadata.
run_meta do
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let term := mkMData {} (mkLet `y (mkConst ``Int) x (mkBVar 0))
    let (translated, _) ← TranslateM.run {} do
      TranslateM.withBoundVar x.fvarId! "x" <| emitTerm term
    unless toString translated == "x" do
      throwError "metadata-wrapped let lost its bound variable"

run_meta do
  let arrow ← mkArrow (mkConst ``Int) (mkConst ``Int)
  withLocalDeclD `f arrow fun f => do
    withLocalDeclD `x (mkConst ``Int) fun x => do
      let term := mkApp (mkMData {} (mkLet `g arrow f (mkBVar 0))) x
      let (translated, _) ← TranslateM.run {} do
        TranslateM.withBoundVar x.fvarId! "x" <| emitTerm term
      let (expected, _) ← TranslateM.run {} do
        TranslateM.withBoundVar x.fvarId! "x" <| emitTerm (mkApp f x)
      unless toString translated == toString expected do
        throwError "metadata-wrapped let in application position lost its arguments"

end SoundnessProofErasureGuards
