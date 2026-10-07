import Crush

open Lean Elab Term Meta in
elab "#check_standard_instance " index:num term:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let expression ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    lambdaTelescope expression fun _ body => do
      unless ← Crush.hasExpectedOverloadInstance body index.getNat do
        throwError "standard operator instance was rejected: {body}"

-- Keep the existing structural repertoire when replacing instance synthesis.
#check_standard_instance 3 (fun (a b : Nat) => a + b)
#check_standard_instance 3 (fun (a b : Nat) => a - b)
#check_standard_instance 3 (fun (a b : Nat) => a * b)
#check_standard_instance 3 (fun (a b : Nat) => a / b)
#check_standard_instance 3 (fun (a b : Nat) => a % b)
#check_standard_instance 1 (fun (a b : Nat) => a ≤ b)
#check_standard_instance 1 (fun (a b : Nat) => a < b)
#check_standard_instance 1 (fun (a b : Nat) => a ≥ b)
#check_standard_instance 1 (fun (a b : Nat) => a > b)
#check_standard_instance 1 (fun (a b : Nat) => min a b)
#check_standard_instance 1 (fun (a b : Nat) => max a b)
#check_standard_instance 3 (fun (a b : Int) => a + b)
#check_standard_instance 3 (fun (a b : Int) => a - b)
#check_standard_instance 3 (fun (a b : Int) => a * b)
#check_standard_instance 3 (fun (a b : Int) => a / b)
#check_standard_instance 3 (fun (a b : Int) => a % b)
#check_standard_instance 1 (fun (a : Int) => -a)
#check_standard_instance 1 (fun (a b : Int) => a ≤ b)
#check_standard_instance 1 (fun (a b : Int) => a < b)
#check_standard_instance 1 (fun (a b : Int) => a ≥ b)
#check_standard_instance 1 (fun (a b : Int) => a > b)
#check_standard_instance 1 (fun (a b : Int) => min a b)
#check_standard_instance 1 (fun (a b : Int) => max a b)
#check_standard_instance 3 (fun (a b : BitVec 8) => a + b)
#check_standard_instance 3 (fun (a b : BitVec 8) => a - b)
#check_standard_instance 3 (fun (a b : BitVec 8) => a * b)
#check_standard_instance 3 (fun (a b : BitVec 8) => a / b)
#check_standard_instance 3 (fun (a b : BitVec 8) => a % b)
#check_standard_instance 3 (fun (a b : BitVec 8) => a &&& b)
#check_standard_instance 3 (fun (a b : BitVec 8) => a ||| b)
#check_standard_instance 3 (fun (a b : BitVec 8) => a ^^^ b)
#check_standard_instance 1 (fun (a : BitVec 8) => ~~~a)
#check_standard_instance 1 (fun (a : BitVec 8) => -a)
#check_standard_instance 1 (fun (a b : BitVec 8) => a ≤ b)
#check_standard_instance 1 (fun (a b : BitVec 8) => a < b)
#check_standard_instance 1 (fun (a b : BitVec 8) => a ≥ b)
#check_standard_instance 1 (fun (a b : BitVec 8) => a > b)
#check_standard_instance 3 (fun (a : BitVec 8) (b : Nat) => a <<< b)
#check_standard_instance 3 (fun (a : BitVec 8) (b : Nat) => a >>> b)
#check_standard_instance 3 (fun (a : BitVec 8) (b : BitVec 16) => a <<< b)
#check_standard_instance 3 (fun (a : BitVec 8) (b : BitVec 16) => a >>> b)
#check_standard_instance 3 (fun (a : BitVec 8) (b : BitVec 16) => a ++ b)
#check_standard_instance 3 (fun (a b : String) => a ++ b)

-- Aliases of canonical dictionaries remain accepted.
abbrev standardIntAdd : Add Int := Int.instAdd
#check_standard_instance 3
  (fun (a b : Int) => @HAdd.hAdd Int Int Int (@instHAdd Int standardIntAdd) a b)

set_option crush.timeout 2

-- These are global high-priority instances: disabling local instances during
-- synthesis does not keep any of them from becoming the synthesized baseline.
namespace NonstandardGlobalIntAdd
instance (priority := high) : Add Int := ⟨fun _ _ => 99⟩
example : True := by
  have h : ∀ a b : Int, a + b = 99 := fun _ _ => rfl
  fail_if_success have : False := by crush
  trivial
end NonstandardGlobalIntAdd

namespace NonstandardGlobalNatAdd
instance (priority := high) : Add Nat := ⟨fun _ _ => 99⟩
example : True := by
  have h : ∀ a b : Nat, a + b = 99 := fun _ _ => rfl
  fail_if_success have : False := by crush
  trivial
end NonstandardGlobalNatAdd

namespace NonstandardGlobalBitVecAdd
instance (priority := high) : Add (BitVec 8) := ⟨fun _ _ => 99#8⟩
example : True := by
  have h : ∀ a b : BitVec 8, a + b = 99#8 := fun _ _ => rfl
  fail_if_success have : False := by crush
  trivial
end NonstandardGlobalBitVecAdd

namespace NonstandardGlobalNeg
instance (priority := high) : Neg Int := ⟨fun _ => 99⟩
example : True := by
  have h : ∀ a : Int, -a = 99 := fun _ => rfl
  fail_if_success have : False := by crush
  trivial
end NonstandardGlobalNeg

namespace NonstandardGlobalLE
instance (priority := high) : LE Int := ⟨fun _ _ => True⟩
example : True := by
  have h : ∀ a b : Int, a ≤ b := fun _ _ => True.intro
  fail_if_success have : False := by crush
  trivial
end NonstandardGlobalLE

namespace NonstandardGlobalMax
instance (priority := high) : Max Int := ⟨fun _ _ => 99⟩
example : True := by
  have h : ∀ a b : Int, max a b = 99 := fun _ _ => rfl
  fail_if_success have : False := by crush
  trivial
end NonstandardGlobalMax

namespace NonstandardGlobalShift
instance (priority := high) : HShiftLeft (BitVec 8) Nat (BitVec 8) := ⟨fun _ _ => 99#8⟩
example : True := by
  have h : ∀ a : BitVec 8, a <<< (0 : Nat) = 99#8 := fun _ => rfl
  fail_if_success have : False := by crush
  trivial
end NonstandardGlobalShift
