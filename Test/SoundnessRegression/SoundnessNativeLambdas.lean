import Crush

set_option crush.backend "cvc5"
set_option crush.ho.mode "native"
set_option crush.timeout 2

example : True := by
  fail_if_success have : (fun x : Nat => x) ≠ (fun x : Nat => x - 0) := by crush
  fail_if_success have : (fun x : Nat => (x : Int)) ≠
      (fun x : Nat => ((x : Int).natAbs : Int)) := by crush
  fail_if_success have : (fun p : Nat × Nat => p) ≠
      (fun p : Nat × Nat => (p.1 - 0, p.2)) := by crush
  trivial

example (F : (Nat → Nat) → Int) (h : F (fun x => x) = 2) :
    F (fun x => x - 0) = 2 := by crush
example (F : (Nat × Nat → Nat × Nat) → Int) (h : F (fun p => p) = 2) :
    F (fun p => (p.1 - 0, p.2)) = 2 := by crush
