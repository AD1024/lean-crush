import Crush

set_option linter.unusedVariables false
set_option crush.backend "cvc5"
set_option crush.ho.mode "native"
set_option crush.timeout 2

example (g : Int → Int) (hg : g 0 = -1) (hg2 : (fun x => g x) = g)
    (h : ∀ f : Nat → Nat, f 0 ≥ 0) : True := by
  fail_if_success have : False := by crush
  trivial

example : True := by
  fail_if_success have : ∃ f : Nat → Nat, f 0 < 0 := by crush
  fail_if_success have : ∃ f : Int → Empty, f = f := by crush
  trivial

example (F : (Nat → Nat) → Int) (h : ∀ f, F f = 2) (g : Nat → Nat) :
    F g = 2 := by crush
example (f : Nat → Nat) (n : Nat) : f n ≥ 0 := by crush
