import Crush

set_option linter.unusedVariables false

example (inst : NatCast Int) (h : @Nat.cast Int inst 1 = 2) : True := by
  fail_if_success have : False := by crush
  trivial

example (inst : NatCast Nat) (h : @Nat.cast Nat inst 1 = 2) : True := by
  fail_if_success have : False := by crush
  trivial

example (n : Nat) : (Nat.cast n : Int) ≥ 0 := by crush
example (n : Nat) (h : n = 2) : (Nat.cast n : Int) = 2 := by crush
