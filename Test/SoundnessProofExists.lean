import Crush

set_option linter.unusedVariables false

example : True := by
  fail_if_success have : ∃ _ : (0 : Int) > 1, True := by crush
  fail_if_success have : ∃ _ : False, True := by crush
  trivial

example (p q : Prop) : (∃ _ : p, q) ↔ p ∧ q := by crush
example (p : Prop) (h : p) : ∃ _ : p, True := by crush
example (p : Prop) (h : ¬p) (h' : ∃ _ : p, True) : False := by crush
