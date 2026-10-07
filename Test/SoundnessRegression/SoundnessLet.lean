import Crush

set_option linter.unusedVariables false

example : True := by
  have h : ∀ x : Int, (let y := x; y + 0) = x := fun x => Int.add_zero x
  fail_if_success have : False := by crush
  trivial

example (f : Int → Int) (h : ∀ x : Int, (let y := x; f y) = x + 1) : f 2 = 3 := by
  crush

example (f : Int → Int) (h : ∀ x : Int, (let g := f; g) x = x + 1) : f 2 = 3 := by
  crush
