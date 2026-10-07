import Crush

set_option linter.unusedVariables false

example : True := by
  have h : ∀ x : Int, (if _h : x > 0 then x else -x) ≥ 0 := by
    intro x
    split <;> omega
  fail_if_success have : False := by crush
  trivial

example (p : Prop) [Decidable p] (h : p) (a b : Int) :
    (dite p (fun _ => a) (fun _ => b)) = a := by crush

example (p : Prop) [Decidable p] (h : ¬p) (a b : Int) :
    (dite p (fun _ => a) (fun _ => b)) = b := by crush

example (x : Int) (h : x > 0) :
    (if _h : x > 0 then x + 1 else x - 1) > x := by crush
