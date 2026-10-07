import Crush

set_option linter.unusedVariables false
set_option crush.timeout 2

example (f : Prop → Int)
    (h : ∀ x : Int, f (x > 0) = if x > 0 then 1 else 0) : True := by
  fail_if_success have : False := by crush
  trivial

def SoundnessBoth (p q : Prop) : Prop := p ∧ q

example : True := by
  have h : ∀ x : Int, SoundnessBoth (x > 0) (x > 0) ↔ x > 0 :=
    fun _ => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : ∀ n : Nat, Nonempty (Fin n) ↔ 0 < n := fun n =>
    ⟨fun ⟨i⟩ => Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt, fun hn => ⟨⟨0, hn⟩⟩⟩
  fail_if_success have : False := by crush
  trivial

-- Distinct propositions must be passed as Boolean arguments, not erased.
example (f : Prop → Int) (h : ∀ p, f p = @ite Int p (Classical.propDecidable p) 1 0) :
    f True ≠ f False := by crush

-- A captured let head is refused until it is explicitly zeta-reduced.
example : True := by
  have h : ∀ x : Int, (let y := x; y + 0) = x := fun x => Int.add_zero x
  fail_if_success have : False := by crush
  trivial

example (p : Prop) [Decidable p] (a b : Int) : True := by
  have h : (dite p (fun _ => a) (fun _ => b)) = (if p then a else b) := by
    split <;> simp_all
  fail_if_success have : False := by crush
  trivial
