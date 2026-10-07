import Crush

/-! Possibly empty carriers must not create Lean inhabitants. -/
set_option linter.unusedVariables false
set_option crush.timeout 2

example (α : Type) : True := by
  fail_if_success have : ∃ x : α, x = x := by crush
  trivial

structure SoundnessEmptyStruct where
  e : Empty
  n : Int

example : True := by
  have h : ∀ s : SoundnessEmptyStruct, s.n ≠ s.n := fun s => s.e.elim
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : ∀ s : Empty × Int, s.2 ≠ s.2 := fun s => s.1.elim
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : ∀ s : Int → Empty, s ≠ s := fun s => (s 0).elim
  fail_if_success have : False := by crush
  trivial

inductive SoundnessNoBase where
  | mk : SoundnessNoBase → Int → SoundnessNoBase

example : True := by
  have h : ∀ s : SoundnessNoBase, s ≠ s := fun s => by
    induction s with
    | mk t n ih => exact (ih rfl).elim
  fail_if_success have : False := by crush
  trivial

-- Hypothetical binders and constructor fields are not inhabitation evidence.
example : True := by
  fail_if_success have : ∃ x : Empty, x = x := by crush
  fail_if_success have : ∃ x : Option Empty, x ≠ none := by crush
  fail_if_success have : ∃ f : Int → Empty, f = f := by crush
  trivial

-- Padding must retain useful reasoning about actual values.
example (α : Type) (x : α) : ∃ y : α, y = x := by crush
example (x : Option Empty) : x = none := by crush
example (x : Nat) (f : Nat → Nat) : f x ≥ 0 := by crush
example (x : Array Empty) : x.size = 0 := by crush
