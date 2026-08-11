import Crush

/-!
An indexed pair shape used by Loom's weakest-precondition generator.

Ordinary structures and `Prod` are handled by Crush. This structure also checks
that constructor equality is normalized when a value parameter is omitted by a
reducible constructor abbreviation.
-/

open Crush

universe u

structure MProdWithNames (α β : Type u) (αName : Lean.Name := default) where
  fst : α
  snd : β

abbrev MProdWithNames.mk' {α β : Type u} (a : α) (b : β)
    (αName : Lean.Name := default) : MProdWithNames α β αName :=
  @MProdWithNames.mk _ _ αName a b

theorem mprodInjectiveLean (n sum i sum' : Nat)
    (hstate : MProdWithNames.mk' n sum = MProdWithNames.mk' i sum') :
    sum = sum' := by
  cases hstate
  rfl

theorem mprodInjectiveCrush (n sum i sum' : Nat)
    (hstate : MProdWithNames.mk' n sum = MProdWithNames.mk' i sum') :
    sum = sum' := by
  crush

/-!
Supplying the generated injectivity theorem remains supported, although
constructor preprocessing now discovers it automatically.
-/

theorem mprodInjectiveHintCrush (n sum i sum' : Nat)
    (hstate : MProdWithNames.mk' n sum = MProdWithNames.mk' i sum') :
    sum = sum' := by
  crush [MProdWithNames.mk.injEq, *]
