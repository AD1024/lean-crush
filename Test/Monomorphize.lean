import Crush

/-!
Tests for datatype monomorphization: a fully-applied parametric type becomes a real
SMT datatype at that instantiation, with injective, distinct, exhaustive
constructors and working selectors.

Covers the cases beyond the basic `Test/Regression.lean` promotions: distinct
instantiations must not conflate, nesting must work, and a `Nat` reached *through* a
type parameter must still pick up the non-negativity guard (else the freely-generated
SMT datatype is unsound in the dangerous direction).
-/

open Crush

set_option crush.trust "trust"

/-! ## Distinct instantiations get distinct sorts

`Option Int` and `Option Bool` are different SMT datatypes; a fact about one says
nothing about the other, and neither goal below may leak into the other. -/

theorem option_int_inj (x y : Int) (h : Option.some x = Option.some y) : x = y := by
  crush

theorem option_bool_inj (x y : Bool) (h : Option.some x = Option.some y) : x = y := by
  crush

-- Both instantiations coexist in one query without collision.
theorem two_instantiations (a b : Int) (p q : Bool)
    (h1 : Option.some a = Option.some b) (h2 : Option.some p = Option.some q) :
    a = b ∧ p = q := by crush

/-! ## Nesting: `Option (Option Int)` is monomorphized structurally. -/

theorem nested_option (x y : Int)
    (h : Option.some (Option.some x) = Option.some (Option.some y)) : x = y := by
  crush

theorem nested_distinct (x : Int) :
    Option.some (Option.some x) ≠ Option.some Option.none := by crush

/-! ## `Prod` selectors and η at a mixed instantiation. -/

theorem prod_mixed_fst (a : Int) (b : Bool) : (a, b).1 = a := by crush
theorem prod_mixed_snd (a : Int) (b : Bool) : (a, b).2 = b := by crush
theorem prod_eta_mixed (x : Int × Bool) : x = (x.1, x.2) := by crush

/-! ## A `Nat` reached through a type parameter keeps its `≥ 0` guard

`Option Nat` freely generated over `Int` (the `Nat` encoding) would contain
`some (-1)`, a phantom with no Lean counterpart. If the guard did not compose through
the parameter, the *true* hypothesis below would become unsatisfiable and `False`
would follow. It must be **rejected** (the goal `False` is not provable). -/

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_option_nat_field (h : ∀ o : Option Nat, ∀ n, o = some n → n ≥ 0) :
    False := by crush

-- And the positive direction: a genuine `Nat` fact through `Option` still goes
-- through, i.e. the guard is not so strong that it blocks provable goals.
theorem option_nat_congr (m n : Nat) (h : m = n) :
    Option.some m = Option.some n := by crush

/-! ## `List Int` recursion: distinctness and structural facts. -/

theorem list_nil_cons (a : Int) (as : List Int) : (a :: as) ≠ [] := by crush
