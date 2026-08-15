import Crush

/-!
Well-formedness predicates for refined recursive datatypes must be SMT recursive
definitions, not quantified equations. The latter make Z3 return `unknown` even when the
user proposition itself is an unconstrained, satisfiable atom.
-/

structure RefinedValue where
  value : Nat

opaque accepts : Array RefinedValue → Prop

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example : accepts #[] := by crush
