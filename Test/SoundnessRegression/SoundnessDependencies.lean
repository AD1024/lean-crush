import Crush

open Lean Meta Elab Tactic

namespace SoundnessDependencies

set_option crush.trust "trust"
set_option linter.defProp false

-- Trusted discharge must retain proof dependencies even when SMT only sees their types.
axiom badEquality : (0 : Int) = 1

theorem retainsAxiom : False := by crush [badEquality]

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem retainsInlineSorry : False := by crush [(sorry : (0 : Int) = 1)]

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem sorryEquality : (0 : Int) = 1 := by sorry

theorem retainsNamedSorry : False := by crush [sorryEquality]

theorem retainsLocalSorry : False := by
  have h : (0 : Int) = 1 := sorryEquality
  crush

unsafe def unsafeBot : False := unsafeBot

/-- error: (kernel) invalid declaration, it uses unsafe declaration -/
#guard_msgs(error, substring := true) in
theorem rejectsUnsafeHint : False := by crush [unsafeBot]

/-- error: fail to show termination -/
#guard_msgs(error, substring := true) in
theorem recursiveBad (n : Nat) : n + 1 = n := by
  exfalso
  crush [recursiveBad 0]

-- This nonlinear contradiction exceeds the checked finishers, forcing the fallback.
axiom irrationalSquare (x : Int) : x * x = 2

set_option crush.trust "reconstructOrTrust" in
/-- warning: crush: solver reported `unsat`, but no finishing tactic could replay it -/
#guard_msgs(warning, substring := true) in
theorem fallbackRetainsAxiom (x : Int) : False := by crush [irrationalSquare x]

run_meta do
  for name in #[``retainsAxiom, ``fallbackRetainsAxiom] do
    let axioms ← collectAxioms name
    unless axioms.contains ``Crush.crushSorry do
      throwError "expected trusted discharge for {name}"
  unless (← collectAxioms ``retainsAxiom).contains ``badEquality do
    throwError "trusted discharge dropped its explicit axiom hint"
  unless (← collectAxioms ``fallbackRetainsAxiom).contains ``irrationalSquare do
    throwError "trusted fallback dropped its explicit axiom hint"
  for name in #[``retainsInlineSorry, ``retainsNamedSorry, ``retainsLocalSorry] do
    unless (← collectAxioms name).contains ``sorryAx do
      throwError "trusted discharge hid a sorry dependency in {name}"

-- Library selection must leave the same audit trail as an explicit hint.
axiom selectedContradiction : ∀ (x : Int), x = x + 1

@[library_suggestions]
meta def selectContradiction : Lean.LibrarySuggestions.Selector := fun _ _ =>
  return #[{ name := ``selectedContradiction, score := 1.0 }]

set_option crush.premises true in
theorem retainsSelectedPremise : (0 : Int) = 1 := by crush

run_meta do
  let axioms ← collectAxioms ``retainsSelectedPremise
  unless axioms.contains ``Crush.crushSorry do
    throwError "selected-premise test did not reach trusted discharge"
  unless axioms.contains ``selectedContradiction do
    throwError "trusted discharge dropped its selected library premise"

end SoundnessDependencies
