import Crush

open Lean Meta Crush

/-! Repeated datatype names at distinct type arguments are not recursion cycles.
Nested products containing Nat must retain the guard on their inner fields. -/

run_meta do
  let inner := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat)
  let outer := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Int) inner
  let (guard, _) ← TranslateM.run {} do
    discard <| emitSort outer
    wfCondition outer (.const "value")
  if guard.isNone then
    throwError "nested Nat fields lost their validity guard"

-- This true Lean hypothesis becomes inconsistent over unguarded SMT tuples,
-- whose inner integer fields include negative values.
set_option crush.timeout 2 in
example : True := by
  have h : ∀ p : Int × (Nat × Nat), p.2.1 ≥ 0 := fun p => Nat.zero_le p.2.1
  fail_if_success have : False := by crush [h]
  trivial

-- Ordinary reasoning about actual nested tuples remains available.
example (p : Int × (Nat × Nat)) : p.2.1 ≥ 0 := by crush
