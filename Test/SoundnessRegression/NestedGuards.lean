import Crush

/-!
Repeated datatype names at distinct type arguments are not recursion cycles.
Nested products must retain validity guards on inner Nat fields so SMT's negative
integer values cannot contradict true Lean hypotheses.
-/

open Lean Meta Crush

run_meta do
  let inner := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat)
  let outer := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Int) inner
  let (guard, _) ← TranslateM.run {} do
    discard <| emitSort outer
    wfCondition outer (.const "value")
  if guard.isNone then
    throwError "nested Nat fields lost their validity guard"

-- Unguarded inner integers would make this true Lean hypothesis inconsistent.
set_option crush.timeout 2 in
example : True := by
  have h : ∀ p : Int × (Nat × Nat), p.2.1 ≥ 0 := fun p => Nat.zero_le p.2.1
  fail_if_success have : False := by crush [h]
  trivial

example (p : Int × (Nat × Nat)) : p.2.1 ≥ 0 := by crush
