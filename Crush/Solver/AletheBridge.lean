import Crush.Solver.ReplayAttr

/-!
Checked bridges from Lean source facts to their decoded SMT assumptions.
The guards belong to the Nat-as-Int encoding, including under quantifiers and
uninterpreted applications. Normalize them without unfolding source functions.
-/

namespace Crush.Alethe

open Lean Meta Elab Tactic

private theorem intForallNonneg (p : Int → Prop) :
    (∀ i : Int, i ≥ 0 → p i) ↔ ∀ n : Nat, p n := by
  constructor
  · intro h n
    exact h n (Int.natCast_nonneg n)
  · intro h i hi
    simpa only [Int.toNat_of_nonneg hi] using h i.toNat

private theorem intExistsNonneg (p : Int → Prop) :
    (∃ i : Int, i ≥ 0 ∧ p i) ↔ ∃ n : Nat, p n := by
  constructor
  · rintro ⟨i, hi, hp⟩
    exact ⟨i.toNat, by simpa only [Int.toNat_of_nonneg hi] using hp⟩
  · rintro ⟨n, hp⟩
    exact ⟨n, Int.natCast_nonneg n, hp⟩

private theorem intDivGuard (a b : Int) :
    (if b = 0 then 0 else a / b) = a / b := by
  split <;> simp_all

private theorem intModGuard (a b : Int) :
    (if b = 0 then a else a % b) = a % b := by
  split <;> simp_all

private theorem intSubGuard (a b : Int) :
    (if a ≥ b then a - b else 0) = ((a - b).toNat : Int) := by
  split <;> omega

/-- Replay introduces the target's binders before running a rule. Revert guarded
integer locals so the quantifier equivalences also cover those outer binders. -/
private def revertNonnegativeInts : TacticM Unit := withMainContext do
  let mut variables := #[]
  let hypotheses ← getLocalHyps
  for decl in ← getLCtx do
    unless decl.type.isConstOf ``Int do continue
    let nonnegative ← mkAppM ``LE.le #[Lean.toExpr (0 : Int), decl.toExpr]
    if ← hypotheses.anyM fun hyp => do isDefEqGuarded (← inferType hyp) nonnegative then
      variables := variables.push decl.fvarId
  unless variables.isEmpty do
    let (_, goal) ← (← getMainGoal).revert variables
    replaceMainGoal [goal]

register_crush_replay rule low <<
  (assume ..) => by
    -- SMT Boolean equality decodes as Iff. This direct bridge avoids using
    -- source equalities as contextual simplification rules under quantifiers.
    simp only [eq_iff_iff] at *
    assumption
>>

register_crush_replay rule low <<
  (assume ..) => by
    run_tac revertNonnegativeInts
    simp_all (failIfUnchanged := false) only
      [eq_iff_iff, intForallNonneg, intExistsNonneg, intDivGuard, intModGuard, intSubGuard]
    simp_all (failIfUnchanged := false) only
      [Int.ofNat_eq_coe, ← Nat.ToInt.natCast_ofNat, Int.toNat_sub,
       ← Int.natCast_add, ← Int.natCast_mul, ← Int.natCast_ediv, ← Int.natCast_emod,
       Int.toNat_natCast, Int.ofNat_lt, Int.ofNat_le, Int.ofNat_inj]
    <;> grind (ematch := 0) only
>>

end Crush.Alethe
