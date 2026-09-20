import Crush

/-!
Round-trip selected assumptions through translation and a fixed resolution
certificate. This isolates decoding and the checked source bridge from cvc5's
choice of later theory steps.
-/

open Lean Meta Elab Tactic Crush

namespace AletheAssumptions

elab "replay_assumption " source:term : tactic => withMainContext do
  let source ← elabTerm source none
  let goal ← getMainGoal
  let target ← goal.getType
  let cfg : Crush.Config := { trust := .reconstruct, reconstruct := .alethe }
  let ((positive, negative), state) ← TranslateM.run cfg do
    let positive ← emitTerm (← inferType source)
    let negative ← emitTerm (mkApp (mkConst ``Not) target)
    return (positive, negative)
  let certificate := s!"unsat\n(\n\
    (assume crush_fact_0 {positive})\n\
    (assume crush_fact_1 {negative})\n\
    (step done (cl) :rule resolution :premises (crush_fact_0 crush_fact_1)))"
  let some parsed := Alethe.parseProof certificate | throwError "bad test certificate"
  let snapshot ← KernelCheckSnapshot.capture
  let implication ← withLocalDeclD `negated (mkApp (mkConst ``Not) target) fun negated => do
    let facts := ({} : Std.HashMap String Expr)
      |>.insert "crush_fact_0" source
      |>.insert "crush_fact_1" negated
    match ← Alethe.replay parsed (SMT.parseSexps certificate) facts state.nameToExpr with
    | .ok proof => mkLambdaFVars #[negated] proof
    | .error failure => throwError "assumption replay failed: {failure.toMessageData}"
  let proof ← mkAppOptM ``Classical.byContradiction #[some target, some implication]
  goal.assign (← kernelCheckProof snapshot target proof)
  replaceMainGoal []

-- Variable zero divisors, truncated subtraction, and nested Nat quantifiers all
-- need bridges; no source recursive function is unfolded to obtain them.
theorem guardedNaturals (f : Nat → Nat) (n d x : Nat)
    (source : f (n - 1) = n % d + f (n / d) ∧ (∀ j < n, j * j ≤ x) ∧
      ¬∃ j : Nat, j < n ∧ j * j > x) :
    f (n - 1) = n % d + f (n / d) ∧ (∀ j < n, j * j ≤ x) ∧
      ¬∃ j : Nat, j < n ∧ j * j > x := by
  replay_assumption source

-- The two erased type arguments differ, and the inner quantifier uses the
-- element type of an emitted datatype sort. SMT decodes the Prop equality as Iff.
theorem polymorphicExists {α β : Type}
    (p : ∀ γ : Type, List γ → Prop) (r : α → Prop) (ys : List β)
    (source : (∃ xs : List α, p α xs ∧ ∀ x : α, x ∈ xs → r x) = p β ys) :
    (∃ xs : List α, p α xs ∧ ∀ x : α, x ∈ xs → r x) = p β ys := by
  replay_assumption source

-- Replay must retain the exact instance chosen by translation.
private abbrev standardNatPower : HPow Nat Nat Nat := inferInstance

theorem powerInstances (custom : HPow Nat Nat Nat) (n x y : Nat)
    (source : @HPow.hPow Nat Nat Nat standardNatPower 2 n = x ∧
      @HPow.hPow Nat Nat Nat custom 2 n = y) :
    @HPow.hPow Nat Nat Nat standardNatPower 2 n = x ∧
      @HPow.hPow Nat Nat Nat custom 2 n = y := by
  replay_assumption source

-- cvc5 scales this integer inequality by 1/10, then tightens its rational bound
-- back to an integer. Require the complete certificate, without the core fallback.
set_option crush.backend "cvc5" in
set_option crush.trust "reconstruct" in
set_option crush.reconstruct "alethe" in
theorem rationalCoefficients (n : Nat) (h : n = 0) : 0 ≥ n * 10 := by
  crush

/-- info: 'AletheAssumptions.guardedNaturals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guardedNaturals

/-- info: 'AletheAssumptions.polymorphicExists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polymorphicExists

/-- info: 'AletheAssumptions.powerInstances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms powerInstances

/-- info: 'AletheAssumptions.rationalCoefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rationalCoefficients

-- Removing the nonnegativity guard is invalid. An excluded ambient contradiction
-- must not make the forged assertion replayable.
example (_excluded : False) : True := by
  run_tac
    let certificate := "unsat ((assume source (forall ((n Int)) (>= n 0))))"
    let some parsed := Alethe.parseProof certificate | throwError "bad test certificate"
    let facts := ({} : Std.HashMap String Expr).insert "source" (mkConst ``Nat.zero_le)
    match ← Alethe.replay parsed (SMT.parseSexps certificate) facts {} with
    | .error failure =>
      unless failure.kind == .ruleGap do
        throwError "expected a rejected assumption, got {failure.toMessageData}"
    | .ok _ => throwError "unguarded integers were accepted as naturals"
  trivial

end AletheAssumptions
