import Lean.Elab.Tactic.Omega.Frontend
import Crush.Solver.Alethe.Term

/-!
# Arithmetic replay rules

Built-in `register_crush_replay` handlers for integer and rational arithmetic,
including linear certificates, polynomial normalization, and absolute values.
The supporting lemmas and witness checkers produce Lean proofs for each step.
-/

open Lean Meta Elab Tactic Omega
open Lean.Elab.Tactic.Omega

namespace Crush.Alethe

open Crush SMT

private def rationalTarget : ReplayConditionHandler := fun ctx =>
  return (ctx.target.find? (·.isConstOf ``Rat)).isSome

register_crush_replay rule low <<
  (evaluate ..) if rationalTarget => by decide +kernel
>>

register_crush_replay rule low <<
  (poly_simp_rel ..) if rationalTarget => by
    simp_all (failIfUnchanged := false) only
      [← Rat.intCast_le_intCast, ← Rat.intCast_lt_intCast]
    <;> grind
>>

register_crush_replay rule low <<
  (rare_rewrite "arith-int-geq-tighten"
    (term value : Int) (term bound : Rat) (term limit : Int)) => by
    have rounded : bound.ceil = limit := by decide +kernel
    simpa only [rounded] using (Rat.ceil_le_iff (x := bound) (y := value)).symm
>>

private structure RationalCoefficient where
  numerator : Int
  denominator : Nat

private def parseCoefficient (value : Sexp) : Option RationalCoefficient := do
  let .atom source := value | none
  let fraction := source.splitOn "/"
  if fraction.length == 2 then
    let numerator ← fraction[0]!.toInt?
    let denominator ← fraction[1]!.toNat?
    if denominator == 0 then none else some { numerator, denominator }
  else if fraction.length == 1 then
    let decimal := source.splitOn "."
    if decimal.length == 1 then
      let numerator ← source.toInt?
      some { numerator, denominator := 1 }
    else if decimal.length == 2 then
      let whole := decimal[0]!
      let digits := decimal[1]!
      if digits.isEmpty || !digits.all Char.isDigit then none
      let sign := if whole.startsWith "-" then -1 else 1
      let magnitude := if whole.startsWith "-" || whole.startsWith "+" then
          (whole.drop 1).toString
        else whole
      if magnitude.isEmpty || !magnitude.all Char.isDigit then none
      let numerator ← (magnitude ++ digits).toInt?
      some {
        numerator := sign * numerator
        denominator := 10 ^ digits.length
      }
    else none
  else none

private def integerMultipliers (args : Array Sexp) : Option (Array Int) := do
  let coefficients ← args.mapM parseCoefficient
  let common := coefficients.foldl
    (fun denominator coefficient => Nat.lcm denominator coefficient.denominator) 1
  return coefficients.map fun coefficient =>
    coefficient.numerator * Int.ofNat (common / coefficient.denominator)

private partial def clauseNegations (proof : Expr) : MetaM (Option (Array Expr)) := do
  let type ← whnfR (← inferType proof)
  let .app (.const ``Not _) clause := type | return none
  let clause ← whnfR clause
  if clause.isAppOfArity ``Or 2 then
    let pair ← mkAppM ``Lean.Omega.and_not_not_of_not_or #[proof]
    let left ← mkAppM ``And.left #[pair]
    let right ← mkAppM ``And.right #[pair]
    let some tail ← clauseNegations right | return none
    return some (#[left] ++ tail)
  return some #[proof]

private structure LinearWitnessFact where
  fact : Fact
  proof : Lean.Elab.Tactic.Omega.Proof

private def equalityFact (index : Nat) (expression proof : Expr) :
    OmegaM LinearWitnessFact := do
  let (combo, evaluation, _) ← asLinearCombo expression
  let groundProof : Lean.Elab.Tactic.Omega.Proof := do
    mkEqTrans (← mkEqSymm (← evaluation)) proof
  let constraint : Constraint := .exact (-combo.const)
  return {
    fact := {
      coeffs := combo.coeffs
      constraint
      justification := .assumption constraint combo.coeffs index
    }
    proof := Problem.addEquality_proof combo.const combo.coeffs groundProof
  }

private def inequalityFact (index : Nat) (expression proof : Expr) :
    OmegaM LinearWitnessFact := do
  let (combo, evaluation, _) ← asLinearCombo expression
  let groundProof : Lean.Elab.Tactic.Omega.Proof := do
    mkAppM ``le_of_le_of_eq #[proof, ← evaluation]
  let constraint : Constraint := {
    lowerBound := some (-combo.const)
    upperBound := none
  }
  return {
    fact := {
      coeffs := combo.coeffs
      constraint
      justification := .assumption constraint combo.coeffs index
    }
    proof := Problem.addInequality_proof combo.const combo.coeffs groundProof
  }

private def normalizeRelation (index : Nat) (proof : Expr) :
    OmegaM (Option LinearWitnessFact) := do
  let type ← whnfR (← inferType proof)
  match_expr type with
  | Eq type left right =>
    unless type.isConstOf ``Int do return none
    let difference ← mkAppM ``HSub.hSub #[left, right]
    let normalized := mkApp3 (mkConst ``Int.sub_eq_zero_of_eq) left right proof
    return some (← equalityFact index difference normalized)
  | LE.le type _ left right =>
    unless type.isConstOf ``Int do return none
    let difference ← mkAppM ``HSub.hSub #[right, left]
    let normalized := mkApp3 (mkConst ``Int.sub_nonneg_of_le) right left proof
    return some (← inequalityFact index difference normalized)
  | LT.lt type _ left right =>
    unless type.isConstOf ``Int do return none
    let lower ← mkAppM ``HAdd.hAdd #[left, Lean.toExpr (1 : Int)]
    let difference ← mkAppM ``HSub.hSub #[right, lower]
    let strengthened := mkApp3 (mkConst ``Int.add_one_le_of_lt) left right proof
    let normalized := mkApp3 (mkConst ``Int.sub_nonneg_of_le) right lower strengthened
    return some (← inequalityFact index difference normalized)
  | _ => return none

private def scaledMultiplier (coefficient : Int) (fact : Fact) : Int :=
  if fact.constraint.isExact then coefficient else coefficient.natAbs

private def scaleFact (coefficient : Int) (fact : Fact) : Fact :=
  Fact.combo coefficient fact 0 fact

private def checkLinearWitness (coefficients : Array Int) (goal : MVarId) :
    TacticM Bool := goal.withContext do
  let some falseGoal ← goal.falseOrByContra (some true)
    | trace[crush.replay] "la_generic witness declined: could not negate the clause"
      return false
  falseGoal.withContext do
    let hypotheses ← getLocalHyps
    let some contradiction := hypotheses.back?
      | trace[crush.replay] "la_generic witness declined: no negated clause hypothesis"
        return false
    let some negations ← clauseNegations contradiction
      | trace[crush.replay] "la_generic witness declined: clause shape is unsupported"
        return false
    unless negations.size == coefficients.size && !negations.isEmpty do
      trace[crush.replay] "la_generic witness declined: {negations.size} literals, \
        {coefficients.size} coefficients"
      return false
    let proof? ← OmegaM.run (do
      let mut facts : Array LinearWitnessFact := #[]
      for h : index in [:negations.size] do
        let type ← whnfR (← inferType negations[index])
        let .app (.const ``Not _) proposition := type
          | trace[crush.replay] "la_generic witness declined: expected a negated literal, \
              got {type}"
            return none
        let some arithmeticProof ← MetaProblem.pushNot negations[index] proposition
          | trace[crush.replay] "la_generic witness declined: could not normalize \
              negation of {proposition}"
            return none
        let arithmeticType ← inferType arithmeticProof
        let some fact ← normalizeRelation index arithmeticProof
          | trace[crush.replay] "la_generic witness declined: unsupported relation \
              {arithmeticType}"
            return none
        facts := facts.push fact
      match coefficients.toList.zip facts.toList with
      | [] => return none
      | (firstCoefficient, firstFact) :: rest =>
        let firstWeight := scaledMultiplier firstCoefficient firstFact.fact
        let mut combined := scaleFact firstWeight firstFact.fact
        for (coefficient, fact) in rest do
          let weight := scaledMultiplier coefficient fact.fact
          combined := Fact.combo 1 combined weight fact.fact
        combined := combined.tidy
        unless combined.coeffs.isZero && combined.constraint.isImpossible do
          trace[crush.replay] "la_generic witness declined: certificate leaves \
            coefficients {combined.coeffs} in constraint {combined.constraint}"
          return none
        return some (← Problem.proveFalse combined.justification (facts.map (·.proof)))
    ) {}
    let some proof := proof? | return false
    falseGoal.assign (← instantiateMVars proof)
    return true

private def linearEqualityProof? (left right : Expr) : MetaM (Option Expr) :=
  OmegaM.run (do
    let (leftCombo, leftProof, _) ← asLinearCombo left
    let (rightCombo, rightProof, _) ← asLinearCombo right
    unless leftCombo == rightCombo do return none
    return some (← mkEqTrans (← leftProof) (← mkEqSymm (← rightProof)))) {}

private def proveLinearEquality (goal : MVarId) : TacticM Bool := goal.withContext do
  let target ← whnfR (← goal.getType)
  let_expr Eq type left right := target | return false
  unless type.isConstOf ``Int do return false
  let proof? ← linearEqualityProof? left right
  let some proof := proof? | return false
  goal.assign (← instantiateMVars proof)
  return true

private theorem intEqIffOfSubEq {a b c d : Int} (h : a - b = c - d) :
    (a = b ↔ c = d) := by
  constructor
  · intro hab
    apply Int.eq_of_sub_eq_zero
    rw [← h]
    exact Int.sub_eq_zero_of_eq hab
  · intro hcd
    apply Int.eq_of_sub_eq_zero
    rw [h]
    exact Int.sub_eq_zero_of_eq hcd

private theorem intLeIffOfSubEq {a b c d : Int} (h : b - a = d - c) :
    (a ≤ b ↔ c ≤ d) := by
  constructor
  · intro hab
    apply Int.le_of_sub_nonneg
    rw [← h]
    exact Int.sub_nonneg_of_le hab
  · intro hcd
    apply Int.le_of_sub_nonneg
    rw [h]
    exact Int.sub_nonneg_of_le hcd

private theorem intLtIffOfSubEq {a b c d : Int} (h : b - a = d - c) :
    (a < b ↔ c < d) := by
  constructor
  · intro hab
    apply Int.lt_of_sub_pos
    rw [← h]
    exact Int.sub_pos_of_lt hab
  · intro hcd
    apply Int.lt_of_sub_pos
    rw [h]
    exact Int.sub_pos_of_lt hcd

private theorem intEqIffOfNegatedSubEq {a b c d : Int}
    (h : -1 * (a - b) = 1 * (c - d)) :
    (a = b ↔ c = d) := by
  omega

private inductive LinearRelation where
  | eq | le | lt
  deriving BEq

private def linearRelation? (proposition : Expr) :
    MetaM (Option (LinearRelation × Expr × Expr × Expr)) := do
  let proposition ← whnfR proposition
  match_expr proposition with
  | Eq type left right =>
    unless type.isConstOf ``Int do return none
    return some (.eq, left, right, ← mkAppM ``HSub.hSub #[left, right])
  | LE.le type _ left right =>
    unless type.isConstOf ``Int do return none
    return some (.le, left, right, ← mkAppM ``HSub.hSub #[right, left])
  | LT.lt type _ left right =>
    unless type.isConstOf ``Int do return none
    return some (.lt, left, right, ← mkAppM ``HSub.hSub #[right, left])
  | _ => return none

private def proveLinearRelationIff (goal : MVarId) : TacticM Bool := goal.withContext do
  let target ← whnfR (← goal.getType)
  let some (left, right) := target.iff? | return false
  let some (leftKind, _, _, leftDifference) ← linearRelation? left | return false
  let some (rightKind, _, _, rightDifference) ← linearRelation? right | return false
  unless leftKind == rightKind do return false
  if let some differenceProof ← linearEqualityProof? leftDifference rightDifference then
    let theoremName := match leftKind with
      | .eq => ``intEqIffOfSubEq
      | .le => ``intLeIffOfSubEq
      | .lt => ``intLtIffOfSubEq
    let proof ← mkAppM theoremName #[differenceProof]
    if ← isDefEqGuarded (← inferType proof) target then
      goal.assign (← instantiateMVars proof)
      return true
  if leftKind == .eq then
    for hypothesis in ← getLocalHyps do
      let candidates ← try
        pure #[hypothesis, ← mkEqSymm hypothesis]
      catch _ =>
        pure #[hypothesis]
      for candidate in candidates do
        try
          let proof ← mkAppM ``intEqIffOfNegatedSubEq #[candidate]
          if ← isDefEqGuarded (← inferType proof) target then
            goal.assign (← instantiateMVars proof)
            return true
        catch _ =>
          pure ()
  return false

@[crush_replay_rule "la_generic" high]
def replayLinearArithmetic : ReplayRuleHandler := fun ctx => do
  let some coefficients := integerMultipliers ctx.args | return none
  ctx.runMetaWithScopeFallback (checkLinearWitness coefficients)

@[crush_replay_rule "poly_simp" high]
def replayPolynomialEquality : ReplayRuleHandler := fun ctx =>
  ctx.runMeta proveLinearEquality

@[crush_replay_rule "poly_simp_rel" high]
def replayPolynomialRelation : ReplayRuleHandler := fun ctx =>
  ctx.runMeta proveLinearRelationIff

/-! ## Integer rewrites and multiplication -/

private theorem intAbsEq (left right : Int) :
    intAbs left = intAbs right ↔ left = right ∨ left = -right := by
  unfold intAbs
  by_cases hl : left < 0 <;> by_cases hr : right < 0 <;>
    simp [hl, hr] <;> omega

private theorem intAbsGt (left right : Int) :
    intAbs left > intAbs right ↔
      if left ≥ 0 then
        if right ≥ 0 then left > right else left > -right
      else
        if right ≥ 0 then -left > right else -left > -right := by
  unfold intAbs
  split <;> split <;> split <;> split <;> omega

private theorem intAbsNatCast (value : Int) : intAbs value = (value.natAbs : Int) := by
  unfold intAbs
  split
  · exact (Int.ofNat_natAbs_of_nonpos (by omega)).symm
  · exact (Int.natAbs_of_nonneg (by omega)).symm

private theorem intAbsSquareLt (left right : Int) (h : intAbs left < intAbs right) :
    intAbs (left * left) < intAbs (right * right) := by
  simp only [intAbsNatCast, Int.natAbs_mul, Int.ofNat_lt] at *
  exact Nat.mul_lt_mul_of_lt_of_lt h h

private theorem intSquarePositive (value : Int) (h : value ≠ 0) : value * value > 0 := by
  by_cases hn : value < 0
  · exact Int.mul_pos_of_neg_of_neg hn hn
  · exact Int.mul_pos (by omega) (by omega)

private theorem intLeNorm (left right : Int) :
    (left ≤ right ↔ ¬left ≥ right + 1) := by
  omega

private theorem intElimLt (left right : Int) :
    (left < right ↔ ¬left ≥ right) := by
  omega

private theorem intElimGt (left right : Int) :
    (left > right ↔ ¬right ≥ left) := by
  omega

private theorem intMulNegative (coefficient left right : Int) :
    coefficient < 0 ∧ left ≥ right →
      coefficient * left ≤ coefficient * right := fun hypothesis =>
  Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hypothesis.1) hypothesis.2

private theorem intMulPositive (coefficient left right : Int) :
    coefficient > 0 ∧ left ≤ right →
      coefficient * left ≤ coefficient * right := fun hypothesis =>
  Int.mul_le_mul_of_nonneg_left hypothesis.2 (Int.le_of_lt hypothesis.1)

private theorem intMulPositiveEq (coefficient left right : Int) :
    coefficient > 0 ∧ left = right →
      coefficient * left = coefficient * right := fun hypothesis =>
  congrArg (coefficient * ·) hypothesis.2

register_crush_replay rule low <<
  (rare_rewrite "arith-leq-norm" ..) => by exact intLeNorm _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "arith-elim-lt" ..) => by exact intElimLt _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "arith-elim-gt" ..) => by exact intElimGt _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "arith-geq-norm1-int" ..) => by exact Int.sub_nonneg.symm
>>

register_crush_replay rule low <<
  (rare_rewrite "arith-abs-eq" ..) => by exact intAbsEq _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "arith-abs-int-gt" (term left : Int) (term right : Int)) => by
    exact intAbsGt left right
>>

register_crush_replay rule low <<
  (la_mult_sign ..) => by exact intSquarePositive _ (by assumption)
>>

register_crush_replay rule low <<
  (la_mult_abs_comparison ..) => by
    first
    | exact intAbsSquareLt _ _ ((intAbsGt _ _).mpr (by assumption))
    | exact intAbsSquareLt _ _ (by assumption)
    | grind [intAbs]
>>

private def hasIntAbsPremise : ReplayConditionHandler := fun ctx =>
  return ctx.premises.any fun premise =>
    (premise.clause.find? (·.isConstOf ``intAbs)).isSome

-- Alethe closes these anchors with expanded sign tests, while their final
-- arithmetic step still states the comparison using absolute values.
register_crush_replay rule low <<
  (subproof ..) if hasIntAbsPremise => by
    simp only [← intAbsGt] at *
    grind (ematch := 0) only
>>

register_crush_replay rule low <<
  (la_mult_neg ..) => by exact intMulNegative _ _ _ (by assumption)
>>

register_crush_replay rule low <<
  (la_mult_pos ..) =>
    by first
      | exact intMulPositive _ _ _ (by assumption)
      | exact intMulPositiveEq _ _ _ (by assumption)
>>

end Crush.Alethe
