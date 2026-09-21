import Crush.Solver.Alethe.ArithmeticRules

/-!
# Built-in Alethe replay rules

Assumption normalization and logical, string, and bit-vector handlers are
registered through the public replay interface. Arithmetic handlers are imported
from `ArithmeticRules`. Supporting lemmas stay with their handlers here; certificate
traversal, structural clause proofs, and final validation live in `Replay`.

`protocolHint?` supplies the engine's fallback tactics for assumptions and anchors.
-/

namespace Crush.Alethe.ReplayRules

open Lean Meta Elab Tactic
open Crush.SMT

universe u

/-! ## Source assumptions

Normalize decoded Nat-as-Int guards, including under quantifiers and
uninterpreted applications, without unfolding source functions.
-/

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

/-! ## Logical and theory rules -/

private theorem stringEqAppendSelfIff (pre rest : String) :
    rest = pre ++ rest ↔ "" = pre := by
  rw [eq_comm (a := rest), String.append_eq_right_iff, eq_comm (a := pre)]

private theorem stringEqSelfAppendIff (pre rest : String) :
    pre = pre ++ rest ↔ "" = rest := by
  rw [eq_comm (a := pre), String.append_eq_left_iff, eq_comm (a := rest)]

private theorem stringSubstrFull (s : String) :
    stringSubstr s 0 (Int.ofNat s.length) = s := by
  apply String.ext
  simp [stringSubstr, ← String.length_toList]

private theorem stringSubstrAppendPrefix (left right : String) :
    stringSubstr (left ++ right) 0 (Int.ofNat left.length) = left := by
  apply String.ext
  simp [stringSubstr, String.toList_append, ← String.length_toList]

private theorem stringSubstrAppendSuffix (left right : String) :
    stringSubstr (left ++ right) (Int.ofNat left.length) (Int.ofNat right.length) = right := by
  have nonnegative : ¬Int.ofNat left.length < 0 :=
    Int.not_lt.mpr (Int.natCast_nonneg _)
  unfold stringSubstr
  rw [if_neg nonnegative]
  apply String.ext
  simp [String.Slice.toList_copy_take, String.toList_copy_drop,
    String.toList_append, ← String.length_toList]

private theorem stringPrefixIffSubstr (pattern value : String) :
    String.isPrefixOf pattern value = true ↔
      pattern = stringSubstr value 0 (Int.ofNat pattern.length) := by
  change value.startsWith pattern ↔ _
  rw [String.startsWith_string_iff, List.prefix_iff_eq_take, String.ext_iff]
  simp [stringSubstr, ← String.length_toList]

private theorem stringEndsWithAppend (left right : String) :
    (left ++ right).endsWith right = true := by
  change (left ++ right).toSlice.endsWith right
  rw [String.Slice.endsWith_string_iff]
  simp [String.toList_append]

private theorem stringSuffixAppendIffSubstr (left right : String) :
    (left ++ right).endsWith right = true ↔
      right = stringSubstr (left ++ right)
        (Int.ofNat (left ++ right).length - Int.ofNat right.length)
        (Int.ofNat right.length) := by
  have start :
      Int.ofNat (left ++ right).length - Int.ofNat right.length =
        Int.ofNat left.length := by
    simp [String.length_append]
  rw [start, stringSubstrAppendSuffix]
  simp [stringEndsWithAppend]

private theorem stringContainsSelf (value : String) :
    value.contains value = true := by
  rw [String.contains_string_iff]
  exact List.infix_refl _

private theorem stringContainsAppend (left right : String) :
    (left ++ right).contains left = true := by
  rw [String.contains_string_iff]
  simpa [String.toList_append] using
    (List.infix_append_left (l₁ := left.toList) (l₂ := right.toList))

private theorem stringIntLengthAppend (left right : String) :
    Int.ofNat (left ++ right).length =
      Int.ofNat left.length + Int.ofNat right.length := by
  rw [String.length_append]
  rfl

private theorem stringIntLengthEqZeroIff (value : String) :
    Int.ofNat value.length = 0 ↔ value = "" := by
  constructor
  · intro h
    exact String.length_eq_zero_iff.mp (Int.ofNat.inj h)
  · intro h
    exact congrArg Int.ofNat (String.length_eq_zero_iff.mpr h)

private theorem stringIntLengthAppendEqZeroIff (left right : String) :
    Int.ofNat (left ++ right).length = 0 ↔
      left = "" ∧ Int.ofNat right.length = 0 := by
  rw [stringIntLengthEqZeroIff, String.append_eq_empty_iff]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨hl, (stringIntLengthEqZeroIff right).mpr hr⟩
  · rintro ⟨hl, hr⟩
    exact ⟨hl, (stringIntLengthEqZeroIff right).mp hr⟩

private theorem stringIsEmptyEqDecide (value : String) :
    value.isEmpty = decide (value = "") := by
  rw [Bool.eq_iff_iff, String.isEmpty_iff, decide_eq_true_iff]

private theorem stringAppendIsEmptyEqIff (left right : String) :
    (left ++ right).isEmpty = (left.isEmpty && right.isEmpty) ↔
      ((left ++ right = "") ↔ (left = "" ∧ right = "")) := by
  rw [Bool.eq_iff_iff]
  simp only [String.isEmpty_iff, Bool.and_eq_true]

private theorem bitVecGetLsbDXor {width : Nat} (left right : BitVec width)
    (index : Nat) :
    (BitVec.xor left right).getLsbD index =
      Bool.xor (left.getLsbD index) (right.getLsbD index) :=
  BitVec.getLsbD_xor

private theorem bitVecUltEqTrueIffLt {width : Nat} (left right : BitVec width) :
    left.ult right = true ↔ left < right :=
  BitVec.ult_iff_lt

private theorem bitVecUleEqTrueIffLe {width : Nat} (left right : BitVec width) :
    left.ule right = true ↔ left ≤ right :=
  BitVec.ule_iff_le

private theorem decideIffBoolEqTrue {predicate : Prop} {decision : Decidable predicate}
    {value : Bool} (equal : @decide predicate decision = value) :
    predicate ↔ value = true := by
  rw [← @decide_eq_true_iff predicate decision]
  exact Bool.eq_iff_iff.mp equal

private theorem decideEqBoolOfIff {predicate : Prop} {decision : Decidable predicate}
    {value : Bool} (equal : predicate ↔ value = true) :
    @decide predicate decision = value := by
  rw [Bool.eq_iff_iff, @decide_eq_true_iff predicate decision]
  exact equal

private theorem existsLtSucc {predicate : Nat → Prop} (bound : Nat) :
    (∃ index < bound + 1, predicate index) ↔
      predicate bound ∨ ∃ index < bound, predicate index := by
  constructor
  · rintro ⟨index, less, holds⟩
    by_cases equal : index = bound
    · exact Or.inl (equal ▸ holds)
    · exact Or.inr ⟨index, by omega, holds⟩
  · rintro (holds | ⟨index, less, holds⟩)
    · exact ⟨bound, by omega, holds⟩
    · exact ⟨index, by omega, holds⟩

private theorem forallIffAtCounterexample {α : Sort u} [Nonempty α] (predicate : α → Prop) :
    (∀ x, predicate x) ↔
      predicate (Classical.epsilon fun x => ¬predicate x) := by
  constructor
  · intro h
    exact h _
  · intro h x
    exact Classical.byContradiction fun hx =>
      (Classical.epsilon_spec (p := fun x => ¬predicate x) ⟨x, hx⟩) h

private theorem existsIffAtWitness {α : Sort u} [Nonempty α] (predicate : α → Prop) :
    (∃ x, predicate x) ↔
      predicate (Classical.epsilon predicate) := by
  constructor
  · exact Classical.epsilon_spec
  · intro h
    exact ⟨_, h⟩

private theorem forallInstClause {α : Sort u} (predicate : α → Prop) (witness : α) :
    (¬∀ x, predicate x) ∨ predicate witness := by
  classical
  by_cases h : ∀ x, predicate x
  · exact Or.inr (h witness)
  · exact Or.inl h

private theorem iffTrueIff (predicate : Prop) : ((predicate ↔ True) ↔ predicate) := by
  simp

private theorem notNotIff (predicate : Prop) : (¬¬predicate ↔ predicate) := by
  exact Classical.not_not

private theorem equalityReflexiveIffTrue {α : Sort u} (value : α) :
    (value = value ↔ True) :=
  iff_true_intro rfl

private theorem equalitySymmetricIff {α : Sort u} (left right : α) :
    (left = right ↔ right = left) :=
  eq_comm

private def bitVecUnsignedLtBits : (width : Nat) → BitVec width → BitVec width → Prop
  | 0, _, _ => False
  | width + 1, left, right =>
      (left.msb = right.msb ∧
        bitVecUnsignedLtBits width (left.setWidth width) (right.setWidth width)) ∨
      (left.msb = false ∧ right.msb = true)

private theorem bitVecUnsignedLtBitsCorrect {width : Nat}
    (left right : BitVec width) :
    bitVecUnsignedLtBits width left right ↔ left.toNat < right.toNat := by
  induction width with
  | zero =>
    simp [bitVecUnsignedLtBits, BitVec.toNat_of_zero_length]
  | succ width ih =>
    have leftValue :
        left.toNat =
          left.msb.toNat * 2 ^ width + (left.setWidth width).toNat := by
      have decomposition :=
        congrArg BitVec.toNat (BitVec.cons_msb_setWidth left)
      rw [BitVec.toNat_cons'] at decomposition
      simpa only [Nat.shiftLeft_eq, Nat.mul_comm] using decomposition.symm
    have rightValue :
        right.toNat =
          right.msb.toNat * 2 ^ width + (right.setWidth width).toNat := by
      have decomposition :=
        congrArg BitVec.toNat (BitVec.cons_msb_setWidth right)
      rw [BitVec.toNat_cons'] at decomposition
      simpa only [Nat.shiftLeft_eq, Nat.mul_comm] using decomposition.symm
    have leftBound := (left.setWidth width).isLt
    have rightBound := (right.setWidth width).isLt
    cases hl : left.msb <;> cases hr : right.msb
    all_goals
      simp only [bitVecUnsignedLtBits, hl, hr]
      rw [ih, leftValue, rightValue]
      simp [hl, hr] <;> omega

private theorem bitVecUnsignedLtBitsBoolCorrect {width : Nat}
    (left right : BitVec width) :
    left.ult right = true ↔ bitVecUnsignedLtBits width left right := by
  simpa [BitVec.ult_eq_decide] using
    (bitVecUnsignedLtBitsCorrect left right).symm

private theorem bitVecSignedLtBitsCorrect {width : Nat}
    (left right : BitVec (width + 1)) :
    left.slt right = true ↔
      (left.msb = right.msb ∧
        bitVecUnsignedLtBits width (left.setWidth width) (right.setWidth width)) ∨
      (left.msb = true ∧ right.msb = false) := by
  by_cases hsign : left.msb = right.msb
  · rw [BitVec.slt_eq_ult_of_msb_eq hsign]
    rw [BitVec.ult_eq_decide, decide_eq_true_iff, ← bitVecUnsignedLtBitsCorrect]
    simp [bitVecUnsignedLtBits, hsign]
  · rw [BitVec.slt_eq_not_ult_of_msb_neq hsign,
      BitVec.ult_eq_msb_of_msb_neq hsign]
    cases hl : left.msb <;> cases hr : right.msb <;> simp_all

private theorem bitVecOfNatPowSubOne (width : Nat) :
    BitVec.ofNat width (2 ^ width - 1) = BitVec.allOnes width := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_allOnes]
  apply Nat.mod_eq_of_lt
  have positive := Nat.two_pow_pos width
  omega

private theorem bitVecUleOfNatPowSubOne {width : Nat} (value : BitVec width) :
    value.ule (BitVec.ofNat width (2 ^ width - 1)) = true := by
  rw [bitVecOfNatPowSubOne, BitVec.ule_eq_decide, decide_eq_true_iff]
  have bound := value.isLt
  simp
  omega

private theorem bitVecAndOfNatPowSubOne {width : Nat} (value : BitVec width) :
    value &&& BitVec.ofNat width (2 ^ width - 1) = value := by
  rw [bitVecOfNatPowSubOne]
  exact BitVec.and_allOnes

private theorem bitVecMulPowTwoEliminate {high shift : Nat}
    (value : BitVec (high + 1 + shift)) :
    value * BitVec.ofNat (high + 1 + shift) (2 ^ shift) =
      BitVec.extractLsb high 0 value ++ 0#shift := by
  have power :
      BitVec.ofNat (high + 1 + shift) (2 ^ shift) =
        BitVec.twoPow (high + 1 + shift) shift := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [power, BitVec.mul_twoPow_eq_shiftLeft]
  have remaining : high + 1 + shift - shift = high + 1 := by omega
  have last : high + 1 - 1 = high := by omega
  rw [BitVec.shiftLeft_eq_concat_of_lt (x := value) (n := shift) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_eq_extractLsb, remaining, last]

private theorem bitVecExtractSignEqFalse {width : Nat} (value : BitVec (width + 1)) :
    BitVec.extractLsb' width 1 value = 0#1 ↔ value.msb = false := by
  simp [BitVec.eq_of_getLsbD_eq_iff, BitVec.msb, BitVec.getMsbD_eq_getLsbD]

private theorem bitVecExtractSignEqTrue {width : Nat} (value : BitVec (width + 1)) :
    BitVec.extractLsb' width 1 value = 1#1 ↔ value.msb = true := by
  simp [BitVec.eq_of_getLsbD_eq_iff, BitVec.msb, BitVec.getMsbD_eq_getLsbD]

private theorem bitVecSmodEliminate {width : Nat}
    (left right : BitVec (width + 1)) :
    left.smod right =
      let leftNonnegative := BitVec.extractLsb' width 1 left = 0#1
      let rightNonnegative := BitVec.extractLsb' width 1 right = 0#1
      let unsigned :=
        (if leftNonnegative then left else -left).umod
          (if rightNonnegative then right else -right)
      if unsigned = 0#(width + 1) then
        unsigned
      else if leftNonnegative ∧ rightNonnegative then
        unsigned
      else if BitVec.extractLsb' width 1 left = 1#1 ∧ rightNonnegative then
        -unsigned + right
      else if leftNonnegative ∧ BitVec.extractLsb' width 1 right = 1#1 then
        unsigned + right
      else
        -unsigned := by
  cases hl : left.msb <;> cases hr : right.msb <;>
    simp_all [BitVec.smod_eq, bitVecExtractSignEqFalse, bitVecExtractSignEqTrue,
      BitVec.sub_eq_add_neg, BitVec.add_comm]

private def bvDecideHint? : CoreM (Option (TSyntax `tactic)) := do
  unless crush.reconstruct.trustBvDecide.get (← getOptions) do return none
  return some (← `(tactic| bv_decide))

register_crush_replay rule low <<
  (rare_rewrite "str-prefixof-elim" ..) =>
    by exact stringPrefixIffSubstr _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "str-suffixof-elim" ..) =>
    by exact stringSuffixAppendIffSubstr _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "str-substr-full-eq" ..) =>
    by exact stringSubstrFull _
>>

register_crush_replay rule low <<
  (rare_rewrite "str-substr-concat1" ..) =>
    by rw [stringSubstrAppendPrefix, stringSubstrFull]
>>

register_crush_replay rule low <<
  (rare_rewrite "str-substr-concat2" ..) =>
    by rw [stringSubstrAppendSuffix, Int.sub_self, stringSubstrFull]
>>

register_crush_replay rule low <<
  (rare_rewrite "str-contains-refl" ..) =>
    by simp only [stringContainsSelf]
>>

register_crush_replay rule low <<
  (rare_rewrite "str-contains-concat-find" ..) =>
    by simp only [stringContainsAppend]
>>

register_crush_replay rule low <<
  (rare_rewrite "str-len-concat-rec" ..) =>
    by exact stringIntLengthAppend _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "str-len-eq-zero-base" ..) =>
    by exact stringIntLengthEqZeroIff _
>>

register_crush_replay rule low <<
  (rare_rewrite "str-len-eq-zero-concat-rec" ..) =>
    by exact stringIntLengthAppendEqZeroIff _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "str-concat-unify" ..) =>
    by
      simp only [String.append_assoc, String.append_left_inj,
        String.append_right_inj]
>>

register_crush_replay rule low <<
  (rare_rewrite "str-concat-unify-base" ..) =>
    by simp only [stringEqAppendSelfIff, stringEqSelfAppendIff]
>>

register_crush_replay rule low <<
  (rare_rewrite "bool-eq-true" ..) => by exact iffTrueIff _
>>

register_crush_replay rule low <<
  (rare_rewrite "bool-double-not-elim" ..) => by exact notNotIff _
>>

register_crush_replay rule low <<
  (rare_rewrite "eq-refl" ..) => by exact equalityReflexiveIffTrue _
>>

register_crush_replay rule low <<
  (rare_rewrite "eq-symm" ..) => by exact equalitySymmetricIff _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "bv-ule-max" ..) =>
    by exact iff_true_intro (bitVecUleOfNatPowSubOne _)
>>

register_crush_replay rule low <<
  (rare_rewrite "bv-mult-pow2-1" _ _ _ _ _ (nat shift) (nat high) ..) =>
    by
      exact bitVecMulPowTwoEliminate
        (high := high) (shift := shift) _
>>

register_crush_replay rule low <<
  (rare_rewrite "bv-smod-eliminate" ..) =>
    by exact bitVecSmodEliminate _ _
>>

register_crush_replay rule low <<
  (rare_rewrite "bv-sle-eliminate" ..) =>
    by simp [BitVec.sle_eq_not_slt]
>>

register_crush_replay rule low <<
  (rare_rewrite "bv-ule-eliminate" ..) =>
    by simp [BitVec.ule_eq_not_ult]
>>

register_crush_replay rule low <<
  (rare_rewrite "bv-lt-self" ..) |
  (rare_rewrite "bv-ult-self" ..) |
  (rare_rewrite "bv-ugt-self" ..) |
  (rare_rewrite "bv-slt-self" ..) |
  (rare_rewrite "bv-sgt-self" ..) =>
    by simp [BitVec.ult_eq_decide, BitVec.slt_eq_decide]
>>

register_crush_replay rule low <<
  (refl ..) => by rfl
>>

register_crush_replay rule low <<
  (evaluate ..) | (false ..) => by decide
>>

register_crush_replay rule low <<
  (cong ..) =>
    by
      first
      | rfl
      | exact imp_congr Iff.rfl (by assumption)
      | exact imp_congr (by assumption) Iff.rfl
      | (apply imp_congr <;> assumption)
      | (congr 1 <;> assumption)
      | simp_all only
>>

register_crush_replay rule low <<
  (forall_inst ..) => by exact forallInstClause _ _
>>

register_crush_replay rule low <<
  (and_neg ..) =>
    by simp_all [Bool.xor_comm, Bool.xor_left_comm]
>>

register_crush_replay rule low <<
  (aci_simp ..) => by exact bitVecAndOfNatPowSubOne _
>>

register_crush_replay rule low <<
  (resolution ..) =>
    by first | grind | simp_all [stringIsEmptyEqDecide]
>>

register_crush_replay rule low <<
  (not_or ..) | (or ..) | (and ..) | (and_intro ..) |
  (and_pos ..) | (or_pos ..) | (or_neg ..) |
  (equiv1 ..) | (equiv2 ..) | (equiv_pos1 ..) |
  (equiv_pos2 ..) | (equiv_neg1 ..) | (equiv_neg2 ..) |
  (xor_pos1 ..) | (xor_pos2 ..) | (xor_neg1 ..) |
  (xor_neg2 ..) | (ite1 ..) | (ite2 ..) | (implies ..) |
  (implies_neg1 ..) | (implies_neg2 ..) =>
    by grind
>>

private partial def concreteNatValue? (value : Expr) : MetaM (Option Nat) := do
  if let some value ← getNatValue? value then return some value
  let value ← whnf value
  if let some value ← getNatValue? value then return some value
  if value.isAppOfArity ``Nat.succ 1 then
    return (← concreteNatValue? value.getAppArgs[0]!).map (· + 1)
  return none

/-- Project a bit-vector equality into cvc5's conjunction of bit equalities. -/
private partial def bitEqualityForward (index width : Nat) :
    TacticM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if index >= width then
    return ← `(tacticSeq| trivial)
  let value : TSyntax `term := ⟨Syntax.mkNumLit (toString index)⟩
  let proveBit ← `(tacticSeq|
    have projected := congrArg (fun vector => vector.getLsbD $value) heq
    repeat' rw [bitVecGetLsbDXor] at projected
    first
    | exact projected
    | simp only [BitVec.getLsbD_ofBoolListLE, List.getD] at projected
      exact decideIffBoolEqTrue projected
    | simp only [BitVec.getLsbD_ofBoolListLE, List.getD] at projected
      exact (decideIffBoolEqTrue projected).symm
    | simp only [BitVec.getLsbD_ofBoolListLE, List.getD] at projected
      exact decideIffBoolEqTrue projected.symm
    | simp only [BitVec.getLsbD_ofBoolListLE, List.getD] at projected
      exact (decideIffBoolEqTrue projected.symm).symm)
  if index + 1 >= width then
    return proveBit
  let rest ← bitEqualityForward (index + 1) width
  `(tacticSeq|
    constructor
    · $proveBit:tacticSeq
    · $rest:tacticSeq)

/-- Enumerate a statically bounded bit index and select its matching bit hypothesis. -/
private partial def bitIndexCases (index width : Nat) :
    TacticM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if index >= width then
    return ← `(tacticSeq| omega <;> done)
  let rest ← bitIndexCases (index + 1) width
  let value : TSyntax `term := ⟨Syntax.mkNumLit (toString index)⟩
  let mut projection ← `(term| hbits)
  for _ in [:index] do
    projection ← `(term| ($projection).2)
  if index + 1 < width then
    projection ← `(term| ($projection).1)
  `(tacticSeq|
    by_cases hindex : i = $value
    · subst i
      first
      | exact $projection
      | simp only [BitVec.getLsbD_ofBoolListLE, List.getD]
        exact decideEqBoolOfIff $projection
      | simp only [BitVec.getLsbD_ofBoolListLE, List.getD]
        exact (decideEqBoolOfIff $projection).symm
      | simp only [BitVec.getLsbD_ofBoolListLE, List.getD]
        exact decideEqBoolOfIff ($projection).symm
      | simp only [BitVec.getLsbD_ofBoolListLE, List.getD]
        exact (decideEqBoolOfIff ($projection).symm).symm
      | repeat' rw [bitVecGetLsbDXor]
        grind
    · $rest:tacticSeq)

/-- Concrete checker for cvc5's vector-equality-to-bits bridge. -/
private def bitVecEqualityHint? (target : Expr) : TacticM (Option (TSyntax `tactic)) := do
  let target ← whnf target
  unless target.isAppOfArity ``Iff 2 do return none
  let equality := target.getAppArgs[0]!
  unless equality.isAppOfArity ``Eq 3 do return none
  let type ← whnf (← inferType equality.getAppArgs[1]!)
  let .app (.const ``BitVec _) widthExpr := type | return none
  let some width ← concreteNatValue? widthExpr | return none
  let forward ← bitEqualityForward 0 width
  let cases ← bitIndexCases 0 width
  let widthSyntax : TSyntax `term := ⟨Syntax.mkNumLit (toString width)⟩
  return some (← `(tactic|
    (constructor
     · intro heq
       ($forward:tacticSeq)
     · intro hbits
       apply BitVec.eq_of_getLsbD_eq
       intro i hi
       have hbound : i < $widthSyntax := by exact hi
       ($cases:tacticSeq))))

/-- Enumerate a concrete bit-vector width and prove each selected negation bit. -/
private partial def bitVecNegCases (index width : Nat) :
    TacticM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if index >= width then
    return ← `(tacticSeq| omega <;> done)
  let rest ← bitVecNegCases (index + 1) width
  let value : TSyntax `term := ⟨Syntax.mkNumLit (toString index)⟩
  `(tacticSeq|
    by_cases hindex : i = $value
    · subst i
      rw [BitVec.neg_eq, BitVec.getLsbD_neg, BitVec.getLsbD_ofBoolListLE]
      simp_all [existsLtSucc, Bool.xor_comm] <;> grind <;> done
    · $rest:tacticSeq)

/-- Prove cvc5's ripple-carry expansion of fixed-width bit-vector negation. -/
private def bitVecNegationHint? (target : Expr) :
    TacticM (Option (TSyntax `tactic)) := do
  let target ← whnf target
  unless target.isAppOfArity ``Eq 3 do return none
  let type ← whnf target.getAppArgs[0]!
  let .app (.const ``BitVec _) widthExpr := type | return none
  let some width ← concreteNatValue? widthExpr | return none
  let cases ← bitVecNegCases 0 width
  return some (← `(tactic|
    (apply BitVec.eq_of_getLsbD_eq
     intro i hi
     ($cases:tacticSeq))))

private partial def bitVecExtractCases (index width : Nat) :
    TacticM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if index >= width then
    return ← `(tacticSeq| omega <;> done)
  let rest ← bitVecExtractCases (index + 1) width
  let value : TSyntax `term := ⟨Syntax.mkNumLit (toString index)⟩
  `(tacticSeq|
    by_cases hindex : i = $value
    · subst i
      rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_ofBoolListLE]
      simp [List.getD]
    · $rest:tacticSeq)

/-- Check cvc5's extraction circuit against Lean's indexed-bit semantics. -/
private def bitVecExtractHint? (target : Expr) :
    TacticM (Option (TSyntax `tactic)) := do
  let target ← whnf target
  unless target.isAppOfArity ``Eq 3 do return none
  let type ← whnf (← inferType target.getAppArgs[1]!)
  let .app (.const ``BitVec _) widthExpr := type | return none
  let some width ← concreteNatValue? widthExpr | return none
  let widthSyntax : TSyntax `term := ⟨Syntax.mkNumLit (toString width)⟩
  let cases ← bitVecExtractCases 0 width
  return some (← `(tactic|
    (apply BitVec.eq_of_getLsbD_eq
     intro i hi
     have hbound : i < $widthSyntax := by exact hi
     ($cases:tacticSeq))))

/-- Prove cvc5's unrolled unsigned lexicographic comparison at any width. -/
private def bitVecUnsignedLtHint? (target : Expr) :
    TacticM (Option (TSyntax `tactic)) := do
  let target ← whnf target
  unless target.isAppOfArity ``Iff 2 do return none
  let comparison := target.getAppArgs[0]!
  unless comparison.isAppOfArity ``Eq 3 do return none
  let ult := comparison.getAppArgs[1]!
  unless ult.isAppOfArity ``BitVec.ult 3 do return none
  let type ← whnf (← inferType ult.getAppArgs[1]!)
  let .app (.const ``BitVec _) widthExpr := type | return none
  let some width ← concreteNatValue? widthExpr | return none
  let widthSyntax : TSyntax `term := ⟨Syntax.mkNumLit (toString width)⟩
  return some (← `(tactic|
    (rw [bitVecUnsignedLtBitsBoolCorrect (width := $widthSyntax)]
     simp [bitVecUnsignedLtBits, BitVec.msb_eq_getLsbD_last])))

/-- Prove cvc5's unrolled signed lexicographic comparison at any positive width. -/
private def bitVecSignedLtHint? (target : Expr) :
    TacticM (Option (TSyntax `tactic)) := do
  let target ← whnf target
  unless target.isAppOfArity ``Iff 2 do return none
  let comparison := target.getAppArgs[0]!
  unless comparison.isAppOfArity ``Eq 3 do return none
  let slt := comparison.getAppArgs[1]!
  unless slt.isAppOfArity ``BitVec.slt 3 do return none
  let type ← whnf (← inferType slt.getAppArgs[1]!)
  let .app (.const ``BitVec _) widthExpr := type | return none
  let some width ← concreteNatValue? widthExpr | return none
  if width == 0 then return none
  let lowerWidth := width - 1
  let widthSyntax : TSyntax `term := ⟨Syntax.mkNumLit (toString lowerWidth)⟩
  return some (← `(tactic|
    (rw [bitVecSignedLtBitsCorrect (width := $widthSyntax)]
     simp [bitVecUnsignedLtBits, BitVec.msb_eq_getLsbD_last])))

private inductive BitVecReplayKind where
  | equality
  | negation
  | extract
  | unsignedLt
  | signedLt

private def BitVecReplayKind.applicable
    (kind : BitVecReplayKind) (target : Expr) : MetaM Bool := do
  let target ← whnf target
  return match kind with
    | .equality | .unsignedLt | .signedLt =>
      target.isAppOfArity ``Iff 2
    | .negation | .extract =>
      target.isAppOfArity ``Eq 3

private def BitVecReplayKind.hint?
    (kind : BitVecReplayKind) (target : Expr) :
    TacticM (Option (TSyntax `tactic)) :=
  match kind with
  | .equality => bitVecEqualityHint? target
  | .negation => bitVecNegationHint? target
  | .extract => bitVecExtractHint? target
  | .unsignedLt => bitVecUnsignedLtHint? target
  | .signedLt => bitVecSignedLtHint? target

private instance : ReplayCondition BitVecReplayKind where
  check kind ctx := kind.applicable ctx.target

private def runBitVecReplay (kind : BitVecReplayKind) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some tactic ← kind.hint? target
    | throwError "bit-vector replay target has an unsupported shape"
  evalTactic tactic

register_crush_replay rule low <<
  (bv_bitblast_step_bvequal ..)
    if BitVecReplayKind.equality =>
    by run_tac runBitVecReplay BitVecReplayKind.equality
>>

register_crush_replay rule low <<
  (bv_bitblast_step_bvneg ..)
    if BitVecReplayKind.negation =>
    by run_tac runBitVecReplay BitVecReplayKind.negation
>>

register_crush_replay rule low <<
  (bv_bitblast_step_extract ..)
    if BitVecReplayKind.extract =>
    by run_tac runBitVecReplay BitVecReplayKind.extract
>>

register_crush_replay rule low <<
  (bv_bitblast_step_bvult ..)
    if BitVecReplayKind.unsignedLt =>
    by run_tac runBitVecReplay BitVecReplayKind.unsignedLt
>>

register_crush_replay rule low <<
  (bv_bitblast_step_bvslt ..)
    if BitVecReplayKind.signedLt =>
    by run_tac runBitVecReplay BitVecReplayKind.signedLt
>>

@[crush_replay_rule low]
private def replayTrustedBitVecRule : ReplayRuleHandler := fun ctx => do
  let rareBitVec :=
    ctx.rule == "rare_rewrite" &&
      match ctx.args[0]? with
      | some (Sexp.str name) => name.startsWith "bv-"
      | _ => false
  let applicable :=
    rareBitVec || ctx.rule == "hole" || ctx.rule == "aci_simp" ||
      ctx.rule == "bv_bitwise_slicing" ||
      ctx.rule.startsWith "bv_bitblast_step_"
  unless applicable do return none
  let some tactic ← bvDecideHint? | return none
  ctx.runTacticWithScopeFallback tactic

/-! ## Assumption and anchor fallbacks -/

/-- A fallback tactic with a stable label for replay telemetry. -/
structure TacticHint where
  label : String
  tactic : TSyntax `tactic

/-- Rule-specific tactics tried before the engine's generic step tactics. -/
def protocolHint? (rule : String) : CoreM (Option TacticHint) := do
  match rule with
  | "assume" =>
    let tactic ← `(tactic| first
        | simpa only [bitVecUltEqTrueIffLt, bitVecUleEqTrueIffLe] using ‹_›
        | exact mt (stringAppendIsEmptyEqIff _ _).mpr (by assumption)
        | simpa [stringIsEmptyEqDecide, String.append_eq_empty_iff] using ‹_›
        | simpa [BitVec.ult_eq_decide, BitVec.ule_eq_decide,
            BitVec.slt_eq_decide, BitVec.sle_eq_decide] using ‹_›
        | (dsimp at *
           simp_all [BitVec.ult_eq_decide, BitVec.ule_eq_decide,
             BitVec.slt_eq_decide, BitVec.sle_eq_decide]))
    return some { label := "hint:assume", tactic }
  | "bind" | "subproof" =>
    let tactic ← `(tactic| grind)
    return some { label := "hint:anchor", tactic }
  | "sko_forall" =>
    let tactic ← `(tactic| simp_all only [forallIffAtCounterexample])
    return some { label := "hint:sko_forall", tactic }
  | "sko_ex" =>
    let tactic ← `(tactic| simp_all only [existsIffAtWitness])
    return some { label := "hint:sko_ex", tactic }
  | _ =>
    return none

end Crush.Alethe.ReplayRules
