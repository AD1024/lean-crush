import Crush.Solver.Alethe
import Crush.Solver.AletheArithmetic
import Crush.Solver.ReplayAttr
import Crush.Solver.AletheTerm
import Crush.Solver.KernelCheck
import Crush.Translation.Monad
open Lean Meta Elab Tactic

/-!
# Replaying an Alethe proof as a Lean proof

The core-directed finisher (`Crush/Solver/Reconstruct.lean`) hands the *whole* goal to one
Lean tactic. That works surprisingly often, but fails when the argument needs a long chain
of small inferences no tactic re-finds in one shot.

An Alethe proof is exactly that chain, already found: cvc5 reports ~20–60 steps, each a
*trivial* clause following from one or two earlier ones. So instead of re-searching, we
replay: restate each step's clause as a Lean proposition, prove it from the premises'
proofs, carry the result forward. The last clause is empty (`False`), contradicting the
negated goal.

## Why this is sound regardless of rule coverage

Each step is type-checked by the elaborator before reuse, and the complete replayed proof is
kernel-checked before assignment. The rule name is only a *hint* for which tactic to try
first: a wrong guess makes a step fail, never succeed wrongly. Any step that cannot be
replayed makes `replay?` return `none`, and the caller falls back to the finisher ladder.

## Subproof blocks

An anchor may bind multiple local assumptions before its steps. Replay introduces each as a
real Lean hypothesis, recursively replays nested anchors, abstracts every discharged
hypothesis with `mkLambdaFVars`, and proves the closing clause from that implication. Only
the discharged closing proof escapes the block, so local assumptions cannot leak into the
outer proof environment.

## Known limits

An unmappable term or a concrete inference that the checked tactic portfolio cannot
prove makes replay decline and fall back to core reconstruction. A solver `hole` is
treated like any other untrusted rule name: it is usable only when Lean independently
proves its concrete clause.
-/

namespace Crush.Alethe

open Crush.SMT

universe u

initialize registerTraceClass `crush.replay

private structure ReplayMethodTelemetry where
  count : Nat := 0
  totalNanos : Nat := 0
  maxNanos : Nat := 0
  slowestStep : String := ""
  deriving Inhabited

private structure ReplayRuleTelemetry where
  attempts : Nat := 0
  successes : Nat := 0
  totalNanos : Nat := 0
  maxNanos : Nat := 0
  slowestStep : String := ""
  methods : Std.HashMap String ReplayMethodTelemetry := {}
  phases : Std.HashMap String ReplayMethodTelemetry := {}
  deriving Inhabited

private structure ReplayTelemetry where
  rules : Std.HashMap String ReplayRuleTelemetry := {}
  deriving Inhabited

private abbrev ReplayTelemetrySession := Option (IO.Ref ReplayTelemetry)

private def slowReplayTraceNanos : Nat := 100000000

namespace ReplayTelemetrySession

def start : CoreM ReplayTelemetrySession := do
  if ← isTracingEnabledFor `crush.replay then
    return some (← IO.mkRef {})
  return none

def mark (session : ReplayTelemetrySession) : BaseIO Nat := do
  if session.isSome then IO.monoNanosNow else return 0

def record (session : ReplayTelemetrySession) (stepId rule method : String)
    (succeeded : Bool) (started : Nat) : TacticM Nat := do
  let some ref := session | return 0
  let finished ← IO.monoNanosNow
  let elapsed := finished - started
  ref.modify fun telemetry =>
    let current := telemetry.rules.getD rule {}
    let currentMethod := current.methods.getD method {}
    let methods := current.methods.insert method {
      count := currentMethod.count + 1
      totalNanos := currentMethod.totalNanos + elapsed
      maxNanos := max currentMethod.maxNanos elapsed
      slowestStep := if elapsed > currentMethod.maxNanos then stepId
        else currentMethod.slowestStep
    }
    { telemetry with rules := telemetry.rules.insert rule {
        attempts := current.attempts + 1
        successes := current.successes + if succeeded then 1 else 0
        totalNanos := current.totalNanos + elapsed
        maxNanos := max current.maxNanos elapsed
        slowestStep := if elapsed > current.maxNanos then stepId else current.slowestStep
        methods
        phases := current.phases
      } }
  return elapsed

def recordPhase (session : ReplayTelemetrySession) (stepId rule phase : String)
    (started : Nat) : TacticM Unit := do
  let some ref := session | return
  let finished ← IO.monoNanosNow
  let elapsed := finished - started
  ref.modify fun telemetry =>
    let current := telemetry.rules.getD rule {}
    let currentPhase := current.phases.getD phase {}
    let phases := current.phases.insert phase {
      count := currentPhase.count + 1
      totalNanos := currentPhase.totalNanos + elapsed
      maxNanos := max currentPhase.maxNanos elapsed
      slowestStep := if elapsed > currentPhase.maxNanos then stepId
        else currentPhase.slowestStep
    }
    { telemetry with rules := telemetry.rules.insert rule { current with phases } }

def report (session : ReplayTelemetrySession) (commands : Nat) (succeeded : Bool) :
    TacticM Unit := do
  let some ref := session | return
  let telemetry ← ref.get
  let rows := telemetry.rules.toList.toArray.qsort fun left right =>
    if left.2.totalNanos == right.2.totalNanos then left.1 < right.1
    else left.2.totalNanos > right.2.totalNanos
  let totalAttempts := rows.foldl (fun total row => total + row.2.attempts) 0
  let totalNanos := rows.foldl (fun total row => total + row.2.totalNanos) 0
  let mut lines := #[s!"alethe replay telemetry: success={succeeded}, commands={commands}, \
    recorded_steps={totalAttempts}, summed_ns={totalNanos}"]
  for (rule, stats) in rows do
    let methods := stats.methods.toList.toArray
      |>.qsort (fun left right =>
        if left.2.totalNanos == right.2.totalNanos then left.1 < right.1
        else left.2.totalNanos > right.2.totalNanos)
      |>.map (fun (method, methodStats) =>
        s!"{method}:count={methodStats.count}:summed_ns={methodStats.totalNanos}:\
          max_ns={methodStats.maxNanos}:slowest_step={methodStats.slowestStep}")
    let phases := stats.phases.toList.toArray
      |>.qsort (fun left right =>
        if left.2.totalNanos == right.2.totalNanos then left.1 < right.1
        else left.2.totalNanos > right.2.totalNanos)
      |>.map (fun (phase, phaseStats) =>
        s!"{phase}:count={phaseStats.count}:summed_ns={phaseStats.totalNanos}:\
          max_ns={phaseStats.maxNanos}:slowest_step={phaseStats.slowestStep}")
    lines := lines.push s!"  {rule}: attempts={stats.attempts}, \
      successes={stats.successes}, failures={stats.attempts - stats.successes}, \
      summed_ns={stats.totalNanos}, max_ns={stats.maxNanos}, \
      slowest_step={stats.slowestStep}, \
      methods=[{String.intercalate "," methods.toList}], \
      phases=[{String.intercalate "," phases.toList}]"
  trace[crush.replay] "{String.intercalate "\n" lines.toList}"

end ReplayTelemetrySession

/-- The stage at which checked Alethe replay declined. -/
inductive ReplayFailureClass where
  | termGap
  | ruleGap
  | malformedCertificate
  | kernelReject
  | replayException
  deriving BEq, Inhabited, Repr

def ReplayFailureClass.label : ReplayFailureClass → String
  | .termGap => "term-gap"
  | .ruleGap => "rule-gap"
  | .malformedCertificate => "malformed-certificate"
  | .kernelReject => "kernel-reject"
  | .replayException => "replay-exception"

/-- Actionable information about the first concrete point where replay declined. -/
structure ReplayFailure where
  kind : ReplayFailureClass
  stepId : Option String := none
  rule : Option String := none
  term : Option Sexp := none
  detail : String
  deriving Inhabited, Repr

def ReplayFailure.toMessageData (failure : ReplayFailure) : MessageData :=
  let location :=
    match failure.stepId, failure.rule with
    | some step, some rule => m!" at step `{step}` (rule `{rule}`)"
    | some step, none => m!" at step `{step}`"
    | none, some rule => m!" for rule `{rule}`"
    | none, none => m!""
  let term :=
    match failure.term with
    | some term => m!"; certificate term: {term}"
    | none => m!""
  m!"{failure.kind.label}{location}: {failure.detail}{term}"

private abbrev ReplayFailureRef := IO.Ref (Option ReplayFailure)

private def rememberFailure (ref : ReplayFailureRef) (failure : ReplayFailure) :
    TacticM Unit := do
  if (← ref.get).isNone then
    ref.set (some failure)

private def clauseSexp (literals : Array Sexp) : Sexp :=
  .list (#[.atom "cl"] ++ literals)

private def replayToProp (e : Expr) : MetaM Expr := do
  let type ← whnf (← inferType e)
  if type.isProp then return e
  if type.isConstOf ``Bool then return ← mkEq e (mkConst ``Bool.true)
  return e

private structure ReplayTactic where
  label : String
  tactic : TSyntax `tactic

/-- Tactics tried on a step after structural and registered replay decline.

Deliberately cheap and local: a step is a trivial consequence of its premises (that is what
makes an Alethe proof long), so a step needing real search is one we mapped wrong, and
declining beats grinding. -/
private def stepTactics : CoreM (Array ReplayTactic) := do
  return #[
    { label := "simp_all", tactic := ← `(tactic| simp_all) },
    { label := "grind", tactic := ← `(tactic| grind) },
    { label := "rfl", tactic := ← `(tactic| rfl) },
    { label := "decide", tactic := ← `(tactic| decide) }]

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

private theorem boolXorPos1 (left right : Bool) :
    ¬((left ^^ right) = true) ∨ left = true ∨ right = true := by
  cases left <;> cases right <;> decide

private theorem boolXorPos2 (left right : Bool) :
    ¬((left ^^ right) = true) ∨ ¬(left = true) ∨ ¬(right = true) := by
  cases left <;> cases right <;> decide

private theorem boolXorNeg1 (left right : Bool) :
    (left ^^ right) = true ∨ left = true ∨ ¬(right = true) := by
  cases left <;> cases right <;> decide

private theorem boolXorNeg2 (left right : Bool) :
    (left ^^ right) = true ∨ ¬(left = true) ∨ right = true := by
  cases left <;> cases right <;> decide

private theorem iffPos1 (left right : Prop) :
    ¬(left ↔ right) ∨ left ∨ ¬right := by grind

private theorem iffPos2 (left right : Prop) :
    ¬(left ↔ right) ∨ ¬left ∨ right := by grind

private theorem iffNeg1 (left right : Prop) :
    (left ↔ right) ∨ ¬left ∨ ¬right := by grind

private theorem iffNeg2 (left right : Prop) :
    (left ↔ right) ∨ left ∨ right := by grind

private theorem boolEqPos1 (left right : Bool) :
    ¬(left = right) ∨ left = true ∨ ¬(right = true) := by
  cases left <;> cases right <;> decide

private theorem boolEqPos2 (left right : Bool) :
    ¬(left = right) ∨ ¬(left = true) ∨ right = true := by
  cases left <;> cases right <;> decide

private theorem boolEqNeg1 (left right : Bool) :
    left = right ∨ ¬(left = true) ∨ ¬(right = true) := by
  cases left <;> cases right <;> decide

private theorem boolEqNeg2 (left right : Bool) :
    left = right ∨ left = true ∨ right = true := by
  cases left <;> cases right <;> decide

private theorem impliesClause (left right : Prop) :
    ¬(left → right) ∨ ¬left ∨ right := by grind

private theorem impliesNeg1Clause (left right : Prop) :
    (left → right) ∨ left := by grind

private theorem impliesNeg2Clause (left right : Prop) :
    (left → right) ∨ ¬right := by grind

private theorem implicationToClause {left right : Prop} (proof : left → right) :
    ¬left ∨ right := by grind

private def boolXorOperands? (literal : Expr) : Option (Expr × Expr) := do
  let atom := literal.not?.getD literal
  let some (carrier, left, right) := atom.eq? | none
  guard (carrier.isConstOf ``Bool)
  let xor ←
    if right.isConstOf ``Bool.true then some left
    else if left.isConstOf ``Bool.true then some right
    else none
  guard (xor.isAppOfArity ``Bool.xor 2)
  let args := xor.getAppArgs
  return (args[0]!, args[1]!)

private def proveBoolClause? (theoremName : Name) (target : Expr)
    (literals : Array Expr) : MetaM (Option Expr) := do
  let some (left, right) := literals.findSome? boolXorOperands? | return none
  let proof := mkApp2 (mkConst theoremName) left right
  if (← inferType proof).consumeMData == target.consumeMData then
    return some proof
  return none

private def boolXorTheorem? : String → Option Name
  | "xor_pos1" => some ``boolXorPos1
  | "xor_pos2" => some ``boolXorPos2
  | "xor_neg1" => some ``boolXorNeg1
  | "xor_neg2" => some ``boolXorNeg2
  | _ => none

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

private theorem intAbsEq (left right : Int) :
    intAbs left = intAbs right ↔ left = right ∨ left = -right := by
  unfold intAbs
  by_cases hl : left < 0 <;> by_cases hr : right < 0 <;>
    simp [hl, hr] <;> omega

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
  (la_mult_abs_comparison ..) => by grind [intAbs]
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

private def protocolHint? (rule : String) : CoreM (Option ReplayTactic) := do
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

private structure StepProof where
  proof : Expr
  method : String

/-- Prove `target` from the proofs in `premises`, trying the rule's hinted tactic first.

Builds the implication `p₁ → … → pₙ → target`, abstracts exactly its free variables,
proves the resulting closed proposition in an empty context, then applies it to those
variables and the premise proofs. Thus a step tactic cannot inspect any ambient declaration
that is absent from the step itself. -/
private def proveStepCore (target : Expr) (premises : Array Expr) (rule : String)
    (_args : Array Sexp := #[]) :
    TacticM (Option StepProof) := do
  let hypTypes ← premises.mapM fun p => do instantiateMVars (← inferType p)
  let impl := hypTypes.foldr (fun ty acc => mkForall `h .default ty acc) target
  let stepParams ← collectProofParams #[impl]
  let closedImpl ← instantiateMVars (← mkForallFVars stepParams impl)
  let hint ← protocolHint? rule
  let hinted := match hint with | some tactic => #[tactic] | none => #[]
  let fallbacks ← stepTactics
  let tactics := hinted ++ fallbacks
  for candidate in tactics do
    let tactic := candidate.tactic
    let saved ← saveState
    try
      let mv ← withLCtx {} {} do mkFreshExprMVar closedImpl
      let gs ← Tactic.run mv.mvarId! <|
        Tactic.withSuppressedMessages <|
          Tactic.withoutRecover (evalTactic
            (← `(tactic| (intros; $tactic))))
      if gs.isEmpty then
        let assigned ← instantiateMVars mv
        let proof := mkAppN (mkAppN assigned stepParams) premises
        let proof ← validateProofCandidate target proof
        return some { proof, method := candidate.label }
      restoreState saved
    catch _ =>
      restoreState saved
  return none

private def proveStep (target : Expr) (premises : Array Expr) (rule : String)
    (args : Array Sexp := #[]) :
    TacticM (Option Expr) :=
  return (← proveStepCore target premises rule args).map (·.proof)

private abbrev ClauseProof := Crush.ReplayClause

private def unitClauseProof (proof : Expr) : MetaM ClauseProof := do
  let clause ← instantiateMVars (← inferType proof)
  return { proof, clause, literals := #[clause] }

private structure ResolutionCandidate where
  left : Nat
  right : Nat
  leftPivot : Nat
  rightPivot : Nat
  result : Array Expr
  score : Nat

private structure BinaryResolutionCandidate where
  leftPivot : Nat
  rightPivot : Nat
  result : Array Expr
  score : Nat

private def wideResolutionThreshold : Nat := 8

private def premiseReferenceCounts (commands : Array Command) :
    Std.HashMap String Nat := Id.run do
  let mut counts : Std.HashMap String Nat := {}
  for command in commands do
    if let .step _ _ _ premises _ _ := command then
      for premise in premises do
        counts := counts.insert premise (counts.getD premise 0 + 1)
  return counts

private def mkClause (literals : Array Expr) : MetaM Expr := do
  if literals.isEmpty then return mkConst ``False
  let mut clause := literals.back!
  for i in [1:literals.size] do
    clause ← mkAppM ``Or #[literals[literals.size - 1 - i]!, clause]
  return clause

private partial def sameLiteral (left right : Expr) (fuel : Nat := 16) : MetaM Bool := do
  let left := left.consumeMData
  let right := right.consumeMData
  if left == right then return true
  if fuel == 0 then return false
  let left ← whnf left
  let right ← whnf right
  if left.consumeMData == right.consumeMData then return true
  match left.consumeMData, right.consumeMData with
  | .app .., .app .. =>
    let leftArgs := left.getAppArgs
    let rightArgs := right.getAppArgs
    unless leftArgs.size == rightArgs.size &&
        left.getAppFn.consumeMData == right.getAppFn.consumeMData do
      return false
    for i in [:leftArgs.size] do
      unless ← sameLiteral leftArgs[i]! rightArgs[i]! (fuel - 1) do
        return false
    return true
  | .forallE _ leftDomain leftBody _, .forallE _ rightDomain rightBody _ =>
    unless ← sameLiteral leftDomain rightDomain (fuel - 1) do
      return false
    if leftBody.consumeMData == rightBody.consumeMData then return true
    withLocalDeclD `x leftDomain fun x =>
      sameLiteral (leftBody.instantiate1 x) (rightBody.instantiate1 x) (fuel - 1)
  | _, _ => return false

private def complementary (left right : Expr) : MetaM Bool := do
  if left.isAppOfArity ``Not 1 then
    if ← sameLiteral left.getAppArgs[0]! right then return true
  if right.isAppOfArity ``Not 1 then
    return ← sameLiteral left right.getAppArgs[0]!
  return false

private def contradictionProof? (left leftProof right rightProof : Expr) :
    MetaM (Option Expr) := do
  if left.isAppOfArity ``Not 1 then
    if ← sameLiteral left.getAppArgs[0]! right then
      return some (mkApp leftProof rightProof)
  if right.isAppOfArity ``Not 1 then
    if ← sameLiteral left right.getAppArgs[0]! then
      return some (mkApp rightProof leftProof)
  return none

private def containsLiteral (literals : Array Expr) (literal : Expr) : MetaM Bool := do
  for existing in literals do
    if ← sameLiteral existing literal then return true
  return false

private def insertLiteral (literals : Array Expr) (literal : Expr) : MetaM (Array Expr) := do
  if ← containsLiteral literals literal then return literals
  return literals.push literal

private def resolveAt (left right : Array Expr) (leftIndex rightIndex : Nat) :
    MetaM (Array Expr) := do
  let mut result := #[]
  for i in [:left.size] do
    unless i == leftIndex do
      result ← insertLiteral result left[i]!
  for i in [:right.size] do
    unless i == rightIndex do
      result ← insertLiteral result right[i]!
  return result

private def clauseSubset (left right : Array Expr) : MetaM Bool := do
  for literal in left do
    unless ← containsLiteral right literal do return false
  return true

/-- Inject a proof of one literal into a right-associated clause containing it. -/
private partial def injectLiteral (target : Expr) (targetLiterals : Array Expr)
    (literal proof : Expr) : MetaM (Option Expr) := do
  let some first := targetLiterals[0]? | return none
  if targetLiterals.size == 1 then
    if ← sameLiteral literal first then return some proof
    return none
  let target := target.consumeMData
  unless target.isAppOfArity ``Or 2 do return none
  let left := target.getAppArgs[0]!
  let right := target.getAppArgs[1]!
  if ← sameLiteral literal first then
    return some (mkApp3 (mkConst ``Or.inl) left right proof)
  let some rightProof ←
      injectLiteral right (targetLiterals.extract 1 targetLiterals.size) literal proof
    | return none
  return some (mkApp3 (mkConst ``Or.inr) left right rightProof)

private partial def projectConjunct? (conjunction proof literal : Expr) :
    MetaM (Option Expr) := do
  if ← sameLiteral conjunction literal then return some proof
  let conjunction := conjunction.consumeMData
  unless conjunction.isAppOfArity ``And 2 do return none
  let left := conjunction.getAppArgs[0]!
  let right := conjunction.getAppArgs[1]!
  let leftProof := mkApp3 (mkConst ``And.left) left right proof
  if let some result ← projectConjunct? left leftProof literal then
    return some result
  let rightProof := mkApp3 (mkConst ``And.right) left right proof
  projectConjunct? right rightProof literal

private partial def injectProposition? (target proposition proof : Expr) :
    MetaM (Option Expr) := do
  if ← sameLiteral target proposition then return some proof
  let target := target.consumeMData
  unless target.isAppOfArity ``Or 2 do return none
  let left := target.getAppArgs[0]!
  let right := target.getAppArgs[1]!
  if let some leftProof ← injectProposition? left proposition proof then
    return some (mkApp3 (mkConst ``Or.inl) left right leftProof)
  let some rightProof ← injectProposition? right proposition proof | return none
  return some (mkApp3 (mkConst ``Or.inr) left right rightProof)

private def excludedMiddleClause? (antecedent target : Expr)
    (positive : Expr → MetaM (Option (Expr × Expr))) : MetaM (Option Expr) := do
  let notAntecedent ← mkAppM ``Not #[antecedent]
  let positiveBranch? ← withLocalDeclD `hpos antecedent fun hpos => do
    let some (proposition, proof) ← positive hpos | return none
    let some result ← injectProposition? target proposition proof | return none
    return some (← mkLambdaFVars #[hpos] result)
  let some positiveBranch := positiveBranch? | return none
  let negativeBranch? ← withLocalDeclD `hneg notAntecedent fun hneg => do
    let some result ← injectProposition? target notAntecedent hneg | return none
    return some (← mkLambdaFVars #[hneg] result)
  let some negativeBranch := negativeBranch? | return none
  let cases ← mkAppM ``Classical.em #[antecedent]
  return some (mkApp6 (mkConst ``Or.elim)
    antecedent notAntecedent target cases positiveBranch negativeBranch)

private def casesProposition? (proposition target : Expr)
    (positive negative : Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  let negation ← mkAppM ``Not #[proposition]
  let positiveBranch? ← withLocalDeclD `hpos proposition fun proof => do
    let some result ← positive proof | return none
    return some (← mkLambdaFVars #[proof] result)
  let some positiveBranch := positiveBranch? | return none
  let negativeBranch? ← withLocalDeclD `hneg negation fun proof => do
    let some result ← negative proof | return none
    return some (← mkLambdaFVars #[proof] result)
  let some negativeBranch := negativeBranch? | return none
  let cases ← mkAppM ``Classical.em #[proposition]
  return some (mkApp6 (mkConst ``Or.elim)
    proposition negation target cases positiveBranch negativeBranch)

private def iffRuleTheorems? : String → Option (Name × Name × Bool)
  | "equiv_pos1" => some (``iffPos1, ``boolEqPos1, true)
  | "equiv_pos2" => some (``iffPos2, ``boolEqPos2, true)
  | "equiv_neg1" => some (``iffNeg1, ``boolEqNeg1, false)
  | "equiv_neg2" => some (``iffNeg2, ``boolEqNeg2, false)
  | _ => none

private def proveIffRuleClause? (rule : String) (target : Expr)
    (literals : Array Expr) : MetaM (Option Expr) := do
  let some (propTheorem, boolTheorem, negated) := iffRuleTheorems? rule
    | return none
  for literal in literals do
    let literal := literal.consumeMData
    let some atom := if negated then literal.not? else some literal | continue
    if let some (left, right) := atom.consumeMData.iff? then
      let proof := mkApp2 (mkConst propTheorem) left right
      if (← inferType proof).consumeMData == target.consumeMData then
        return some proof
    if let some (carrier, left, right) := atom.consumeMData.eq? then
      if carrier.isConstOf ``Bool then
        let proof := mkApp2 (mkConst boolTheorem) left right
        if (← inferType proof).consumeMData == target.consumeMData then
          return some proof
  return none

private def implicationRuleTheorem? : String → Option (Name × Bool)
  | "implies" => some (``impliesClause, true)
  | "implies_neg1" => some (``impliesNeg1Clause, false)
  | "implies_neg2" => some (``impliesNeg2Clause, false)
  | _ => none

private def proveImplicationRuleClause? (rule : String) (target : Expr)
    (literals : Array Expr) : MetaM (Option Expr) := do
  let some (theoremName, negated) := implicationRuleTheorem? rule | return none
  for literal in literals do
    let literal := literal.consumeMData
    let some implication := if negated then literal.not? else some literal | continue
    let .forallE _ left right _ := implication.consumeMData | continue
    if right.hasLooseBVars then continue
    let proof := mkApp2 (mkConst theoremName) left right
    if (← inferType proof).consumeMData == target.consumeMData then
      return some proof
  return none

private def proveImplicationPremiseClause? (target : Expr)
    (premise : ClauseProof) : MetaM (Option Expr) := do
  let .forallE _ _ body _ := premise.clause.consumeMData | return none
  if body.hasLooseBVars then return none
  let proof ← mkAppM ``implicationToClause #[premise.proof]
  if (← inferType proof).consumeMData == target.consumeMData then return some proof
  return none

private partial def conjunctionLeaves (proposition : Expr) : Array Expr :=
  let proposition := proposition.consumeMData
  if proposition.isAppOfArity ``And 2 then
    conjunctionLeaves proposition.getAppArgs[0]! ++
      conjunctionLeaves proposition.getAppArgs[1]!
  else
    #[proposition]

private partial def buildConjunctionProof (proposition : Expr)
    (leaves proofs : Array Expr) (index : Nat := 0) :
    MetaM (Option (Expr × Nat)) := do
  let proposition := proposition.consumeMData
  if proposition.isAppOfArity ``And 2 then
    let left := proposition.getAppArgs[0]!
    let right := proposition.getAppArgs[1]!
    let some (leftProof, next) ← buildConjunctionProof left leaves proofs index
      | return none
    let some (rightProof, next) ← buildConjunctionProof right leaves proofs next
      | return none
    return some (mkApp4 (mkConst ``And.intro) left right leftProof rightProof, next)
  let some leaf := leaves[index]? | return none
  let some proof := proofs[index]? | return none
  unless ← sameLiteral proposition leaf do return none
  return some (proof, index + 1)

private def proveConjunctionTautologyClause? (target : Expr) (literals : Array Expr) :
    MetaM (Option Expr) := do
  for conjunction in literals do
    let leaves := conjunctionLeaves conjunction
    unless leaves.size > 1 do continue
    let rec proveLeaves : Nat → Nat → Array Expr → MetaM (Option Expr)
      | 0, _, proofs => do
        let some (proof, _) ← buildConjunctionProof conjunction leaves proofs
          | return none
        return ← injectLiteral target literals conjunction proof
      | remaining + 1, index, proofs => do
        let some leaf := leaves[index]? | return none
        casesProposition? leaf target
          (fun proof => proveLeaves remaining (index + 1) (proofs.push proof))
          (fun proof => do
            let negation ← mkAppM ``Not #[leaf]
            injectLiteral target literals negation proof)
    if let some proof ← proveLeaves leaves.size 0 #[] then return some proof
  return none

private def proveNotAndClause? (target : Expr) (targetLiterals : Array Expr)
    (premise : ClauseProof) : MetaM (Option Expr) := do
  let premiseClause := premise.clause.consumeMData
  unless premiseClause.isAppOfArity ``Not 1 do return none
  let conjunction := premiseClause.getAppArgs[0]!
  let leaves := conjunctionLeaves conjunction
  unless leaves.size > 1 do return none
  let rec proveLeaves : Nat → Nat → Array Expr → MetaM (Option Expr)
    | 0, _, proofs => do
      let some (conjunctionProof, _) ← buildConjunctionProof conjunction leaves proofs
        | return none
      let falseProof := mkApp premise.proof conjunctionProof
      return some (mkApp2 (mkConst ``False.elim [Level.zero]) target falseProof)
    | remaining + 1, index, proofs => do
      let some leaf := leaves[index]? | return none
      casesProposition? leaf target
        (fun proof => proveLeaves remaining (index + 1) (proofs.push proof))
        (fun proof => do
          let negation ← mkAppM ``Not #[leaf]
          injectLiteral target targetLiterals negation proof)
  proveLeaves leaves.size 0 #[]

private partial def buildConjunctionFromPremises (proposition : Expr)
    (premises : Array ClauseProof) (index : Nat := 0) :
    MetaM (Option (Expr × Nat)) := do
  if let some premise := premises[index]? then
    if proposition.consumeMData == premise.clause.consumeMData then
      return some (premise.proof, index + 1)
  let proposition := proposition.consumeMData
  unless proposition.isAppOfArity ``And 2 do return none
  let left := proposition.getAppArgs[0]!
  let right := proposition.getAppArgs[1]!
  let some (leftProof, next) ← buildConjunctionFromPremises left premises index
    | return none
  let some (rightProof, next) ← buildConjunctionFromPremises right premises next
    | return none
  return some (mkApp4 (mkConst ``And.intro) left right leftProof rightProof, next)

private def proveAndIntroStep? (target : Expr) (targetLiterals : Array Expr)
    (premises : Array ClauseProof) : MetaM (Option Expr) := do
  unless targetLiterals.size == 1 && !premises.isEmpty do return none
  let conjunction := targetLiterals[0]!
  let some (proof, next) ←
      buildConjunctionFromPremises conjunction premises
    | return none
  unless next == premises.size do return none
  if (← inferType proof).consumeMData == target.consumeMData then return some proof
  return none

private def proveReflexiveClause? (target : Expr) : MetaM (Option Expr) := do
  if let some (left, right) := target.iff? then
    unless ← sameLiteral left right do return none
    let forward ← withLocalDeclD `h left fun proof => mkLambdaFVars #[proof] proof
    let backward ← withLocalDeclD `h right fun proof => mkLambdaFVars #[proof] proof
    return some (mkApp4 (mkConst ``Iff.intro) left right forward backward)
  if let some (carrier, left, right) := target.eq? then
    unless ← sameLiteral left right do return none
    let level ← getLevel carrier
    return some (mkApp2 (mkConst ``Eq.refl [level]) carrier left)
  return none

private def proveProjectionClause? (target : Expr) (targetLiterals : Array Expr) :
    MetaM (Option Expr) := do
  for negative in targetLiterals do
    let negative := negative.consumeMData
    unless negative.isAppOfArity ``Not 1 do continue
    let antecedent := negative.getAppArgs[0]!
    let proof? ← excludedMiddleClause? antecedent target fun hpos => do
      for literal in targetLiterals do
        if let some proof ← projectConjunct? antecedent hpos literal then
          return some (literal, proof)
      return some (antecedent, hpos)
    if let some proof := proof? then return some proof
  return none

private def proveIffClause? (target : Expr) (premise : ClauseProof) :
    MetaM (Option Expr) := do
  let some (left, right) := premise.clause.iff? | return none
  let forward? ← excludedMiddleClause? left target fun hleft =>
    return some (right, mkApp4 (mkConst ``Iff.mp) left right premise.proof hleft)
  if let some proof := forward? then return some proof
  excludedMiddleClause? right target fun hright =>
    return some (left, mkApp4 (mkConst ``Iff.mpr) left right premise.proof hright)

/-- Eliminate the exact top-level literals of a right-associated clause. -/
private partial def eliminateClause (clause : Expr) (literals : Array Expr)
    (proof target : Expr)
    (onLiteral : Expr → Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  if literals.isEmpty then
    if clause.consumeMData.isConstOf ``False then
      return some (mkApp2 (mkConst ``False.elim [Level.zero]) target proof)
    return none
  if literals.size == 1 then
    return ← onLiteral literals[0]! proof
  let clause := clause.consumeMData
  unless clause.isAppOfArity ``Or 2 do return none
  let left := clause.getAppArgs[0]!
  let right := clause.getAppArgs[1]!
  let leftProof? ← withLocalDeclD `hleft left fun hleft => do
    let some result ← onLiteral literals[0]! hleft | return none
    return some (← mkLambdaFVars #[hleft] result)
  let some leftProof := leftProof? | return none
  let rightProof? ← withLocalDeclD `hright right fun hright => do
    let some result ← eliminateClause right
        (literals.extract 1 literals.size) hright target onLiteral
      | return none
    return some (← mkLambdaFVars #[hright] result)
  let some rightProof := rightProof? | return none
  return some (mkApp6 (mkConst ``Or.elim) left right target proof leftProof rightProof)

/-- Weaken a clause by reordering its literals or adding alternatives. -/
private def weakenClause (source : Expr) (sourceLiterals : Array Expr) (proof : Expr)
    (target : Expr) (targetLiterals : Array Expr) : MetaM (Option Expr) := do
  eliminateClause source sourceLiterals proof target fun literal literalProof =>
    injectLiteral target targetLiterals literal literalProof

/-- Construct one binary propositional-resolution proof without invoking a tactic. -/
private def resolveClauses (leftClause : Expr) (leftLiterals : Array Expr)
    (rightClause : Expr) (rightLiterals : Array Expr)
    (target : Expr) (targetLiterals : Array Expr) (leftProof rightProof
    leftPivot rightPivot : Expr) : MetaM (Option Expr) := do
  eliminateClause leftClause leftLiterals leftProof target
      fun leftLiteral leftLiteralProof => do
    if ← sameLiteral leftLiteral leftPivot then
      eliminateClause rightClause rightLiterals rightProof target
          fun rightLiteral rightLiteralProof => do
        if ← sameLiteral rightLiteral rightPivot then
          let some falseProof ← contradictionProof?
              leftLiteral leftLiteralProof rightLiteral rightLiteralProof
            | return none
          return some (mkApp2 (mkConst ``False.elim [Level.zero]) target falseProof)
        injectLiteral target targetLiterals rightLiteral rightLiteralProof
    else
      injectLiteral target targetLiterals leftLiteral leftLiteralProof

private def bestBinaryResolution? (left right target : Array Expr) :
    MetaM (Option BinaryResolutionCandidate) := do
  let mut best : Option BinaryResolutionCandidate := none
  for leftIndex in [:left.size] do
    for rightIndex in [:right.size] do
      unless ← complementary left[leftIndex]! right[rightIndex]! do
        continue
      let result ← resolveAt left right leftIndex rightIndex
      let mut foreign := 0
      for literal in result do
        unless ← containsLiteral target literal do foreign := foreign + 1
      let candidate := {
        leftPivot := leftIndex
        rightPivot := rightIndex
        result
        score := foreign * 1024 + result.size
      }
      if best.all (candidate.score < ·.score) then
        best := some candidate
  return best

private def bestResolution? (pool : Array ClauseProof) (target : Array Expr) :
    MetaM (Option ResolutionCandidate) := do
  let mut best : Option ResolutionCandidate := none
  for i in [:pool.size] do
    for j in [i + 1:pool.size] do
      let some binary ← bestBinaryResolution?
          pool[i]!.literals pool[j]!.literals target | continue
      let candidate := {
        left := i
        right := j
        leftPivot := binary.leftPivot
        rightPivot := binary.rightPivot
        result := binary.result
        score := binary.score
      }
      if best.all (candidate.score < ·.score) then
        best := some candidate
  return best

private def weakenClauseProof? (target : Expr) (targetLiterals : Array Expr)
    (entry : ClauseProof) :
    TacticM (Option Expr) := do
  unless ← clauseSubset entry.literals targetLiterals do return none
  let some proof ← weakenClause entry.clause entry.literals entry.proof
      target targetLiterals | return none
  return some proof

/-- Resolve premises in certificate order when cvc5 emits a linear resolution node. -/
private def proveOrderedResolutionStep? (target : Expr)
    (targetLiterals : Array Expr) (premises : Array ClauseProof) :
    TacticM (Option Expr) := do
  let some first := premises[0]? | return none
  let mut current := first
  if let some proof ← weakenClauseProof? target targetLiterals current then
    return some proof
  for i in [1:premises.size] do
    let next := premises[i]!
    let some candidate ←
        bestBinaryResolution? current.literals next.literals targetLiterals
      | return none
    let intermediate ← mkClause candidate.result
    let some proof ← resolveClauses current.clause current.literals
        next.clause next.literals intermediate candidate.result current.proof next.proof
        current.literals[candidate.leftPivot]! next.literals[candidate.rightPivot]!
      | return none
    current := { proof, clause := intermediate, literals := candidate.result }
    if let some proof ← weakenClauseProof? target targetLiterals current then
      return some proof
  return none

/-- Replay a resolution node structurally when its clause graph is small or linear. -/
private def proveResolutionStep (target : Expr) (targetLiterals : Array Expr)
    (premises : Array ClauseProof) :
    TacticM (Option Expr) := do
  let mut pool := premises
  if pool.size >= wideResolutionThreshold then
    if let some proof ←
        proveOrderedResolutionStep? target targetLiterals pool then
      return some proof
    return none
  while !pool.isEmpty do
    for entry in pool do
      if let some proof ← weakenClauseProof? target targetLiterals entry then
        return some proof
    if pool.size < 2 then break
    let some candidate ← bestResolution? pool targetLiterals | break
    let intermediate ← mkClause candidate.result
    let left := pool[candidate.left]!
    let right := pool[candidate.right]!
    let some proof ← resolveClauses left.clause left.literals right.clause right.literals
        intermediate candidate.result left.proof right.proof
        left.literals[candidate.leftPivot]! right.literals[candidate.rightPivot]!
      | break
    let mut next := #[]
    for i in [:pool.size] do
      unless i == candidate.left || i == candidate.right do
        next := next.push pool[i]!
    pool := next.push { proof, clause := intermediate, literals := candidate.result }
  return none

/-- Replay a clause permutation or contraction by structural weakening. -/
private def proveWeakeningStep (target : Expr) (targetLiterals : Array Expr)
    (premise : ClauseProof) : MetaM (Option Expr) :=
  weakenClause premise.clause premise.literals premise.proof
    target targetLiterals

private structure RelationView where
  isIff : Bool
  carrier : Expr
  left : Expr
  right : Expr
  deriving Inhabited

private structure RelationProof where
  view : RelationView
  proof : Expr
  deriving Inhabited

private def relationView? (type : Expr) : Option RelationView :=
  if let some (left, right) := type.iff? then
    some { isIff := true, carrier := mkSort .zero, left, right }
  else if let some (carrier, left, right) := type.eq? then
    some { isIff := false, carrier, left, right }
  else
    none

private def relationProof? (entry : ClauseProof) : Option RelationProof :=
  (relationView? entry.clause).map fun view => { view, proof := entry.proof }

private def reverseRelation (relation : RelationProof) : MetaM RelationProof := do
  let view := relation.view
  let proof ←
    if view.isIff then
      pure (mkApp3 (mkConst ``Iff.symm) view.left view.right relation.proof)
    else
      let level ← getLevel view.carrier
      pure (mkApp4 (mkConst ``Eq.symm [level])
        view.carrier view.left view.right relation.proof)
  return {
    view := { view with left := view.right, right := view.left }
    proof
  }

private def composeRelations (left right : RelationProof) :
    MetaM (Option RelationProof) := do
  unless left.view.isIff == right.view.isIff do return none
  unless ← sameLiteral left.view.right right.view.left do return none
  unless left.view.isIff || (← sameLiteral left.view.carrier right.view.carrier) do
    return none
  let proof ←
    if left.view.isIff then
      pure (mkApp5 (mkConst ``Iff.trans)
        left.view.left left.view.right right.view.right left.proof right.proof)
    else
      let level ← getLevel left.view.carrier
      pure (mkApp6 (mkConst ``Eq.trans [level])
        left.view.carrier left.view.left left.view.right right.view.right
        left.proof right.proof)
  return some {
    view := { left.view with right := right.view.right }
    proof
  }

private def relationAsEquality (relation : RelationProof) :
    MetaM RelationProof := do
  if !relation.view.isIff then return relation
  return {
    view := {
      isIff := false
      carrier := mkSort .zero
      left := relation.view.left
      right := relation.view.right
    }
    proof := mkApp3 (mkConst ``propext)
      relation.view.left relation.view.right relation.proof
  }

private def sameCongruenceTerm (left right : Expr) : Bool :=
  left.consumeMData == right.consumeMData

private partial def synthesizeCongruenceEquality
    (left right : Expr) (relations : Array RelationProof)
    (fuel : Nat := 64) : MetaM (Option Expr) := do
  let left := left.consumeMData
  let right := right.consumeMData
  if sameCongruenceTerm left right then
    return some (← mkEqRefl left)
  for relation in relations do
    if sameCongruenceTerm left relation.view.left &&
        sameCongruenceTerm right relation.view.right then
      return some relation.proof
    if sameCongruenceTerm left relation.view.right &&
        sameCongruenceTerm right relation.view.left then
      return some (← reverseRelation relation).proof
  if fuel == 0 then return none
  let .app leftFn leftArg := left | return none
  let .app rightFn rightArg := right | return none
  let some functionProof ←
      synthesizeCongruenceEquality leftFn rightFn relations (fuel - 1)
    | return none
  let some argumentProof ←
      synthesizeCongruenceEquality leftArg rightArg relations (fuel - 1)
    | return none
  try
    return some (← mkCongr functionProof argumentProof)
  catch _ =>
    return none

private def proveCongruenceStep? (target : Expr)
    (premises : Array ClauseProof) : MetaM (Option Expr) := do
  let some targetView := relationView? target | return none
  let mut relations := #[]
  for premise in premises do
    let some relation := relationProof? premise | return none
    relations := relations.push (← relationAsEquality relation)
  let some equality ← synthesizeCongruenceEquality
      targetView.left targetView.right relations
    | return none
  if targetView.isIff then
    return some (mkApp3 (mkConst ``Eq.to_iff)
      targetView.left targetView.right equality)
  return some equality

private def proveTransStep? (target : Expr) (premises : Array ClauseProof) :
    MetaM (Option Expr) := do
  let some targetView := relationView? target | return none
  let mut relations := #[]
  let mut allRelations := #[]
  for premise in premises do
    let some relation := relationProof? premise | return none
    allRelations := allRelations.push relation
    unless sameCongruenceTerm relation.view.left relation.view.right do
      relations := relations.push relation
  if relations.isEmpty then relations := allRelations
  let some first := relations[0]? | return none
  let mut current := first
  for i in [1:relations.size] do
    let next := relations[i]!
    let next ←
      if ← sameLiteral current.view.right next.view.left then
        pure next
      else if ← sameLiteral current.view.right next.view.right then
        reverseRelation next
      else
        return none
    let some composed ← composeRelations current next | return none
    current := composed
  if current.view.isIff != targetView.isIff then return none
  if !targetView.isIff &&
      !(← sameLiteral current.view.carrier targetView.carrier) then
    return none
  if (← sameLiteral current.view.left targetView.left) &&
      (← sameLiteral current.view.right targetView.right) then
    return some current.proof
  if (← sameLiteral current.view.left targetView.right) &&
      (← sameLiteral current.view.right targetView.left) then
    return some (← reverseRelation current).proof
  return none

/-- Replay a parsed Alethe proof into a Lean proof of `False`.

`facts` maps a `crush_fact_<n>` assumption id to the Lean proof of that hypothesis (from
`TranslateState.facts`); `symbols` is the emitted-symbol → Lean-term map. -/
partial def replay (proof : AletheProof) (rawSexps : Array Sexp)
    (facts : Std.HashMap String Expr) (symbols : Std.HashMap String Expr) :
    TacticM (Except ReplayFailure Expr) := do
  -- Collected from the *unstripped* text: the parser drops the annotations, which is
  -- exactly what `@p_k` references need.
  let named := rawSexps.foldl (fun acc s => collectNamed s acc) {}
  let decoders ← getReplayTermHandlers
  let replayRules ← getReplayRuleHandlers
  let ctx : TermCtx := { symbols, named, decoders }
  let failureRef ← IO.mkRef none
  let telemetry ← ReplayTelemetrySession.start
  let referenceCounts := premiseReferenceCounts proof.commands
  let result ← go failureRef telemetry ctx replayRules facts proof.commands
    referenceCounts 0 {} #[]
  telemetry.report proof.commands.size result.isSome
  match result with
  | some proof => return .ok proof
  | none =>
    let failure ← failureRef.get
    return .error (failure.getD {
      kind := .malformedCertificate
      detail := "certificate contains no replayable empty clause" })
where
  /-- Replay `cmds` from index `i` under proof environment `env`, returning the proof of the
  first empty clause reached. -/
  go (failureRef : ReplayFailureRef) (telemetry : ReplayTelemetrySession) (ctx : TermCtx)
      (replayRules : ReplayRuleRegistry)
      (facts : Std.HashMap String Expr) (cmds : Array Command)
      (referenceCounts : Std.HashMap String Nat)
      (i : Nat) (env : Std.HashMap String ClauseProof) (scopedProofs : Array Expr) :
      TacticM (Option Expr) := do
    let mut i := i
    let mut env := env
    while h : i < cmds.size do
      match cmds[i] with
      | .assume id term =>
        -- A top-level assumption is one of our asserted facts, so its Lean proof is already
        -- in hand. Decode its asserted SMT formula and check the semantic bridge from the
        -- source fact before adding it to the clause environment. Unnamed encoding axioms
        -- are accepted only when Lean can prove their translated statement in an empty
        -- context; an unused, untranslatable axiom may be skipped because no later step can
        -- consume it without a proof.
        match facts.get? id with
        | some sourceProof =>
          let some target ← toExpr? ctx 64 term
            | rememberFailure failureRef {
                kind := .termGap
                stepId := some id
                term := some term
                detail := "selected SMT assumption could not be decoded" }
              return none
          let target ← replayToProp target
          let sourceType ← instantiateMVars (← inferType sourceProof)
          let proof? ←
            if ← isDefEqGuarded sourceType target then
              pure (some sourceProof)
            else
              proveStep target #[sourceProof] "assume"
          let some proof := proof?
            | trace[crush.result] "alethe replay: assumption bridge failed at {id}; \
                source: {sourceType}; target: {target}"
              rememberFailure failureRef {
                kind := .ruleGap
                stepId := some id
                term := some term
                detail := "decoded SMT assumption was not derivable from its Lean source fact" }
              return none
          let proof := mkApp2 (mkConst ``id [Level.zero]) target proof
          env := env.insert id { proof, clause := target, literals := #[target] }
        | none =>
          match ← toExpr? ctx 64 term with
          | some target =>
            let target ← replayToProp target
            if let some proof ←
                (proveStep target #[] "assume" : TacticM (Option Expr)) then
              env := env.insert id (← unitClauseProof proof)
            else
              trace[crush.result] "alethe replay: skipped unproved encoding assumption {id}"
          | none =>
            trace[crush.result] "alethe replay: skipped untranslatable encoding \
                                 assumption {id}"
        i := i + 1
      | .anchor .. =>
        let some (stepId, pf, next) ←
            replayAnchor failureRef telemetry ctx replayRules facts cmds
              referenceCounts i env scopedProofs
          | return none
        env := env.insert stepId pf
        if pf.literals.isEmpty then
          trace[crush.result] "alethe replay: succeeded at {stepId}"
          return some pf.proof
        i := next
      | .step id clause rule premises args _ =>
        let some pf ←
            replayStep failureRef telemetry ctx replayRules referenceCounts env scopedProofs
              id clause rule premises args
          | return none
        env := env.insert id pf
        -- The empty clause is `False`: the refutation is complete.
        if clause.isEmpty then
          trace[crush.result] "alethe replay: succeeded at {id}"
          return some pf.proof
        i := i + 1
    trace[crush.result] "alethe replay: declined (no empty-clause step)"
    rememberFailure failureRef {
      kind := .malformedCertificate
      detail := "certificate contains no empty-clause step" }
    return none

  /-- Replay one ordinary derived step from the proofs currently in scope. -/
  replayStep (failureRef : ReplayFailureRef) (telemetry : ReplayTelemetrySession)
      (ctx : TermCtx)
      (replayRules : ReplayRuleRegistry)
      (referenceCounts : Std.HashMap String Nat)
      (env : Std.HashMap String ClauseProof) (scopedProofs : Array Expr)
      (id : String)
      (clause : Array Sexp) (rule : String) (premises : Array String)
      (args : Array Sexp) : TacticM (Option ClauseProof) := do
    let started ← telemetry.mark
    let result ← replayStepCore failureRef telemetry ctx replayRules referenceCounts env
      scopedProofs id clause rule premises args
    let method := (result.map fun result => result.2).getD "failed"
    let elapsed ← telemetry.record id rule method result.isSome started
    if elapsed >= slowReplayTraceNanos then
      let targetExpr := (result.map fun replayed => replayed.1.clause).getD (mkConst ``False)
      let target := (toString (← ppExpr targetExpr)).replace "\n" " "
      let premiseClauses ← premises.filterMap (env.get? ·)
        |>.mapM fun premise =>
          return (toString (← ppExpr premise.clause)).replace "\n" " "
      let premiseIds := String.intercalate "," premises.toList
      trace[crush.replay] "slow replay step: id={id}, rule={rule}, method={method}, \
        elapsed_ns={elapsed}, premises=[{premiseIds}], target={target}, \
        premise_clauses={premiseClauses}, args={args}, clause={clause}"
    return result.map (fun result => result.1)

  replayStepCore (failureRef : ReplayFailureRef) (telemetry : ReplayTelemetrySession)
      (ctx : TermCtx)
      (replayRules : ReplayRuleRegistry)
      (referenceCounts : Std.HashMap String Nat)
      (env : Std.HashMap String ClauseProof) (scopedProofs : Array Expr)
      (id : String)
      (clause : Array Sexp) (rule : String) (premises : Array String)
      (args : Array Sexp) : TacticM (Option (ClauseProof × String)) := do
    let decodeStarted ← telemetry.mark
    let targetLiterals? ← clauseLiteralsToExprs? ctx 64 clause
    let some targetLiterals := targetLiterals?
      | trace[crush.result] "alethe replay: declined (untranslatable clause at {id}: \
                             {clause})"
        telemetry.recordPhase id rule "decode" decodeStarted
        rememberFailure failureRef {
          kind := .termGap
          stepId := some id
          rule := some rule
          term := some (clauseSexp clause)
          detail := "certificate clause could not be decoded as a Lean proposition" }
        return none
    let target ← mkClause targetLiterals
    telemetry.recordPhase id rule "decode" decodeStarted
    let mut premiseProofs : Array ClauseProof := #[]
    for premise in premises do
      let some pf := env.get? premise
        | trace[crush.result] "alethe replay: declined (missing premise {premise} of {id})"
          rememberFailure failureRef {
            kind := .malformedCertificate
            stepId := some id
            rule := some rule
            term := some (clauseSexp clause)
            detail := s!"referenced premise `{premise}` has no replayed proof" }
          return none
      premiseProofs := premiseProofs.push pf
    let prems := premiseProofs.map (·.proof)
    let replayContext : ReplayRuleContext := {
      stepId := id
      rule
      target
      targetLiterals
      premises := premiseProofs
      args
      scopedProofs
      decodeTerm := toExpr? ctx 64
      decodeSort := sortToType? ctx
      toProp := replayToProp
    }
    let dispatchStarted ← telemetry.mark
    let initialStructural : Option (Expr × String) ←
      if premiseProofs.isEmpty then
        if let some proof ← proveReflexiveClause? target then
          pure (some (proof, "structural:reflexivity"))
        else if let some theoremName := boolXorTheorem? rule then
          let proof? ← proveBoolClause? theoremName target targetLiterals
          pure (proof?.map fun proof : Expr => (proof, "structural:bool-xor"))
        else if rule == "equiv_pos1" || rule == "equiv_pos2" ||
            rule == "equiv_neg1" || rule == "equiv_neg2" then
          let proof? ← proveIffRuleClause? rule target targetLiterals
          pure (proof?.map fun proof : Expr => (proof, "structural:iff-clause"))
        else if rule == "implies" || rule == "implies_neg1" ||
            rule == "implies_neg2" then
          let proof? ← proveImplicationRuleClause? rule target targetLiterals
          pure (proof?.map fun proof : Expr => (proof, "structural:implies-clause"))
        else if rule == "and_neg" || rule == "and_intro" then
          let proof? ← proveConjunctionTautologyClause? target targetLiterals
          pure (proof?.map fun proof : Expr => (proof, "structural:and-tautology"))
        else if let some proof ← proveProjectionClause? target targetLiterals then
          pure (some (proof, "structural:projection"))
        else
          pure none
      else if premiseProofs.size == 1 then
        if rule == "implies" then
          let proof? ← proveImplicationPremiseClause? target premiseProofs[0]!
          pure (proof?.map fun proof : Expr => (proof, "structural:implies-elim"))
        else if rule == "not_and" then
          let proof? ← proveNotAndClause? target targetLiterals premiseProofs[0]!
          pure (proof?.map fun proof : Expr => (proof, "structural:not-and"))
        else
          let proof? ← proveIffClause? target premiseProofs[0]!
          pure (proof?.map fun proof : Expr => (proof, "structural:iff"))
      else
        pure none
    let structural : Option (Expr × String) ← match initialStructural with
    | some result => pure (some result)
    | none =>
      if rule == "and_intro" then
        let proof? ← proveAndIntroStep? target targetLiterals premiseProofs
        pure (proof?.map fun proof : Expr => (proof, "structural:and-intro"))
      else if rule == "cong" then
        let proof? ← proveCongruenceStep? target premiseProofs
        pure (proof?.map fun proof : Expr => (proof, "structural:congruence"))
      else if rule == "trans" then
        let proof? ← proveTransStep? target premiseProofs
        pure (proof?.map fun proof : Expr => (proof, "structural:transitivity"))
      else if rule == "resolution" && premiseProofs.size > 1 then
        let proof? ← proveResolutionStep target targetLiterals premiseProofs
        pure (proof?.map fun proof : Expr => (proof, "structural:resolution"))
      else if (rule == "reordering" || rule == "contraction") &&
          premiseProofs.size == 1 then
        let proof? ← proveWeakeningStep target targetLiterals premiseProofs[0]!
        pure (proof?.map fun proof : Expr => (proof, "structural:weakening"))
      else
        pure none
    let structuralProof : Option StepProof ← match structural with
    | some (proof, method) => do
      pure (some { proof := ← validateProofCandidate target proof, method })
    | none =>
      pure none
    let proof? : Option StepProof ← match structuralProof with
    | some proof => pure (some proof)
    | none =>
      let result? ← runReplayRuleHandlersDetailed replayRules replayContext
      pure (result?.map fun result => { proof := result.proof, method := result.source })
    let proof? ← match proof? with
    | some proof => pure (some proof)
    | none => proveStepCore target prems rule args
    let proof? ←
      match proof? with
      | some proof => pure (some proof)
      | none =>
        if scopedProofs.isEmpty then
          pure none
        else
          let result? ← proveStepCore target (prems ++ scopedProofs) rule args
          pure (result?.map fun result =>
            { result with method := result.method ++ ":scope" })
    let some replayed := proof?
      | let premiseTypes ← prems.mapM fun premise => inferType premise
        telemetry.recordPhase id rule "dispatch:failed" dispatchStarted
        trace[crush.replay] "replay declined at {id}: rule={rule}, args={args}"
        trace[crush.result] "alethe replay: declined (rule `{rule}` at {id} not \
                             replayed; args: {args}; target: {target}; \
                             premises: {premiseTypes})"
        rememberFailure failureRef {
          kind := .ruleGap
          stepId := some id
          rule := some rule
          term := some (clauseSexp clause)
          detail := "Lean could not prove this concrete inference from its replayed premises" }
        return none
    telemetry.recordPhase id rule s!"dispatch:{replayed.method}" dispatchStarted
    let pf := replayed.proof
    let pf ←
      if rule == "resolution" &&
          (referenceCounts.getD id 0 > 1 ||
            premiseProofs.size >= wideResolutionThreshold) then
        mkAuxTheorem target pf (zetaDelta := true)
          (kind? := some `crushAletheStep)
      else
        pure pf
    return some ({ proof := pf, clause := target, literals := targetLiterals }, replayed.method)

  /-- Replay an anchored subproof or binder congruence and return its closed proof. -/
  replayAnchor (failureRef : ReplayFailureRef) (telemetry : ReplayTelemetrySession)
      (ctx : TermCtx)
      (replayRules : ReplayRuleRegistry)
      (facts : Std.HashMap String Expr) (cmds : Array Command)
      (referenceCounts : Std.HashMap String Nat)
      (index : Nat) (env : Std.HashMap String ClauseProof) (scopedProofs : Array Expr) :
      TacticM (Option (String × ClauseProof × Nat)) := do
    let started ← telemetry.mark
    let (stepId, rule) :=
      match cmds[index]? with
      | some (.anchor stepId _) =>
        match findClose cmds (index + 1) stepId with
        | some close => match cmds[close]? with
          | some (.step _ _ rule _ _ _) => (stepId, rule)
          | _ => (stepId, "anchor")
        | none => (stepId, "anchor")
      | _ => (s!"command-{index}", "anchor")
    let result ← replayAnchorCore failureRef telemetry ctx replayRules facts cmds
      referenceCounts index env scopedProofs
    let _ ← telemetry.record stepId rule "anchor:inclusive" result.isSome started
    return result

  replayAnchorCore (failureRef : ReplayFailureRef) (telemetry : ReplayTelemetrySession)
      (ctx : TermCtx) (replayRules : ReplayRuleRegistry)
      (facts : Std.HashMap String Expr) (cmds : Array Command)
      (referenceCounts : Std.HashMap String Nat)
      (index : Nat) (env : Std.HashMap String ClauseProof) (scopedProofs : Array Expr) :
      TacticM (Option (String × ClauseProof × Nat)) := do
    let some (.anchor stepId anchorArgs) := cmds[index]?
      | rememberFailure failureRef {
          kind := .malformedCertificate
          detail := s!"command {index} was expected to be an anchor" }
        return none
    let some close := findClose cmds (index + 1) stepId
      | trace[crush.result] "alethe replay: declined (anchor {stepId} unclosed)"
        rememberFailure failureRef {
          kind := .malformedCertificate
          stepId := some stepId
          detail := "anchor has no matching closing step" }
        return none
    let .step _ closeClause closeRule _ _ discharge := cmds[close]!
      | trace[crush.result] "alethe replay: declined (invalid close for anchor {stepId})"
        rememberFailure failureRef {
          kind := .malformedCertificate
          stepId := some stepId
          detail := "anchor close is not an Alethe step" }
        return none
    let (assumptions, bodyStart) := collectAssumptions cmds (index + 1) close
    let some conclusionLiterals ← clauseLiteralsToExprs? ctx 64 closeClause
      | trace[crush.result] "alethe replay: declined (untranslatable anchored \
                             conclusion {stepId})"
        rememberFailure failureRef {
          kind := .termGap
          stepId := some stepId
          rule := some closeRule
          term := some (clauseSexp closeClause)
          detail := "anchored conclusion could not be decoded as a Lean proposition" }
        return none
    let conclusion ← mkClause conclusionLiterals
    let pf? ←
      if closeRule == "subproof" then
        let localIds := assumptions.map (·.1)
        unless discharge.size == localIds.size &&
            discharge.all localIds.contains && localIds.all discharge.contains do
          trace[crush.result] "alethe replay: declined (subproof {stepId} discharges \
                               {discharge}, but binds {localIds})"
          rememberFailure failureRef {
            kind := .malformedCertificate
            stepId := some stepId
            rule := some closeRule
            term := some (clauseSexp closeClause)
            detail := "subproof discharge list does not match its local assumptions" }
          return none
        let rec bindAssumptions (j : Nat) (innerEnv : Std.HashMap String ClauseProof)
            (locals : Array Expr) : TacticM (Option Expr) := do
          if h : j < assumptions.size then
            let (localId, localTerm) := assumptions[j]
            let some hypTy ← toExpr? ctx 64 localTerm
              | trace[crush.result] "alethe replay: declined (untranslatable local assume \
                                     {localId})"
                rememberFailure failureRef {
                  kind := .termGap
                  stepId := some localId
                  rule := some closeRule
                  term := some localTerm
                  detail := "local subproof assumption could not be decoded" }
                return none
            let hypTy ← replayToProp hypTy
            withLocalDeclD (`hsub ++ localId.toName) hypTy fun hlocal => do
              let localProof : ClauseProof :=
                { proof := hlocal, clause := hypTy, literals := #[hypTy] }
              bindAssumptions (j + 1) (innerEnv.insert localId localProof)
                (locals.push hlocal)
          else
            let some body ← goInner failureRef telemetry ctx replayRules facts cmds
                bodyStart close innerEnv referenceCounts (scopedProofs ++ locals)
              | trace[crush.result] "alethe replay: declined (subproof {stepId} body)"
                return none
            let implication ← mkLambdaFVars locals body
            proveStep conclusion (#[implication] ++ scopedProofs) "subproof"
        bindAssumptions 0 env #[]
      else if closeRule == "bind" then
        unless assumptions.isEmpty && discharge.isEmpty do
          trace[crush.result] "alethe replay: declined (bind anchor {stepId} has assumptions)"
          rememberFailure failureRef {
            kind := .malformedCertificate
            stepId := some stepId
            rule := some closeRule
            detail := "binder anchor unexpectedly contains local assumptions" }
          return none
        let binders := bindDeclarations anchorArgs
        if binders.isEmpty then
          trace[crush.result] "alethe replay: declined (bind anchor {stepId} has no binders)"
          rememberFailure failureRef {
            kind := .malformedCertificate
            stepId := some stepId
            rule := some closeRule
            detail := "binder anchor contains no binder declarations" }
          return none
        let rec bindVariables (j : Nat) (innerCtx : TermCtx)
            (locals : Array Expr) : TacticM (Option Expr) := do
          if h : j < binders.size then
            let (name, sort) := binders[j]
            let some type ← sortToType? innerCtx sort
              | trace[crush.result] "alethe replay: declined (unknown bind sort {sort})"
                rememberFailure failureRef {
                  kind := .termGap
                  stepId := some stepId
                  rule := some closeRule
                  term := some sort
                  detail := "binder sort could not be decoded as a Lean type" }
                return none
            withLocalDeclD name.toName type fun bound =>
              bindVariables (j + 1)
                { innerCtx with locals := innerCtx.locals.insert name bound }
                (locals.push bound)
          else
            applyAnchorAssignments failureRef innerCtx stepId closeRule anchorArgs
                fun assignedCtx => do
              let some body ←
                  goInner failureRef telemetry assignedCtx replayRules facts cmds
                    bodyStart close env referenceCounts scopedProofs
                | trace[crush.result] "alethe replay: declined (bind anchor {stepId} body)"
                  return none
              let generalized ← mkLambdaFVars locals body
              proveStep conclusion (#[generalized] ++ scopedProofs) "bind"
        bindVariables 0 ctx #[]
      else if closeRule == "sko_forall" || closeRule == "sko_ex" then
        unless assumptions.isEmpty && discharge.isEmpty do
          trace[crush.result] "alethe replay: declined ({closeRule} anchor {stepId} \
                               has assumptions)"
          rememberFailure failureRef {
            kind := .malformedCertificate
            stepId := some stepId
            rule := some closeRule
            detail := "Skolem anchor unexpectedly contains local assumptions" }
          return none
        let assignments := anchorAssignments anchorArgs
        if assignments.isEmpty then
          trace[crush.result] "alethe replay: declined ({closeRule} anchor {stepId} \
                               has no assignment)"
          rememberFailure failureRef {
            kind := .malformedCertificate
            stepId := some stepId
            rule := some closeRule
            detail := "Skolem anchor contains no assignment" }
          return none
        applyAnchorAssignments failureRef ctx stepId closeRule anchorArgs
            fun assignedCtx => do
          let some body ←
              goInner failureRef telemetry assignedCtx replayRules facts cmds
                bodyStart close env referenceCounts scopedProofs
            | trace[crush.result] "alethe replay: declined ({closeRule} anchor \
                                   {stepId} body)"
              return none
          proveStep conclusion (#[body] ++ scopedProofs) closeRule
      else
        trace[crush.result] "alethe replay: declined (unsupported anchor rule \
                             `{closeRule}` at {stepId})"
        rememberFailure failureRef {
          kind := .ruleGap
          stepId := some stepId
          rule := some closeRule
          term := some (clauseSexp closeClause)
          detail := "anchor rule is not supported by the replay engine" }
        return none
    let some pf := pf?
      | trace[crush.result] "alethe replay: declined (anchor {stepId} discharge)"
        rememberFailure failureRef {
          kind := .ruleGap
          stepId := some stepId
          rule := some closeRule
          term := some (clauseSexp closeClause)
          detail := "Lean could not discharge the anchored conclusion" }
        return none
    return some
      (stepId, { proof := pf, clause := conclusion, literals := conclusionLiterals },
        close + 1)

  /-- Replay a subproof block's steps, `[from, upto)`, returning the proof of the last one
  (the block's inner conclusion). -/
  goInner (failureRef : ReplayFailureRef) (telemetry : ReplayTelemetrySession)
      (ctx : TermCtx)
      (replayRules : ReplayRuleRegistry)
      (facts : Std.HashMap String Expr) (cmds : Array Command)
      («from» upto : Nat) (env : Std.HashMap String ClauseProof)
      (referenceCounts : Std.HashMap String Nat)
      (scopedProofs : Array Expr) :
      TacticM (Option Expr) := do
    let mut i := «from»
    let mut env := env
    let mut last : Option Expr := none
    while i < upto do
      match cmds[i]! with
      | .anchor .. =>
        let some (stepId, pf, next) ←
            replayAnchor failureRef telemetry ctx replayRules facts cmds
              referenceCounts i env scopedProofs
          | return none
        if next > upto then
          trace[crush.result] "alethe replay: declined (nested subproof {stepId} \
                               crosses its parent boundary)"
          rememberFailure failureRef {
            kind := .malformedCertificate
            stepId := some stepId
            detail := "nested subproof crosses its parent boundary" }
          return none
        env := env.insert stepId pf
        last := some pf.proof
        i := next
      | .step id clause rule premises args _ =>
        let some pf ←
            replayStep failureRef telemetry ctx replayRules referenceCounts env scopedProofs
              id clause rule premises args
          | return none
        env := env.insert id pf
        last := some pf.proof
        i := i + 1
      | .assume id _ =>
        trace[crush.result] "alethe replay: declined (stray local assumption {id})"
        rememberFailure failureRef {
          kind := .malformedCertificate
          stepId := some id
          detail := "local assumption does not immediately follow an anchor" }
        return none
    return last

  /-- Consecutive local assumptions immediately following an anchor. -/
  collectAssumptions (cmds : Array Command) («from» upto : Nat) :
      Array (String × Sexp) × Nat := Id.run do
    let mut assumptions := #[]
    let mut i := «from»
    while i < upto do
      match cmds[i]! with
      | .assume id term =>
        assumptions := assumptions.push (id, term)
        i := i + 1
      | _ => break
    return (assumptions, i)

  /-- Binder declarations from an anchor's `:args` payload. -/
  bindDeclarations (args : Array Sexp) : Array (String × Sexp) := Id.run do
    let mut declarations := #[]
    for i in [:args.size] do
      if args[i]? != some (Sexp.atom ":args") then continue
      let some (Sexp.list entries) := args[i + 1]? | continue
      for entry in entries do
        let Sexp.list pair := entry | continue
        let some (Sexp.atom name) := pair[0]? | continue
        let some sort := pair[1]? | continue
        if name != ":=" && pair.size == 2 then
          declarations := declarations.push (name, sort)
    return declarations

  /-- Explicit substitutions from a Skolem anchor's `:args` payload. -/
  anchorAssignments (args : Array Sexp) : Array (String × Sexp × Sexp) := Id.run do
    let mut assignments := #[]
    for i in [:args.size] do
      if args[i]? != some (Sexp.atom ":args") then continue
      let some (Sexp.list entries) := args[i + 1]? | continue
      for entry in entries do
        let Sexp.list parts := entry | continue
        if parts.size != 3 || parts[0]? != some (Sexp.atom ":=") then continue
        let some (Sexp.list binder) := parts[1]? | continue
        let some (Sexp.atom name) := binder[0]? | continue
        let some sort := binder[1]? | continue
        let some value := parts[2]? | continue
        if binder.size == 2 then
          assignments := assignments.push (name, sort, value)
    return assignments

  /-- Apply the explicit substitutions carried by bind and Skolem anchors. -/
  applyAnchorAssignments {α : Type} (failureRef : ReplayFailureRef)
      (ctx : TermCtx) (stepId rule : String) (args : Array Sexp)
      (onDone : TermCtx → TacticM (Option α)) : TacticM (Option α) := do
    let assignments := anchorAssignments args
    let rec go (index : Nat) (ctx : TermCtx) : TacticM (Option α) := do
      if h : index < assignments.size then
        let (name, sort, valueTerm) := assignments[index]
        let some expectedType ← sortToType? ctx sort
          | trace[crush.result] "alethe replay: declined (unknown assignment sort {sort})"
            rememberFailure failureRef {
              kind := .termGap
              stepId := some stepId
              rule := some rule
              term := some sort
              detail := s!"sort of assignment `{name}` could not be decoded" }
            return none
        let some value ← toExpr? ctx 64 valueTerm
          | trace[crush.result] "alethe replay: declined (untranslatable assignment \
                                 for {name})"
            rememberFailure failureRef {
              kind := .termGap
              stepId := some stepId
              rule := some rule
              term := some valueTerm
              detail := s!"value of assignment `{name}` could not be decoded" }
            return none
        unless ← isDefEq expectedType (← inferType value) do
          trace[crush.result] "alethe replay: declined (ill-typed assignment for {name})"
          rememberFailure failureRef {
            kind := .termGap
            stepId := some stepId
            rule := some rule
            term := some valueTerm
            detail := s!"value of assignment `{name}` has the wrong Lean type" }
          return none
        go (index + 1) { ctx with locals := ctx.locals.insert name value }
      else
        onDone ctx
    go 0 ctx

  /-- Index of the step that closes `stepId`, at or after `from`. -/
  findClose (cmds : Array Command) («from» : Nat) (stepId : String) : Option Nat := Id.run do
    let mut i := «from»
    while i < cmds.size do
      if let .step id _ rule _ _ _ := cmds[i]! then
        if id == stepId &&
            (rule == "subproof" || rule == "bind" ||
             rule == "sko_ex" || rule == "sko_forall") then
          return some i
      i := i + 1
    return none

/-- Compatibility wrapper for callers interested only in replay success. -/
def replay? (proof : AletheProof) (rawSexps : Array Sexp)
    (facts : Std.HashMap String Expr) (symbols : Std.HashMap String Expr) :
    TacticM (Option Expr) := do
  return (← replay proof rawSexps facts symbols).toOption

end Crush.Alethe
