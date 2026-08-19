import Crush.Solver.Alethe
import Crush.Solver.AletheTerm
import Crush.Solver.KernelCheck
import Crush.Translation.Monad
open Lean Meta Elab Tactic

/-!
# Replaying an Alethe proof as a Lean proof

The core-directed finisher (`Crush/Solver/Reconstruct.lean`) hands the *whole* goal to one
Lean tactic. That works surprisingly often, but fails when the argument needs a long chain
of small inferences no tactic re-finds in one shot — a Boolean pigeonhole, an EUF conflict
several congruences deep.

An Alethe proof is exactly that chain, already found: cvc5 reports ~20–60 steps, each a
*trivial* clause following from one or two earlier ones. So instead of re-searching, we
replay: restate each step's clause as a Lean proposition, prove it from the premises'
proofs, carry the result forward. The last clause is empty (`False`), contradicting the
negated goal.

## Why this is sound regardless of rule coverage

Every step is discharged by a Lean tactic into a real proof term the kernel checks, so the
trusted base is unchanged: the kernel plus the tactics we invoke. The rule name is only a
*hint* for which tactic to try first — a wrong guess makes a step fail, never succeed
wrongly. Any step that cannot be replayed (unhandled rule, unmappable term, failing tactic)
makes `replay?` return `none`, and the caller falls back to the finisher ladder.

So this is `Doc/PLAN.md` §9 M4 phase 3 done per *step* rather than per *rule*: we do not
prove each Alethe rule sound once and for all (lean-auto's reflective checker, ~12k lines),
we let the kernel check the proof's concrete instances. That trades a soundness
meta-theorem for per-call work, and needs no verified checker.

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

/-- Tactics tried on a step, in order. The rule name only selects which goes *first*; all
are tried, so an unrecognized rule still gets a chance.

Deliberately cheap and local: a step is a trivial consequence of its premises (that is what
makes an Alethe proof long), so a step needing real search is one we mapped wrong, and
declining beats grinding. -/
private def stepTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| simp_all)),
    (← `(tactic| grind)),
    (← `(tactic| omega)),
    (← `(tactic| rfl)),
    (← `(tactic| decide))]

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

private theorem bitVecGetLsbDXor {width : Nat} (left right : BitVec width)
    (index : Nat) :
    (BitVec.xor left right).getLsbD index =
      Bool.xor (left.getLsbD index) (right.getLsbD index) :=
  BitVec.getLsbD_xor

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

/-- Alethe's `rare_rewrite` rule carries the concrete rewrite name as its first argument.
Use that name to keep string-theory replay local to the relevant bridge theorem. -/
private def rareRewriteHint? (args : Array Sexp) :
    CoreM (Option (TSyntax `tactic)) := do
  let some (Sexp.str name) := args[0]? | return none
  match name with
  | "str-prefixof-elim" =>
    return some (← `(tactic| exact stringPrefixIffSubstr _ _))
  | "str-suffixof-elim" =>
    return some (← `(tactic| exact stringSuffixAppendIffSubstr _ _))
  | "str-substr-full-eq" =>
    return some (← `(tactic| exact stringSubstrFull _))
  | "str-substr-concat1" =>
    return some
      (← `(tactic| rw [stringSubstrAppendPrefix, stringSubstrFull]))
  | "str-substr-concat2" =>
    return some
      (← `(tactic| rw [stringSubstrAppendSuffix, Int.sub_self, stringSubstrFull]))
  | "str-contains-refl" =>
    return some (← `(tactic| simp only [stringContainsSelf]))
  | "str-contains-concat-find" =>
    return some (← `(tactic| simp only [stringContainsAppend]))
  | "str-len-concat-rec" =>
    return some (← `(tactic| exact stringIntLengthAppend _ _))
  | "str-len-eq-zero-base" =>
    return some (← `(tactic| exact stringIntLengthEqZeroIff _))
  | "str-len-eq-zero-concat-rec" =>
    return some (← `(tactic| exact stringIntLengthAppendEqZeroIff _ _))
  | "str-concat-unify" =>
    return some
      (← `(tactic| simp only [String.append_assoc, String.append_left_inj,
                              String.append_right_inj]))
  | "str-concat-unify-base" =>
    return some
      (← `(tactic| simp only [stringEqAppendSelfIff, stringEqSelfAppendIff]))
  | "bool-eq-true" | "bool-double-not-elim" | "eq-refl" | "eq-symm" =>
    return some (← `(tactic| grind))
  | "arith-geq-norm1-int" =>
    return some (← `(tactic| omega))
  | "arith-abs-eq" =>
    return some (← `(tactic| exact intAbsEq _ _))
  | name =>
    if name.startsWith "bv-" then
      return some (← `(tactic| bv_decide))
    return none

/-- Tactic to try first for a given rule, where we have a good guess. Purely a performance
hint — see the module comment on soundness. -/
private def ruleHint? (rule : String) (args : Array Sexp) :
    CoreM (Option (TSyntax `tactic)) := do
  match rule with
  | "refl" => return some (← `(tactic| rfl))
  | "evaluate" | "false" => return some (← `(tactic| decide))
  | "cong" | "trans" => return some (← `(tactic| grind))
  | "forall_inst" =>
    return some (← `(tactic| exact forallInstClause _ _))
  | "bind" => return some (← `(tactic| grind))
  | "sko_forall" =>
    return some (← `(tactic| simp_all only [forallIffAtCounterexample]))
  | "sko_ex" =>
    return some (← `(tactic| simp_all only [existsIffAtWitness]))
  | "la_mult_abs_comparison" =>
    return some (← `(tactic| grind [intAbs]))
  | "and_neg" =>
    return some (← `(tactic| simp_all [Bool.xor_comm, Bool.xor_left_comm]))
  | "hole" =>
    return some (← `(tactic| bv_decide))
  | "aci_simp" | "bv_bitwise_slicing" =>
    return some (← `(tactic| bv_decide))
  | "rare_rewrite" => rareRewriteHint? args
  | "resolution" => return some (← `(tactic| simp_all [stringIsEmptyEqDecide]))
  | "not_or" | "or" | "and" | "equiv_pos2" | "contraction"
  | "reordering" | "implies" | "implies_neg1" | "implies_neg2" | "subproof" =>
    return some (← `(tactic| grind))
  | rule =>
    if rule.startsWith "bv_bitblast_step_" then
      return some (← `(tactic| bv_decide))
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
    exact projected)
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
  `(tacticSeq|
    by_cases hindex : i = $value
    · subst i
      repeat' rw [bitVecGetLsbDXor]
      grind
    · $rest:tacticSeq)

/-- Concrete checker for cvc5's vector-equality-to-bits bridge. -/
private def bitVecEqualityHint? (target : Expr) : TacticM (Option (TSyntax `tactic)) := do
  let target ← whnf target
  unless target.isAppOfArity ``Iff 2 do return none
  let equality := target.getAppArgs[0]!
  unless equality.isAppOfArity ``Eq 3 do return none
  let type ← whnf equality.getAppArgs[0]!
  let .app (.const ``BitVec _) widthExpr := type | return none
  let some width ← getNatValue? widthExpr | return none
  let forward ← bitEqualityForward 0 width
  let cases ← bitIndexCases 0 width
  return some (← `(tactic|
    (constructor
     · intro heq
       ($forward:tacticSeq)
     · intro hbits
       apply BitVec.eq_of_getLsbD_eq
       intro i hi
       ($cases:tacticSeq))))

/-- Enumerate a concrete bit-vector width and prove each selected negation bit. -/
private partial def bitVecNegCases (remaining : Nat) :
    TacticM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if remaining == 0 then
    return ← `(tacticSeq| omega <;> done)
  let rest ← bitVecNegCases (remaining - 1)
  `(tacticSeq|
    cases i with
    | zero =>
      simp_all [BitVec.getLsbD_append, BitVec.getLsbD_neg, existsLtSucc,
        Bool.xor_comm, Bool.xor_left_comm] <;> done
    | succ i => $rest:tacticSeq)

/-- Prove cvc5's ripple-carry expansion of fixed-width bit-vector negation. -/
private def bitVecNegationHint? (target : Expr) :
    TacticM (Option (TSyntax `tactic)) := do
  let target ← whnf target
  unless target.isAppOfArity ``Eq 3 do return none
  let type ← whnf target.getAppArgs[0]!
  let .app (.const ``BitVec _) widthExpr := type | return none
  let some width ← getNatValue? widthExpr | return none
  let cases ← bitVecNegCases width
  return some (← `(tactic|
    (apply BitVec.eq_of_getLsbD_eq
     intro i hi
     ($cases:tacticSeq))))

/-- Prove `target` from the proofs in `premises`, trying the rule's hinted tactic first.

Builds the implication `p₁ → … → pₙ → target`, abstracts exactly its free variables,
proves the resulting closed proposition in an empty context, then applies it to those
variables and the premise proofs. Thus a step tactic cannot inspect any ambient declaration
that is absent from the step itself. -/
private def proveStep (target : Expr) (premises : Array Expr) (rule : String)
    (args : Array Sexp := #[]) :
    TacticM (Option Expr) := do
  let hypTypes ← premises.mapM fun p => do instantiateMVars (← inferType p)
  let impl := hypTypes.foldr (fun ty acc => mkForall `h .default ty acc) target
  let stepParams ← collectProofParams #[impl]
  let checkParams ← collectProofParams (premises.push impl)
  let closedImpl ← instantiateMVars (← mkForallFVars stepParams impl)
  let hint ←
    if rule == "bv_bitblast_step_bvequal" then
      bitVecEqualityHint? target
    else if rule == "bv_bitblast_step_bvneg" then
      bitVecNegationHint? target
    else
      ruleHint? rule args
  let isStringRewrite :=
    rule == "rare_rewrite" &&
      match args[0]? with
      | some (Sexp.str name) => name.startsWith "str-"
      | _ => false
  let hinted := match hint with | some t => #[t] | none => #[]
  let fallbacks ← stepTactics
  let tactics :=
    if isStringRewrite || rule == "bv_bitblast_step_bvneg" then hinted
    else hinted ++ fallbacks
  for tac in tactics do
    let saved ← saveState
    let snapshot ← KernelCheckSnapshot.capture
    try
      let mv ← withLCtx {} {} do mkFreshExprMVar closedImpl
      let gs ← Tactic.run mv.mvarId! <|
        Tactic.withSuppressedMessages <|
          Tactic.withoutRecover (evalTactic (← `(tactic| (intros; $tac))))
      if gs.isEmpty then
        let assigned ← instantiateMVars mv
        if rule == "bv_bitblast_step_bvneg" && assigned.hasMVar then
          for mvarId in (← getMVars assigned) do
            trace[crush.result] "Alethe bvneg unresolved metavariable {mvarId}: \
              {← instantiateMVars (← mvarId.getType)}"
        let proof := mkAppN (mkAppN assigned stepParams) premises
        let proof ← kernelCheckProofWithParams snapshot checkParams target proof
        return some proof
      if rule == "bv_bitblast_step_bvneg" then
        let remaining ← gs.mapM fun goal => do instantiateMVars (← goal.getType)
        trace[crush.result] "Alethe bvneg proof left goals: {remaining}"
      restoreState saved
    catch e =>
      if rule == "bv_bitblast_step_bvneg" then
        trace[crush.result] "Alethe bvneg proof failed: {e.toMessageData}"
      restoreState saved
  return none

private structure ClauseProof where
  proof : Expr
  literals : Array Expr
  deriving Inhabited

private structure ResolutionCandidate where
  left : Nat
  right : Nat
  leftPivot : Nat
  rightPivot : Nat
  result : Array Expr
  score : Nat

private partial def flattenClause (clause : Expr) : Array Expr :=
  let clause := clause.consumeMData
  if clause.isConstOf ``False then #[]
  else if clause.isAppOfArity ``Or 2 then
    flattenClause clause.getAppArgs[0]! ++ flattenClause clause.getAppArgs[1]!
  else
    #[clause]

private def mkClause (literals : Array Expr) : MetaM Expr := do
  if literals.isEmpty then return mkConst ``False
  let mut clause := literals.back!
  for i in [1:literals.size] do
    clause ← mkAppM ``Or #[literals[literals.size - 1 - i]!, clause]
  return clause

private def sameLiteral (left right : Expr) : MetaM Bool :=
  isDefEq left right

private def complementary (left right : Expr) : MetaM Bool := do
  if left.isAppOfArity ``Not 1 then
    return ← sameLiteral left.getAppArgs[0]! right
  if right.isAppOfArity ``Not 1 then
    return ← sameLiteral left right.getAppArgs[0]!
  return false

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
private partial def injectLiteral (target literal proof : Expr) : MetaM (Option Expr) := do
  let target := target.consumeMData
  if target.isAppOfArity ``Or 2 then
    let left := target.getAppArgs[0]!
    let right := target.getAppArgs[1]!
    if ← sameLiteral literal left then
      return some (mkApp3 (mkConst ``Or.inl) left right proof)
    let some rightProof ← injectLiteral right literal proof | return none
    return some (mkApp3 (mkConst ``Or.inr) left right rightProof)
  if ← sameLiteral literal target then return some proof
  return none

/-- Eliminate every literal of a clause into a common target. -/
private partial def eliminateClause (clause proof target : Expr)
    (onLiteral : Expr → Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  let clause := clause.consumeMData
  if clause.isAppOfArity ``Or 2 then
    let left := clause.getAppArgs[0]!
    let right := clause.getAppArgs[1]!
    let leftProof? ← withLocalDeclD `hleft left fun hleft => do
      let some result ← eliminateClause left hleft target onLiteral | return none
      return some (← mkLambdaFVars #[hleft] result)
    let some leftProof := leftProof? | return none
    let rightProof? ← withLocalDeclD `hright right fun hright => do
      let some result ← eliminateClause right hright target onLiteral | return none
      return some (← mkLambdaFVars #[hright] result)
    let some rightProof := rightProof? | return none
    return some (mkApp6 (mkConst ``Or.elim) left right target proof leftProof rightProof)
  onLiteral clause proof

/-- Weaken a clause by reordering its literals or adding alternatives. -/
private def weakenClause (source proof target : Expr) : MetaM (Option Expr) := do
  if source.consumeMData.isConstOf ``False then
    return some (mkApp2 (mkConst ``False.elim [Level.zero]) target proof)
  eliminateClause source proof target fun literal literalProof =>
    injectLiteral target literal literalProof

/-- Construct one binary propositional-resolution proof without invoking a tactic. -/
private def resolveClauses (leftClause rightClause target leftProof rightProof
    leftPivot rightPivot : Expr) : MetaM (Option Expr) := do
  eliminateClause leftClause leftProof target fun leftLiteral leftLiteralProof => do
    if ← sameLiteral leftLiteral leftPivot then
      eliminateClause rightClause rightProof target fun rightLiteral rightLiteralProof => do
        if ← sameLiteral rightLiteral rightPivot then
          let falseProof :=
            if leftPivot.isAppOfArity ``Not 1 then
              mkApp leftLiteralProof rightLiteralProof
            else
              mkApp rightLiteralProof leftLiteralProof
          return some (mkApp2 (mkConst ``False.elim [Level.zero]) target falseProof)
        injectLiteral target rightLiteral rightLiteralProof
    else
      injectLiteral target leftLiteral leftLiteralProof

private def bestResolution? (pool : Array ClauseProof) (target : Array Expr) :
    MetaM (Option ResolutionCandidate) := do
  let mut best : Option ResolutionCandidate := none
  for i in [:pool.size] do
    for j in [i + 1:pool.size] do
      for leftIndex in [:pool[i]!.literals.size] do
        for rightIndex in [:pool[j]!.literals.size] do
          unless ← complementary
              pool[i]!.literals[leftIndex]! pool[j]!.literals[rightIndex]! do
            continue
          let result ← resolveAt
            pool[i]!.literals pool[j]!.literals leftIndex rightIndex
          let mut foreign := 0
          for literal in result do
            unless ← containsLiteral target literal do foreign := foreign + 1
          let candidate := {
            left := i
            right := j
            leftPivot := leftIndex
            rightPivot := rightIndex
            result
            score := foreign * 1024 + result.size
          }
          if best.all (candidate.score < ·.score) then
            best := some candidate
  return best

/-- Replay a wide resolution node as a sequence of checked binary resolutions. -/
private def proveResolutionStep (target : Expr) (premises : Array Expr) :
    TacticM (Option Expr) := do
  let snapshot ← KernelCheckSnapshot.capture
  let targetLiterals := flattenClause target
  let mut pool := #[]
  for proof in premises do
    let type ← instantiateMVars (← inferType proof)
    pool := pool.push { proof, literals := flattenClause type }
  while !pool.isEmpty do
    for entry in pool do
      if ← clauseSubset entry.literals targetLiterals then
        let source ← instantiateMVars (← inferType entry.proof)
        if let some proof ← weakenClause source entry.proof target then
          return some (← kernelCheckProof snapshot target proof)
    if pool.size < 2 then break
    let some candidate ← bestResolution? pool targetLiterals | break
    let intermediate ← mkClause candidate.result
    let left := pool[candidate.left]!
    let right := pool[candidate.right]!
    let leftClause ← instantiateMVars (← inferType left.proof)
    let rightClause ← instantiateMVars (← inferType right.proof)
    let some proof ← resolveClauses leftClause rightClause intermediate
        left.proof right.proof
        left.literals[candidate.leftPivot]! right.literals[candidate.rightPivot]!
      | break
    let proof ← kernelCheckProof snapshot intermediate proof
    let mut next := #[]
    for i in [:pool.size] do
      unless i == candidate.left || i == candidate.right do
        next := next.push pool[i]!
    pool := next.push { proof, literals := candidate.result }
  return none

/-- Replay a clause permutation or contraction by structural weakening. -/
private def proveWeakeningStep (target premise : Expr) : TacticM (Option Expr) := do
  let snapshot ← KernelCheckSnapshot.capture
  let source ← instantiateMVars (← inferType premise)
  let some proof ← weakenClause source premise target | return none
  return some (← kernelCheckProof snapshot target proof)

/-- Replay a parsed Alethe proof into a Lean proof of `False`.

`facts` maps a `crush_fact_<n>` assumption id to the Lean proof of that hypothesis (from
`TranslateState.facts`); `symbols` is the emitted-symbol → Lean-term map. -/
partial def replay (proof : AletheProof) (rawSexps : Array Sexp)
    (facts : Std.HashMap String Expr) (symbols : Std.HashMap String Expr) :
    TacticM (Except ReplayFailure Expr) := do
  -- Collected from the *unstripped* text: the parser drops the annotations, which is
  -- exactly what `@p_k` references need.
  let named := rawSexps.foldl (fun acc s => collectNamed s acc) {}
  let decoders ← getAletheDecoders
  let ctx : TermCtx := { symbols, named, decoders }
  let failureRef ← IO.mkRef none
  match ← go failureRef ctx facts proof.commands 0 {} #[] with
  | some proof => return .ok proof
  | none =>
    let failure ← failureRef.get
    return .error (failure.getD {
      kind := .malformedCertificate
      detail := "certificate contains no replayable empty clause" })
where
  /-- Replay `cmds` from index `i` under proof environment `env`, returning the proof of the
  first empty clause reached. -/
  go (failureRef : ReplayFailureRef) (ctx : TermCtx)
      (facts : Std.HashMap String Expr) (cmds : Array Command)
      (i : Nat) (env : Std.HashMap String Expr) (scopedProofs : Array Expr) :
      TacticM (Option Expr) := do
    let mut i := i
    let mut env := env
    while h : i < cmds.size do
      match cmds[i] with
      | .assume id term =>
        -- A top-level assumption is one of our asserted facts, so its Lean proof is already
        -- in hand. Unnamed encoding axioms are accepted only when Lean can prove their
        -- translated statement in an empty context; an unused, untranslatable axiom may be
        -- skipped because no later step can consume it without a proof.
        match facts.get? id with
        | some proof =>
          env := env.insert id proof
        | none =>
          match ← toExpr? ctx 64 term with
          | some target =>
            let target ← toPropM target
            if let some proof ←
                (proveStep target #[] "assume" : TacticM (Option Expr)) then
              env := env.insert id proof
            else
              trace[crush.result] "alethe replay: skipped unproved encoding assumption {id}"
          | none =>
            trace[crush.result] "alethe replay: skipped untranslatable encoding \
                                 assumption {id}"
        i := i + 1
      | .anchor .. =>
        let some (stepId, closeClause, pf, next) ←
            replayAnchor failureRef ctx facts cmds i env scopedProofs
          | return none
        env := env.insert stepId pf
        if closeClause.isEmpty then
          trace[crush.result] "alethe replay: succeeded at {stepId}"
          return some pf
        i := next
      | .step id clause rule premises args _ =>
        let some pf ←
            replayStep failureRef ctx env scopedProofs id clause rule premises args
          | return none
        env := env.insert id pf
        -- The empty clause is `False`: the refutation is complete.
        if clause.isEmpty then
          trace[crush.result] "alethe replay: succeeded at {id}"
          return some pf
        i := i + 1
    trace[crush.result] "alethe replay: declined (no empty-clause step)"
    rememberFailure failureRef {
      kind := .malformedCertificate
      detail := "certificate contains no empty-clause step" }
    return none

  /-- Replay one ordinary derived step from the proofs currently in scope. -/
  replayStep (failureRef : ReplayFailureRef) (ctx : TermCtx)
      (env : Std.HashMap String Expr) (scopedProofs : Array Expr)
      (id : String)
      (clause : Array Sexp) (rule : String) (premises : Array String)
      (args : Array Sexp) : TacticM (Option Expr) := do
    let some target ← clauseToExpr? ctx 64 clause
      | trace[crush.result] "alethe replay: declined (untranslatable clause at {id}: \
                             {clause})"
        rememberFailure failureRef {
          kind := .termGap
          stepId := some id
          rule := some rule
          term := some (clauseSexp clause)
          detail := "certificate clause could not be decoded as a Lean proposition" }
        return none
    let mut prems := #[]
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
      prems := prems.push pf
    let proof? ←
      if rule == "resolution" && prems.size > 1 then
        match ← proveResolutionStep target prems with
        | some proof => pure (some proof)
        | none => proveStep target prems rule args
      else if (rule == "reordering" || rule == "contraction") && prems.size == 1 then
        match ← proveWeakeningStep target prems[0]! with
        | some proof => pure (some proof)
        | none => proveStep target prems rule args
      else
        proveStep target prems rule args
    let proof? ←
      match proof? with
      | some proof => pure (some proof)
      | none =>
        if scopedProofs.isEmpty then
          pure none
        else
          proveStep target (prems ++ scopedProofs) rule args
    let some pf := proof?
      | let premiseTypes ← prems.mapM fun premise => inferType premise
        trace[crush.result] "alethe replay: declined (rule `{rule}` at {id} not \
                             replayed; target: {target}; premises: {premiseTypes})"
        rememberFailure failureRef {
          kind := .ruleGap
          stepId := some id
          rule := some rule
          term := some (clauseSexp clause)
          detail := "Lean could not prove this concrete inference from its replayed premises" }
        return none
    return some pf

  /-- Replay an anchored subproof or binder congruence and return its closed proof. -/
  replayAnchor (failureRef : ReplayFailureRef) (ctx : TermCtx)
      (facts : Std.HashMap String Expr) (cmds : Array Command)
      (index : Nat) (env : Std.HashMap String Expr) (scopedProofs : Array Expr) :
      TacticM (Option (String × Array Sexp × Expr × Nat)) := do
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
    let some conclusion ← clauseToExpr? ctx 64 closeClause
      | trace[crush.result] "alethe replay: declined (untranslatable anchored \
                             conclusion {stepId})"
        rememberFailure failureRef {
          kind := .termGap
          stepId := some stepId
          rule := some closeRule
          term := some (clauseSexp closeClause)
          detail := "anchored conclusion could not be decoded as a Lean proposition" }
        return none
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
        let rec bindAssumptions (j : Nat) (innerEnv : Std.HashMap String Expr)
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
            let hypTy ← toPropM hypTy
            withLocalDeclD (`hsub ++ localId.toName) hypTy fun hlocal =>
              bindAssumptions (j + 1) (innerEnv.insert localId hlocal)
                (locals.push hlocal)
          else
            let some body ← goInner failureRef ctx facts cmds bodyStart close innerEnv
                (scopedProofs ++ locals)
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
                  goInner failureRef assignedCtx facts cmds bodyStart close env scopedProofs
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
              goInner failureRef assignedCtx facts cmds bodyStart close env scopedProofs
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
    return some (stepId, closeClause, pf, close + 1)

  /-- Replay a subproof block's steps, `[from, upto)`, returning the proof of the last one
  (the block's inner conclusion). -/
  goInner (failureRef : ReplayFailureRef) (ctx : TermCtx)
      (facts : Std.HashMap String Expr) (cmds : Array Command)
      («from» upto : Nat) (env : Std.HashMap String Expr) (scopedProofs : Array Expr) :
      TacticM (Option Expr) := do
    let mut i := «from»
    let mut env := env
    let mut last : Option Expr := none
    while i < upto do
      match cmds[i]! with
      | .anchor .. =>
        let some (stepId, _, pf, next) ←
            replayAnchor failureRef ctx facts cmds i env scopedProofs
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
        last := some pf
        i := next
      | .step id clause rule premises args _ =>
        let some pf ←
            replayStep failureRef ctx env scopedProofs id clause rule premises args
          | return none
        env := env.insert id pf
        last := some pf
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

  /-- `AletheTerm.toProp` is private; this mirrors it for the local-assumption type. -/
  toPropM (e : Expr) : TacticM Expr := do
    let ty ← whnf (← inferType e)
    if ty.isProp then return e
    else if ty.isConstOf ``Bool then mkEq e (mkConst ``Bool.true)
    else return e

/-- Compatibility wrapper for callers interested only in replay success. -/
def replay? (proof : AletheProof) (rawSexps : Array Sexp)
    (facts : Std.HashMap String Expr) (symbols : Std.HashMap String Expr) :
    TacticM (Option Expr) := do
  return (← replay proof rawSexps facts symbols).toOption

end Crush.Alethe
