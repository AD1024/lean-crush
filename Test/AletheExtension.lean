import Crush

/-!
End-to-end coverage for custom lowering inversion during Alethe replay.
-/

open Lean Meta Elab Tactic
open Crush Crush.Alethe Crush.SMT

def MultipleOfThree (value : Int) : Prop :=
  value % 3 = 0

@[crush_translate_head MultipleOfThree]
def lowerMultipleOfThree : LoweringHandler := fun ctx => do
  let #[value] := ctx.args | return none
  let value ← ctx.emitTerm value
  return some (.app (.indexed "divisible" #[.inr 3]) #[value])

register_crush_replay term <<
  ((_ divisible (int divisor)) (term value : Int)) |
  (divisible (term divisor : Int) (term value : Int)) =>
    value % divisor = 0
>>

register_crush_replay term low <<
  (test_term_priority) => (0 : Nat)
>>

register_crush_replay term high <<
  (test_term_priority) => (1 : Nat)
>>

@[crush_replay "test_low_level_replay"]
def lowLevelReplayHandler : ReplayTermHandler := fun ctx => do
  unless ctx.indices.isEmpty && ctx.args.isEmpty do return none
  return some (Lean.toExpr (2 : Nat))

register_crush_replay rule <<
  (test_replay_left (nat value)) |
  (test_replay_right (nat value)) =>
    by exact Nat.le_refl value
>>

register_crush_replay rule low <<
  (test_replay_priority ..) => by exact True.intro
>>

register_crush_replay rule high <<
  (test_replay_priority ..) => by exact True.intro
>>

register_crush_replay rule <<
  (test_replay_context ..) => by assumption
>>

structure ReplayStringBindingIs where
  name : Name
  expected : String

instance : ReplayCondition ReplayStringBindingIs where
  check condition ctx := do
    let some (.lit (.strVal value)) := ctx.binding? condition.name
      | return false
    return value == condition.expected

private def enabledReplayCondition : ReplayStringBindingIs where
  name := `value
  expected := "enabled"

register_crush_replay rule <<
  (test_replay_conditional_left (atom value)) |
  (test_replay_conditional_right (atom value))
    if enabledReplayCondition =>
    by exact True.intro
>>

private def functionReplayCondition : ReplayConditionHandler := fun ctx =>
  return ctx.args[0]? == some (.atom "function")

register_crush_replay rule <<
  (test_replay_function_condition ..)
    if functionReplayCondition =>
    by exact True.intro
>>

private def assigningReplayCondition : ReplayConditionHandler := fun ctx => do
  let target ← whnf ctx.target
  unless target.isAppOfArity ``Eq 3 do return false
  let value := target.getAppArgs[1]!
  unless value.isMVar do return false
  value.mvarId!.assign (Lean.toExpr (1 : Nat))
  return true

register_crush_replay rule <<
  (test_replay_condition_state ..)
    if assigningReplayCondition =>
    by rfl
>>

private def failingReplayCondition : ReplayConditionHandler := fun _ =>
  throwError "condition exploded"

register_crush_replay rule <<
  (test_replay_condition_error ..)
    if failingReplayCondition =>
    by exact True.intro
>>

/-!
error: failed to synthesize
-/
#guard_msgs(error, substring := true) in
register_crush_replay rule <<
  (test_replay_missing_condition_instance ..)
    if (0 : Nat) =>
    by exact True.intro
>>

/-!
error: all replay pattern alternatives must bind the same names
-/
#guard_msgs(error, substring := true) in
register_crush_replay rule <<
  (test_replay_mismatch_left (nat left)) |
  (test_replay_mismatch_right (nat right)) =>
    by exact True.intro
>>

@[crush_replay_rule "test_replay_kernel_rejection"]
private def invalidReplayRule : ReplayRuleHandler := fun _ =>
  return some (mkConst ``True.intro)

private def parseTerm (source : String) : MetaM Sexp := do
  let some (term, rest) := parseSexp source
    | throwError "failed to parse Alethe term `{source}`"
  unless rest.trimAscii.isEmpty do
    throwError "trailing input after Alethe term `{source}`"
  return term

private def assertDecoded (symbols : Std.HashMap String Expr)
    (source : String) (expected : Expr) : MetaM Unit := do
  let decoders ← getReplayTermHandlers
  let context : TermCtx := { symbols, named := {}, decoders }
  let some actual ← toExpr? context 64 (← parseTerm source)
    | throwError "failed to decode Alethe term `{source}`"
  unless ← isDefEq actual expected do
    throwError "Alethe term `{source}` decoded as `{actual}`, expected `{expected}`"

run_meta do
  unless ← hasReplayTermHandlersFor "divisible" do
    throwError "the `divisible` replay handler was not registered"
  let termHandlers ← getReplayTermHandlers
  let some prioritizedTerm ←
      runReplayTermHandlers termHandlers "test_term_priority" #[] #[]
    | throwError "the prioritized replay term did not match"
  unless ← isDefEq prioritizedTerm (Lean.toExpr (1 : Nat)) do
    throwError "replay term handlers were not ordered by priority"
  let some lowLevelTerm ←
      runReplayTermHandlers termHandlers "test_low_level_replay" #[] #[]
    | throwError "the low-level replay term handler did not match"
  unless ← isDefEq lowLevelTerm (Lean.toExpr (2 : Nat)) do
    throwError "the low-level replay term handler returned the wrong term"
  let rules ← getReplayRuleHandlers
  for rule in #["test_replay_left", "test_replay_right"] do
    if (rules.getD rule #[]).isEmpty then
      throwError "the alternative replay rule `{rule}` was not registered"
  let priorities :=
    (rules.getD "test_replay_priority" #[]).map (·.priority)
  unless priorities.size ≥ 2 && priorities[0]! > priorities[1]! do
    throwError "replay rule handlers were not ordered by priority"
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let remainder ← mkAppM ``HMod.hMod #[x, Lean.toExpr (3 : Int)]
    let expected ← mkEq remainder (Lean.toExpr (0 : Int))
    let symbols := ({} : Std.HashMap String Expr).insert "x" x
    assertDecoded symbols "((_ divisible 3) x)" expected
    assertDecoded symbols "(divisible 3 x)" expected

private def replayTestRule (goal : MVarId) (rule arg : String) :
    TacticM (Option Expr) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let registry ← getReplayRuleHandlers
  runReplayRuleHandlers registry {
    stepId := "test"
    rule
    target
    targetLiterals := #[target]
    premises := #[]
    args := #[.atom arg]
    decodeTerm := fun _ => return none
    decodeSort := fun _ => return none
    toProp := pure
  }

elab "run_test_replay " rule:str arg:str : tactic => do
  let goal ← getMainGoal
  let some rule := rule.raw.isStrLit?
    | throwErrorAt rule "expected a rule string"
  let some arg := arg.raw.isStrLit?
    | throwErrorAt arg "expected an argument string"
  let some proof ← replayTestRule goal rule arg
    | throwError "test replay rule `{rule}` declined"
  goal.assign proof
  replaceMainGoal []

elab "assert_test_replay_declines " rule:str arg:str : tactic => do
  let goal ← getMainGoal
  let some rule := rule.raw.isStrLit?
    | throwErrorAt rule "expected a rule string"
  let some arg := arg.raw.isStrLit?
    | throwErrorAt arg "expected an argument string"
  if (← replayTestRule goal rule arg).isSome then
    throwError "test replay rule `{rule}` unexpectedly used the ambient context"

elab "assert_test_replay_condition_isolated" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let value ← mkFreshExprMVar (mkConst ``Nat)
    let target ← mkEq value (Lean.toExpr (0 : Nat))
    let registry ← getReplayRuleHandlers
    let some _ ← runReplayRuleHandlers registry {
      stepId := "condition-state"
      rule := "test_replay_condition_state"
      target
      targetLiterals := #[target]
      premises := #[]
      args := #[]
      decodeTerm := fun _ => return none
      decodeSort := fun _ => return none
      toProp := pure
    } | throwError "replay condition leaked its metavariable assignment"
    let value ← instantiateMVars value
    unless ← isDefEq value (Lean.toExpr (0 : Nat)) do
      throwError "replay condition state was retained"
    goal.assign (mkConst ``True.intro)
    replaceMainGoal []

example : (3 : Nat) ≤ 3 := by
  run_test_replay "test_replay_left" "3"

example : (4 : Nat) ≤ 4 := by
  run_test_replay "test_replay_right" "4"

example (h : False) : False := by
  assert_test_replay_declines "test_replay_context" "unused"
  exact h

example : True := by
  run_test_replay "test_replay_conditional_left" "enabled"

example : True := by
  run_test_replay "test_replay_conditional_right" "enabled"

example (h : True) : True := by
  assert_test_replay_declines "test_replay_conditional_left" "disabled"
  exact h

example : True := by
  run_test_replay "test_replay_function_condition" "function"

example : True := by
  assert_test_replay_condition_isolated

/-!
error: replay condition `failingReplayCondition` failed:
-/
#guard_msgs(error, substring := true) in
example : True := by
  run_test_replay "test_replay_condition_error" "unused"

/-!
error: crush: reconstructed proof failed kernel validation:
-/
#guard_msgs(error, substring := true) in
example : False := by
  run_test_replay "test_replay_kernel_rejection" "unused"

section Replay

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option crush.timeout 10

theorem custom_divisibility_replay (x : Int)
    (hx : MultipleOfThree x) :
    ¬x % 3 ≠ 0 := by
  crush

#print axioms custom_divisibility_replay

end Replay
