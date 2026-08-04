import Lean
import Crush.Frontend.Config
import Crush.Reify.Collect
import Crush.Translation.Translate
import Crush.Solver.Process
import Crush.Solver.Reconstruct
import Crush.SMT.Print
import Crush.SMT.Result
open Lean Elab Tactic Meta

/-!
# The `crush` tactic

The end-to-end path:

1. read `Config` from the option environment;
2. collect local `Prop` hypotheses and the negated goal (`Crush.collectFacts`);
3. translate each fact to an `SMT.Term`, asserting it with a `:named crush_fact_N`
   attribute so an unsat core maps back to provenance (`Crush.emitTerm`);
4. build the script (`set-logic`, declarations, assertions, `check-sat`), optionally
   saving/tracing it;
5. run the backend with a hard timeout (`Crush.Solver.runQuery`);
6. discharge: on `unsat`, close the goal per `crush.trust`; on `sat`, report the
   model as a counterexample; on `unknown`/timeout, say so.

Three discharge policies, selected by `crush.trust`:

* `trust` — close with the `crushSorry` axiom. Fast; the solver and its translation
  are in the trusted computing base.
* `reconstruct` — replay the verdict as a checked Lean proof using the unsat core
  (`Crush.tryReconstruct`); error if that fails, so the axiom is never used.
* `reconstructOrTrust` (default) — replay if possible, else fall back to the axiom
  with a warning, so the fallback is visible rather than silent.
-/

namespace Crush

/-- The trust axiom, used only under `crush.trust`. Deliberately `Prop`-only (not
`Sort u`), so it cannot be used to fabricate data, and auditable via
`#print axioms`: any theorem closed by trusting the solver names it. -/
axiom crushSorry (P : Prop) : P

initialize registerTraceClass `crush
initialize registerTraceClass `crush.script
initialize registerTraceClass `crush.result

open SMT

/-- Resolve the SMT-LIB logic string: explicit `crush.logic`, else a permissive
default (`ALL`, or `HO_ALL` when higher-order support must be switched on). -/
def resolveLogic (cfg : Config) : String :=
  match cfg.logic with
  | some l => l
  | none =>
    -- cvc5 gates its higher-order solver on the *logic-string prefix*: `HO_ALL`
    -- turns it on, plain `ALL` does not (its `enableEverything` checks for `HO_`).
    -- Only cvc5 understands the prefix — z3 warns "ignoring unsupported logic" and
    -- carries on, then fails on the function sorts — so we emit it solely when it
    -- will actually be honoured.
    if cfg.hoMode == .native && cfg.backend == .cvc5 then "HO_ALL" else "ALL"

/-- Translate all facts into assertion commands, each `:named` for unsat-core
provenance, prepended by the declarations they induce. Returns the full script
(minus `check-sat`) and the final `TranslateState` (for provenance lookup). -/
def buildScript (cfg : Config) (facts : Array Fact) :
    MetaM (Array SMT.Command × TranslateState) := do
  let (_, st) ← TranslateM.run cfg do
    for fact in facts do
      let id ← TranslateM.recordFact fact.descr fact.proof
      let body ← emitTerm fact.prop
      let named := Term.annot body #[.named s!"{factNamePrefix}{id}"]
      TranslateM.emitCommand (.assert named)
  -- Prepend set-logic. Declarations are emitted eagerly on first use (before the
  -- assertion that references them), so command order already satisfies SMT-LIB's
  -- declare-before-reference rule.
  return (#[Command.setLogic (resolveLogic cfg)] ++ st.commands, st)

/-- Render a `sat` model into a short counterexample message. -/
def formatCounterexample (modelText : String) (st : TranslateState) : MessageData := Id.run do
  let entries := parseModel modelText
  if entries.isEmpty then
    return m!"solver found a model (no assignments reported)"
  let mut lines : Array MessageData := #[]
  for e in entries do
    -- Map the SMT symbol back to its Lean origin when known.
    let origin := (st.nameToAtom.get? e.name).getD e.name
    lines := lines.push m!"  {origin} := {e.value}"
  return m!"counterexample:{indentD (MessageData.joinSep lines.toList "\n")}"

/-- The core driver, given a resolved goal and config. -/
def runCrush (goal : MVarId) (cfg : Config) : TacticM Unit := goal.withContext do
  -- `native` HO mode needs a backend that honours the `HO_` logic prefix. z3 prints
  -- "ignoring unsupported logic" and then chokes on the function sorts, so fall
  -- back to the portable encoding rather than emitting a script it cannot read.
  let cfg :=
    if cfg.hoMode == .native && !nativeSupported cfg.backend then
      { cfg with hoMode := .defunctionalize }
    else cfg
  if (← getOptions) |> (fun o => crush.ho.mode.get o == HOMode.native) then
    unless nativeSupported cfg.backend do
      logWarning m!"crush: `crush.ho.mode native` requires a higher-order capable \
                    backend (cvc5); `{cfg.backend}` is first-order only. Falling \
                    back to `defunctionalize`."
  -- `combinators` is specified but not yet implemented. Say so rather than
  -- silently behaving as `defunctionalize` — a user who selected it would
  -- otherwise believe they were exercising the combinator encoding.
  let cfg :=
    if cfg.hoMode == .combinators then
      { cfg with hoMode := .defunctionalize }
    else cfg
  if (← getOptions) |> (fun o => crush.ho.mode.get o == HOMode.combinators) then
    logWarning "crush: `crush.ho.mode combinators` is not implemented yet \
                (`defunctionalize` and `native` are); using `defunctionalize`."
  let facts ← collectFacts goal
  let (script, st) ← buildScript cfg facts
  if cfg.traceScript then
    logInfo m!"crush SMT script:{indentD (scriptToString script)}"
  trace[crush.script] "{scriptToString script}"
  Solver.maybeSave cfg script
  if cfg.backend == .none then
    logInfo m!"crush: backend is `none`; emitted {script.size} commands, no solver run."
    return
  let result ← Solver.runQuery cfg script
  match result with
  | .unsat coreText _ =>
    let coreIds := parseUnsatCore coreText
    trace[crush.result] "unsat; core facts: {coreIds}"
    match cfg.trust with
    | .trust =>
      let goalType ← goal.getType
      goal.assign (mkApp (mkConst ``crushSorry) goalType)
    | .reconstruct | .reconstructOrTrust =>
      -- Solver-as-oracle: the core tells us *which* hypotheses matter, and a Lean
      -- finishing tactic re-proves the goal from just those. On success the solver
      -- leaves the trusted computing base — it was only a search heuristic.
      let coreProofs := coreHypotheses st coreIds
      trace[crush.result] "reconstructing from core: {coreDescriptions st coreIds}"
      if ← tryReconstruct goal coreProofs (← finisherTactics) then
        trace[crush.result] "reconstruction succeeded; no axiom used"
      else if cfg.trust == .reconstructOrTrust then
        logWarning m!"crush: solver reported `unsat`, but no finishing tactic could \
                      replay it from the {coreProofs.size} core \
                      hypothes{if coreProofs.size == 1 then "is" else "es"}; \
                      closing with the `crushSorry` axiom (trusting the solver). \
                      Set `crush.trust` to `reconstruct` to make this an error."
        let goalType ← goal.getType
        goal.assign (mkApp (mkConst ``crushSorry) goalType)
      else
        throwError m!"crush: solver reported `unsat`, but reconstruction failed — no \
                      finishing tactic could replay it from the core \
                      ({coreDescriptions st coreIds}). Set `crush.trust` to \
                      \"reconstructOrTrust\" to accept the solver's verdict anyway."
  | .sat modelText =>
    throwError m!"crush: the goal is not provable — solver found a {formatCounterexample modelText st}"
  | .unknown reason =>
    let reason := if reason.isEmpty then "no reason given" else reason
    throwError m!"crush: solver returned `unknown` ({reason}). \
                  Try increasing `crush.timeout` or adding hypotheses."

/-- `crush` tactic. Takes no arguments; uses all local `Prop` hypotheses. -/
syntax (name := crushTac) "crush" : tactic

@[tactic crushTac]
def evalCrush : Tactic := fun _stx => do
  let cfg := Config.ofOptions (← getOptions)
  let goal ← getMainGoal
  -- Intro any leading binders so ∀-goals become closed props under hypotheses.
  let (_, goal) ← goal.intros
  replaceMainGoal [goal]
  runCrush goal cfg

end Crush
