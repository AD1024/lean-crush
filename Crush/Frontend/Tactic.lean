import Lean
import Crush.Frontend.Config
import Crush.Reify.Collect
import Crush.Translation.Monomorphize
import Crush.Translation.Translate
import Crush.Util.Profile
import Crush.Solver.Process
import Crush.Solver.Reconstruct
import Crush.Solver.AletheReplay
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
* `reconstruct` (default) — replay the verdict as a checked Lean proof using the
  unsat core (`Crush.tryReconstruct`); error if that fails, so the axiom is never
  used. Making this the default means a translation bug that yields a false `unsat`
  cannot silently close a false goal: it fails reconstruction and errors instead.
* `reconstructOrTrust` — replay if possible, else fall back to the axiom with a
  warning, so the fallback is visible rather than silent. Opt in when a goal is
  genuinely beyond the finishers (nonlinear arithmetic, finite-domain
  exhaustiveness) and trusting the solver is acceptable.
-/

namespace Crush

/-- The trust axiom, used only under `crush.trust`. Deliberately `Prop`-only (not
`Sort u`), so it cannot be used to fabricate data, and auditable via
`#print axioms`: any theorem closed by trusting the solver names it. -/
axiom crushSorry (P : Prop) : P

initialize registerTraceClass `crush
initialize registerTraceClass `crush.script
initialize registerTraceClass `crush.result
initialize registerTraceClass `crush.mono

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

/-- Try to close `goal` by replaying the solver's proof certificate.

The certificate refutes the *negated* goal, so the shape is a proof by contradiction:
`Classical.byContradiction` turns the goal `G` into `¬G ⊢ False`, the fresh `¬G` hypothesis
is bound to the certificate's assumption for the negated goal (which has no Lean proof of
its own — it is the thing being refuted), and replay produces the `False`.

Returns `false` — leaving `goal` untouched — whenever anything is missing or a step cannot
be replayed, so the caller falls back to the finisher ladder. Every replayed step is a
kernel-checked term, so declining is the only failure mode; a certificate is never taken
on faith. -/
def tryProofReplay (goal : MVarId) (cfg : Config) (st : TranslateState) (proofText : String) :
    TacticM Bool := do
  unless cfg.proofReplay do return false
  if proofText.trimAscii.isEmpty then return false
  let some proof := Alethe.parseProof proofText | return false
  goal.withContext do
    -- `byContradiction` gives us `¬G` as a hypothesis and `False` as the goal.
    let goalType ← goal.getType
    let negGoal ← mkAppM ``Not #[goalType]
    let mv ← mkFreshExprMVar (← mkArrow negGoal (mkConst ``False))
    let (fvarId, inner) ← mv.mvarId!.intro `hneg
    let res ← inner.withContext do
      -- Map each `crush_fact_<n>` assumption to a Lean proof: a real hypothesis for an
      -- asserted fact, and the freshly-introduced `¬G` for the negated goal.
      let mut facts : Std.HashMap String Expr := {}
      for src in st.facts do
        let name := s!"{factNamePrefix}{src.id}"
        match src.proof with
        | some p => facts := facts.insert name p
        | none => facts := facts.insert name (mkFVar fvarId)
      Alethe.replay? proof (SMT.parseSexps proofText) facts st.nameToExpr
    match res with
    | none => return false
    | some falseProof =>
      -- Assemble `byContradiction (fun hneg => falseProof)` and hand it to the kernel.
      inner.assign falseProof
      let lam ← instantiateMVars mv
      if lam.hasSorry || lam.hasExprMVar then return false
      try
        let pf ← mkAppOptM ``Classical.byContradiction #[some goalType, some lam]
        -- Type-check before assigning: a mis-assembled term must fail here, not later.
        let ty ← inferType pf
        unless ← isDefEq ty goalType do return false
        goal.assign pf
        return true
      catch _ => return false

/-- The core driver, given a resolved goal, config, and collected hints. -/
def runCrush (goal : MVarId) (cfg : Config) (hints : Hints := {}) : TacticM Unit :=
  goal.withContext do
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
  -- Profiling: when `crush.profile` is on, each phase below is wall-clock timed and a
  -- breakdown is logged at the end. Off by default and costs only a branch per phase.
  let mut prof := if cfg.profile then Profiler.on else Profiler.off
  let (facts, prof') ← prof.time "collect" (collectFacts goal hints cfg.autoUnfold)
  prof := prof'
  -- Specialize polymorphic facts at the types the query mentions. Without this a
  -- polymorphic lemma is emitted at an abstract instantiation, giving SMT symbols
  -- disjoint from the goal's, so it cannot discharge anything — even for a ground
  -- goal (see `Crush.monomorphizeFacts`).
  let (mono, prof') ← prof.time "monomorphize" (monomorphizeFacts cfg facts)
  prof := prof'
  let facts := mono.facts
  trace[crush.mono] "generated {mono.generated} instance(s); \
                     dropped: {mono.dropped}; rejected: {mono.rejected}; \
                     exhausted: {mono.exhausted}"
  -- Truncation is never silent: a hit bound is a completeness loss the user can act
  -- on by raising `crush.mono.fuel`/`rounds`.
  if mono.exhausted then
    logWarning m!"crush: monomorphization hit its bound after {mono.generated} \
                  instance(s) (`crush.mono.fuel` = {cfg.monoFuel}, \
                  `crush.mono.rounds` = {cfg.monoRounds}); the fact set may be \
                  incomplete. Raise the bound if the goal is not provable."
  -- A certification failure (only possible with `crush.mono.certify`) means the pass
  -- built an instance whose proof did not match its proposition — a bug in
  -- monomorphization, not the user's goal. Loud, since it would otherwise be a silent
  -- soundness hole under a trusting policy.
  unless mono.rejected.isEmpty do
    logWarning m!"crush: monomorphization produced {mono.rejected.size} \
                  instance(s) that failed certification and were dropped \
                  ({mono.rejected}); this indicates an internal bug in the \
                  monomorphizer. The affected facts were not asserted."
  let ((script, st), prof') ← prof.time "translate" (buildScript cfg facts)
  prof := prof'
  if cfg.traceScript then
    logInfo m!"crush SMT script:{indentD (scriptToString script)}"
  trace[crush.script] "{scriptToString script}"
  Solver.maybeSave cfg script
  if cfg.backend == .none then
    logInfo m!"crush: backend is `none`; emitted {script.size} commands, no solver run."
    if cfg.profile then logInfo prof.report
    return
  let (result, prof') ← prof.time "solve" (Solver.runQuery cfg script)
  prof := prof'
  match result with
  | .unsat coreText proofText =>
    let coreIds := parseUnsatCore coreText
    trace[crush.result] "unsat; core facts: {coreIds}"
    match cfg.trust with
    | .trust =>
      let goalType ← goal.getType
      goal.assign (mkApp (mkConst ``crushSorry) goalType)
      if cfg.profile then logInfo prof.report
    | .reconstruct | .reconstructOrTrust =>
      -- Solver-as-oracle: the core tells us *which* hypotheses matter, and a Lean
      -- finishing tactic re-proves the goal from just those. On success the solver
      -- leaves the trusted computing base — it was only a search heuristic.
      let coreProofs := coreHypotheses st coreIds
      trace[crush.result] "reconstructing from core: {coreDescriptions st coreIds}"
      -- Proof replay first, when the solver gave us a certificate. It closes goals the
      -- single-shot ladder cannot (long chains of trivial steps: Boolean pigeonhole, deep
      -- EUF conflicts) because the chain is already found. Declining is free — every step
      -- is kernel-checked, so a step we cannot replay just falls through to the ladder.
      let (replayed, prof') ← prof.time "replay" (tryProofReplay goal cfg st proofText)
      prof := prof'
      if replayed then
        trace[crush.result] "proof replay succeeded; no axiom used"
        if cfg.profile then logInfo prof.report
        return
      let (ok, prof') ← prof.time "reconstruct" (tryReconstruct goal coreProofs (← finisherTactics))
      prof := prof'
      if ok then
        trace[crush.result] "reconstruction succeeded; no axiom used"
        if cfg.profile then logInfo prof.report
      else if cfg.trust == .reconstructOrTrust then
        logWarning m!"crush: solver reported `unsat`, but no finishing tactic could \
                      replay it from the {coreProofs.size} core \
                      hypothes{if coreProofs.size == 1 then "is" else "es"}; \
                      closing with the `crushSorry` axiom (trusting the solver). \
                      Set `crush.trust` to `reconstruct` to make this an error."
        let goalType ← goal.getType
        goal.assign (mkApp (mkConst ``crushSorry) goalType)
        if cfg.profile then logInfo prof.report
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

/-! ## Tactic syntax and the hint grammar

```
crush [h₁, …, hₙ, *] u[f₁, …] d[g₁, …]
```

* bare `crush` — assert every local `Prop` hypothesis plus the negated goal;
* `[…]` — an explicit hint list. A `term` element is a lemma or hypothesis to
  assert (this is how you point `crush` at a lemma that is *not* in context — the
  gap that made the tactic argumentless before). A `*` element additionally sweeps
  in all local hypotheses. An explicit list *without* `*` restricts to exactly the
  listed facts (plus the goal), matching Sledgehammer/`auto`;
* `u[f, …]` — unfold: add each `f`'s equation lemmas (`getEqnsFor?`);
* `d[f, …]` — definitional equality: add each `f`'s unfold equation
  (`getUnfoldEqnFor?`, the `f x = body` form).

The grammar mirrors lean-auto's so the muscle memory transfers. -/

syntax crushHintElem := term <|> "*"
syntax crushHints := ("[" crushHintElem,* "]")?
syntax crushUnfolds := "u[" ident,* "]"
syntax crushDefeqs := "d[" ident,* "]"
syntax crushUOrD := crushUnfolds <|> crushDefeqs

/-- `crush` tactic. See the module comment for the hint grammar. -/
syntax (name := crushTac) "crush" crushHints (ppSpace crushUOrD)* : tactic

/-- Resolve an `ident` hint to the constant name it names, erroring helpfully. -/
private def resolveHintConst (i : TSyntax `ident) : TacticM Name := do
  match ← Term.resolveId? i with
  | some (.const n _) => return n
  | some e =>
    match e.getAppFn with
    | .const n _ => return n
    | _ => throwError "crush: `{i}` does not name a constant to unfold."
  | none => throwError "crush: unknown identifier `{i}`."

/-- Gather the equation-lemma names requested by all `u[…]`/`d[…]` groups. `u[f]`
adds `f`'s full equation set; `d[f]` adds its single unfold equation. -/
private def parseUOrDs (stxs : Array (TSyntax ``crushUOrD)) : TacticM (Array Name) := do
  let mut names : Array Name := #[]
  for stx in stxs do
    match stx with
    | `(crushUOrD| u[ $[$is],* ]) =>
      for i in is do
        let n ← resolveHintConst i
        match ← getEqnsFor? n with
        | some eqns => names := names ++ eqns
        | none =>
          -- No equation lemmas (e.g. a non-recursive `def`): fall back to the
          -- unfold equation (`nonRec` so non-recursive defs are covered too).
          match ← getUnfoldEqnFor? n (nonRec := true) with
          | some eqn => names := names.push eqn
          | none => throwError "crush: `{n}` has no equational lemmas to unfold."
    | `(crushUOrD| d[ $[$is],* ]) =>
      for i in is do
        let n ← resolveHintConst i
        match ← getUnfoldEqnFor? n (nonRec := true) with
        | some eqn => names := names.push eqn
        | none => throwError "crush: `{n}` has no unfold equation."
    | _ => throwUnsupportedSyntax
  return names

/-- Parse the `[…]` hint list into elaborated proof terms and the `allHyps` flag. -/
private def parseHintList (goal : MVarId) (stx : TSyntax ``crushHints) :
    TacticM (Array (Expr × String) × Bool) := goal.withContext do
  match stx with
  | `(crushHints| ) =>
    -- No list at all: default to all local hypotheses.
    return (#[], true)
  | `(crushHints| [ $[$elems],* ]) =>
    let mut terms : Array (Expr × String) := #[]
    let mut allHyps := false
    for elem in elems do
      match elem with
      | `(crushHintElem| *) => allHyps := true
      | `(crushHintElem| $t:term) =>
        let e ← Term.elabTerm t none
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        let descr := (t.raw.reprint.getD "hint").trimAscii.toString
        terms := terms.push (e, s!"hint {descr}")
      | _ => throwUnsupportedSyntax
    -- An explicit list without `*` is a *restriction*: only the listed facts.
    return (terms, allHyps)
  | _ => throwUnsupportedSyntax

@[tactic crushTac]
def evalCrush : Tactic := fun stx => do
  let cfg := Config.ofOptions (← getOptions)
  let goal ← getMainGoal
  -- Intro any leading binders so ∀-goals become closed props under hypotheses.
  let (_, goal) ← goal.intros
  replaceMainGoal [goal]
  -- Parse the hint grammar: `crush <hints> <uord>*`.
  let hintsStx : TSyntax ``crushHints := ⟨stx[1]⟩
  let uordStxs := stx[2].getArgs.map (⟨·⟩ : Syntax → TSyntax ``crushUOrD)
  let (terms, allHyps) ← parseHintList goal hintsStx
  let eqnLemmas ← parseUOrDs uordStxs
  let hints : Hints := { terms, eqnLemmas, allHyps }
  runCrush goal cfg hints

end Crush
