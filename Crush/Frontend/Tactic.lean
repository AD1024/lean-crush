import Lean
import Crush.Frontend.Config
import Crush.Reify.Collect
import Crush.Translation.Preprocess
import Crush.Translation.Monomorphize
import Crush.Translation.Instantiate
import Crush.Translation.Translate
import Crush.Translation.DefaultLowerings
import Crush.Util.Profile
import Crush.Solver.Process
import Crush.Solver.KernelCheck
import Crush.Solver.Reconstruct
import Crush.Solver.AletheReplay
import Crush.SMT.Check
import Crush.SMT.Print
import Crush.SMT.Result
open Lean Elab Tactic Meta

/-!
# The `crush` tactic

The end-to-end path:

1. read `Config` from the option environment;
2. collect local `Prop` hypotheses, selected premises, and the negated goal;
3. normalize facts with selected definition equations, then monomorphize them;
4. translate each fact to an `SMT.Term`, asserting it with a `:named crush_fact_N`
   attribute so an unsat core maps back to provenance (`Crush.emitTerm`);
5. build the script (`set-logic`, declarations, assertions, `check-sat`), optionally
   saving/tracing it;
6. run the backend with a hard timeout (`Crush.Solver.runQuery`);
7. discharge: on `unsat`, close the goal per `crush.trust`; on `sat`, report the
   model as a counterexample; on `unknown`/timeout, say so.

Three discharge policies, selected by `crush.trust`:

* `trust` (default) — close with the `crushSorry` axiom. Fast, and what every deployed
  hammer does; the solver and its translation are in the trusted computing base. The
  axiom is auditable, so `#print axioms` names it on any theorem closed this way.
* `reconstruct` — replay the verdict as a checked Lean proof, from the solver's proof
  certificate when there is one (`tryProofReplay`) and otherwise from the unsat core
  (`Crush.tryReconstruct`); error if both fail, so the axiom is never used. A
  translation bug yielding a false `unsat` cannot close a false goal here: it fails
  reconstruction and errors instead.
* `reconstructOrTrust` — reconstruct if possible, else fall back to the axiom with a
  warning, so the fallback is visible rather than silent. The middle ground when a goal
  is genuinely beyond the finishers (nonlinear arithmetic, finite-domain exhaustiveness).
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
initialize registerTraceClass `crush.inst

open SMT

/-- Resolve the SMT-LIB logic string: explicit `crush.logic`, else a permissive
default (`ALL`, or `HO_ALL` when higher-order support must be switched on) passed
through the backend's own mapping.

`BackendSpec.logic` rewrites the default only; an explicit `crush.logic` is
authoritative. -/
def resolveLogic (cfg : Config) : String :=
  match cfg.logic with
  | some l => l
  | none =>
    -- cvc5 gates its higher-order solver on the *logic-string prefix*: `HO_ALL`
    -- turns it on, plain `ALL` does not (its `enableEverything` checks for `HO_`).
    -- Only cvc5 understands the prefix — z3 warns "ignoring unsupported logic" and
    -- carries on, then fails on the function sorts — so we emit it solely when it
    -- will actually be honoured.
    let dflt :=
      if cfg.hoMode == .native && (cfg.backend == .cvc5 || cfg.backend == .none) then
        "HO_ALL"
      else
        "ALL"
    match Solver.backendSpec cfg.backend with
    | some spec => spec.logic dflt
    | none => dflt

/-- Translate all facts into assertion commands, each `:named` for unsat-core
provenance, prepended by the declarations they induce. Returns the full script
(minus `check-sat`) and the final `TranslateState` (for provenance lookup). -/
def buildScript (cfg : Config) (facts : Array Fact) :
    MetaM (Array SMT.Command × TranslateState) := do
  let (_, st) ← TranslateM.run cfg do
    for fact in facts do
      let id ← TranslateM.recordFact fact.descr fact.proof (some fact.prop)
        fact.negationTransform fact.reconstructionProof fact.instanceOf
      let body ← emitTerm fact.prop
      let named := Term.annot body #[.named s!"{factNamePrefix}{id}"]
      TranslateM.emitCommand (.assert named)
  -- Prepend set-logic. Declarations are emitted eagerly on first use (before the
  -- assertion that references them), so command order already satisfies SMT-LIB's
  -- declare-before-reference rule.
  let script := #[Command.setLogic (resolveLogic cfg)] ++ st.commands
  match checkScript script with
  | .ok () => return (script, st)
  | .error err =>
    let command := script[err.commandIndex]?.map commandToString |>.getD "<missing command>"
    let factId? :=
      match script[err.commandIndex]? with
      | some (.assert (.annot _ attrs)) =>
        attrs.findSome? fun
          | SMT.Attr.named name =>
            if name.startsWith factNamePrefix then
              (name.drop factNamePrefix.length).toNat?
            else none
          | _ => none
      | _ => none
    let fact? : Option FactSource := factId?.bind fun id => st.facts[id]?
    let source ←
      match fact? with
      | some fact =>
        match fact.prop with
        | some prop => pure s!"`{toString (← ppExpr prop)}` ({fact.descr})"
        | none => pure fact.descr
      | none => pure s!"generated command {err.commandIndex}"
    throwError "crush: internal SMT sort error while translating {source}: \
      {err.message}\nSMT command: {command}"

/-- Structural tags of symbols that exist only in the higher-order encoding. -/
private def encodingTags : Array String := #["arrow-sort", "arrow-app", "closure"]

/-- Whether the model assigns a value that only the encoding can hold: a symbol from
the higher-order encoding, or a negative integer standing where a `Nat` belongs. -/
private def mentionsEncodedSort (st : TranslateState) (entries : Array ModelEntry) :
    MetaM Bool := do
  for entry in entries do
    if let some tag := st.nameToAtom.get? entry.name then
      if encodingTags.contains tag then return true
    let some origin := st.nameToExpr.get? entry.name | continue
    let isNat ←
      try
        let type ← whnf (← inferType origin)
        pure (type.isConstOf ``Nat)
      catch _ =>
        pure false
    if isNat && entry.value.contains "(- " then return true
  return false

/-- Render a `sat` model into a short message.

Labels come from `nameToExpr`, the Lean head a symbol was allocated for; `nameToAtom`
holds only a structural key's tag, which several distinct symbols share. Entries named
`crush_fact_<n>` are the solver echoing our own named assertions and are dropped. -/
def formatCounterexample (modelText : String) (st : TranslateState) :
    MetaM MessageData := do
  let entries := (parseModel modelText).filter fun e => !e.name.startsWith factNamePrefix
  if entries.isEmpty then
    return m!"model (no assignments to report)"
  let labels ← entries.mapM fun entry =>
    match st.nameToExpr.get? entry.name with
    | some origin => return toString (← ppExpr origin)
    | none => return entry.name
  let mut labelCounts : Std.HashMap String Nat := {}
  for label in labels do
    labelCounts := labelCounts.insert label (labelCounts.getD label 0 + 1)
  let mut lines : Array MessageData := #[]
  for i in [0:entries.size] do
    let e := entries[i]!
    let baseLabel := labels[i]!
    let label :=
      if labelCounts.getD baseLabel 0 > 1 then s!"{baseLabel} [{e.name}]"
      else baseLabel
    lines := lines.push m!"  {label} := {e.value}"
  let body := m!"model:{indentD (MessageData.joinSep lines.toList "\n")}"
  if ← mentionsEncodedSort st entries then
    return body ++ m!"\nSome values above are in encoding sorts (`Nat` as `Int`, \
                      functions as an uninterpreted sort), where a model need not \
                      describe any Lean value."
  return body

/-- Try to close `goal` by replaying the solver's proof certificate
(`Crush/Solver/AletheReplay.lean`).

The certificate refutes the *negated* goal, so the shape is a proof by contradiction:
`Classical.byContradiction` turns `G` into `¬G ⊢ False`, the fresh `¬G` hypothesis is bound
to the certificate's assumption for the negated goal (the thing being refuted, so it has no
Lean proof of its own), and replay produces the `False`.

Returns `false`, leaving `goal` untouched, whenever anything is missing or a step cannot be
replayed — so the caller falls back to the finisher ladder. -/
def tryProofReplay (goal : MVarId) (cfg : Config) (st : TranslateState)
    (proofSexps : Array SMT.Sexp) : TacticM Bool := do
  if cfg.reconstruct == .core then return false
  if proofSexps.isEmpty then return false
  let some proof := Alethe.parseProofSexps proofSexps | return false
  goal.withContext do
    let saved ← saveState
    let snapshot ← KernelCheckSnapshot.capture
    try
      -- `byContradiction` gives us `¬G` as a hypothesis and `False` as the goal.
      let goalType ← instantiateMVars (← goal.getType)
      let negGoal ← mkAppM ``Not #[goalType]
      let res ← withLocalDeclD `hneg negGoal fun hneg => do
        -- Map each `crush_fact_<n>` assumption to a Lean proof: a real hypothesis for an
        -- asserted fact, and the freshly-introduced `¬G` for the negated goal.
        let mut facts : Std.HashMap String Expr := {}
        for src in st.facts do
          let name := s!"{factNamePrefix}{src.id}"
          match src.proof with
          | some p =>
            facts := facts.insert name p
          | none =>
            let proof := src.negationTransform.map (fun transform => mkApp transform hneg)
              |>.getD hneg
            facts := facts.insert name proof
        let some falseProof ← Alethe.replay? proof proofSexps facts st.nameToExpr
          | return none
        return some (← mkLambdaFVars #[hneg] falseProof)
      match res with
      | none =>
        restoreState saved
        return false
      | some lam =>
        -- Assemble `byContradiction (fun hneg => falseProof)` and hand it to the kernel.
        let pf ← mkAppOptM ``Classical.byContradiction #[some goalType, some lam]
        goal.assign (← kernelCheckProof snapshot goalType pf)
        return true
    catch e =>
      trace[crush.result] "alethe replay: declined during final kernel validation \
                           ({e.toMessageData})"
      restoreState saved
      return false

/-- Close a goal that is already one of the selected facts.

Checking only `facts` preserves the strict meaning of `crush [h₁, ...]`: an ambient
hypothesis omitted by the user cannot be used by this fast path. This runs before
translation because quantified nonlinear assumptions can otherwise make an identity query
expensive for SMT despite the Lean proof being a single local constant. -/
private def closeFromSelectedFacts (goal : MVarId) (facts : Array Fact) : TacticM Bool :=
  goal.withContext do
    let snapshot ← KernelCheckSnapshot.capture
    let target ← instantiateMVars (← goal.getType)
    for fact in facts do
      let some proof := fact.proof | continue
      let saved ← saveState
      try
        let proof ← instantiateMVars proof
        if ← isDefEqGuarded (← inferType proof) target then
          let proof ← instantiateMVars proof
          goal.assign (← kernelCheckProof snapshot target proof)
          return true
        restoreState saved
      catch _ => restoreState saved
    return false

/-- The core driver, given a resolved goal, config, and collected hints. -/
def runCrush (goal : MVarId) (cfg : Config) (hints : Hints := {}) : TacticM Unit :=
  goal.withContext do
  -- `native` HO mode needs cvc5, or `none` when the script is only being emitted.
  -- z3 prints "ignoring unsupported logic" and then chokes on the function sorts,
  -- so fall back to the portable encoding rather than sending it an invalid query.
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
  let premiseMax :=
    if cfg.premises && hints.allowPremiseSelection then cfg.premiseMax else 0
  let (collected, prof') ←
    prof.time "collect" (collectFactsWithRewrite goal hints cfg.autoUnfold premiseMax)
  prof := prof'
  trace[crush] "selected {collected.selectedPremises} library premise(s)"
  -- `backend = none` is an emission/debugging mode, so it must still produce the script
  -- even when Lean can close the goal without consulting a solver.
  if cfg.backend != .none then
    if ← closeFromSelectedFacts goal collected.facts then
      trace[crush.result] "goal is one of the selected facts; skipped SMT"
      if cfg.profile then logInfo prof.report
      return
    let (closed, prof') ←
      prof.time "pre-reconstruct"
        (tryPreReconstruct goal collected.facts (selectedRuleSearch := cfg.trust != .trust))
    prof := prof'
    if closed then
      trace[crush.result] "pre-translation checked proof succeeded; skipped SMT"
      if cfg.profile then logInfo prof.report
      return
  let (normalized, prof') ←
    prof.time "normalize" (normalizeFacts collected.facts collected.rewriteLemmas)
  prof := prof'
  trace[crush] "normalized {normalized.rewritten} fact(s) with \
                {collected.rewriteLemmas.size} selected equation lemma(s)"
  let facts := normalized.facts
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
  let (instantiated, prof') ←
    prof.time "instantiate" (instantiateGroundFacts cfg facts)
  prof := prof'
  let fullFacts := instantiated.facts
  trace[crush.inst] "generated {instantiated.generated} ground instance(s); \
                     exhausted: {instantiated.exhausted}"
  if instantiated.exhausted then
    logWarning m!"crush: ground instantiation hit its bound after \
                  {instantiated.generated} instance(s) (`crush.inst.fuel` = \
                  {cfg.instFuel}, `crush.inst.rounds` = {cfg.instRounds}); \
                  raise the bound if an explicit lemma is not being instantiated."
  -- Try the soundly weakened ground-only query first. `unsat` is conclusive;
  -- every other verdict retries with the complete quantified fact set.
  let reducedFacts :=
    if cfg.backend == .none then none else instantiated.groundFacts
  let firstFacts := reducedFacts.getD fullFacts
  let ((firstScript, firstSt), prof') ← prof.time "translate" (buildScript cfg firstFacts)
  prof := prof'
  let mut script := firstScript
  let mut st := firstSt
  if cfg.traceScript then
    logInfo m!"crush SMT script:{indentD (scriptToString script)}"
  trace[crush.script] "{scriptToString script}"
  if cfg.backend == .none then
    Solver.maybeSave cfg script
    logInfo m!"crush: backend is `none`; emitted {script.size} commands, no solver run."
    if cfg.profile then logInfo prof.report
    return
  -- Saved before the run, so a query that throws still leaves its script on disk.
  Solver.maybeSave cfg script
  let (firstResult, prof') ← prof.time "solve" (Solver.runQuery cfg script)
  prof := prof'
  let mut result := firstResult
  if reducedFacts.isSome then
    match result with
    | .unsat .. =>
      trace[crush.result] "ground-instance query was unsatisfiable; skipped quantified fallback"
    | .sat .. | .unknown .. =>
      trace[crush.result] "ground-instance query did not close the goal; retrying with \
                           retained quantified templates"
      let ((fallbackScript, fallbackSt), prof') ←
        prof.time "translate-fallback" (buildScript cfg fullFacts)
      prof := prof'
      script := fallbackScript
      st := fallbackSt
      if cfg.traceScript then
        logInfo m!"crush SMT fallback script:{indentD (scriptToString script)}"
      trace[crush.script] "{scriptToString script}"
      Solver.maybeSave cfg script
      let (fallbackResult, prof') ←
        prof.time "solve-fallback" (Solver.runQuery cfg script)
      prof := prof'
      result := fallbackResult
  match result with
  | .unsat coreSexp proofSexps =>
    let coreIds := unsatCoreFactIds coreSexp
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
      -- Certificate replay first (unless `crush.reconstruct core` opts out): it closes
      -- goals the single-shot ladder cannot (long chains of trivial steps — Boolean
      -- pigeonhole, deep EUF conflicts) because the chain is already found. A step it
      -- cannot replay falls through to the ladder below.
      let (replayed, prof') ← prof.time "replay" (tryProofReplay goal cfg st proofSexps)
      prof := prof'
      if replayed then
        trace[crush.result] "proof replay succeeded; no axiom used"
        if cfg.profile then logInfo prof.report
        return
      -- `alethe` mode deliberately has no fallback: it is for working on replay itself,
      -- where the ladder silently closing the goal would hide whether replay worked.
      if cfg.reconstruct == .alethe then
        throwError m!"crush: `crush.reconstruct alethe` is set and the solver's Alethe \
                      certificate could not be replayed. Set `crush.reconstruct` to \
                      \"auto\" to fall back to the core-directed finishers, or enable \
                      `trace.crush.result` to see which step declined."
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
    -- The verdict is about the encoding, which is incomplete in places, so the message
    -- reports a model rather than claiming the Lean goal is false.
    throwError m!"crush: could not prove the goal — the solver found a \
                  {← formatCounterexample modelText st}\n\
                  The encoding is incomplete, so a model does not necessarily \
                  describe a Lean counterexample."
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

/-- Parse the `[…]` hint list into elaborated proof terms and local-hypothesis flags. -/
private def parseHintList (goal : MVarId) (stx : TSyntax ``crushHints) :
    TacticM (Array (Expr × String) × Bool × Bool × Bool) := goal.withContext do
  match stx with
  | `(crushHints| ) =>
    -- No list at all: send every local hypothesis to SMT, but reserve eager
    -- proof-producing instantiation for hypotheses explicitly selected by `*`.
    return (#[], true, false, true)
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
    return (terms, allHyps, allHyps, false)
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
  let (terms, allHyps, instantiateHyps, allowPremiseSelection) ←
    parseHintList goal hintsStx
  let eqnLemmas ← parseUOrDs uordStxs
  let hints : Hints := {
    terms, eqnLemmas, allHyps, instantiateHyps, allowPremiseSelection }
  runCrush goal cfg hints

end Crush
