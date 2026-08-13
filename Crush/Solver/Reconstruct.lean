import Lean
import Crush.Frontend.Config
import Crush.Reify.Collect
import Crush.SMT.Result
import Crush.Solver.ReconstructRules
open Lean Meta Elab Tactic

/-!
# Turning an `unsat` verdict into a checked Lean proof

The `trust` policy closes a goal with an axiom: the solver said `unsat`, we believe
it. That is fast and it is what every deployed hammer does by default, but the
solver's translation and the solver itself both sit in the trusted computing base.

This module implements the *solver-as-oracle* model instead. The solver's real
contribution is not the proof object — it is the **selection**: out of a context
with dozens of hypotheses, the unsat core names the two or three that actually
matter. That is exactly the information a Lean-side automated tactic lacks. So:

1. take the unsat core, mapping each `crush_fact_<n>` back to its Lean hypothesis;
2. build a goal whose context is *only* those hypotheses;
3. hand it to a Lean finishing tactic (`grind`, then `omega`).

If the finisher succeeds we have a kernel-checked proof and the solver drops out of
the trusted base entirely — it was only a search heuristic. If it fails we report
that honestly rather than silently falling back to the axiom (unless the policy
explicitly says to).

Why this works when calling the finisher on the *whole* context often does not:
automated tactics degrade badly as the hypothesis count grows, and irrelevant
arithmetic facts are exactly what makes them time out. Core-directed selection
turns a 40-hypothesis goal into a 3-hypothesis goal.

Some verdicts turn on a constructor case analysis instead, which no fixed tactic string can
perform — the required step names a variable. Those are handled after the ladder by the
programmatic pre-pass below.

This is the general path, tried for every backend. It does depend on a Lean tactic
re-finding the argument, which fails for long inference chains; when cvc5 supplies an
Alethe certificate, `Crush/Solver/AletheReplay.lean` runs first and replays the chain
step by step instead. Both end in a kernel-checked term, so they differ only in reach.
-/

namespace Crush

initialize registerTraceClass `crush.reconstruct

/-- The hypotheses named by an unsat core, deduplicated and in context order.

Fact ids index `TranslateState.facts`; entries with no `proof` (the negated goal)
are skipped, since the goal is not a hypothesis to feed the finisher. Ids that fall
outside the table are ignored rather than fatal: a solver is free to name anything
in its core, and a malformed name should not crash the tactic. -/
def coreHypotheses (st : TranslateState) (coreIds : Array Nat) : Array Expr := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut seenProofs : Std.HashSet Expr := {}
  let mut out : Array Expr := #[]
  for id in coreIds do
    if seen.contains id then continue
    seen := seen.insert id
    if let some src := st.facts[id]? then
      if let some proof := src.proof then
        unless seenProofs.contains proof do
          seenProofs := seenProofs.insert proof
          out := out.push proof
  -- Preserve compatibility with fact producers that emit a quantified parent
  -- together with generated instances. Ground instantiation replaces eligible
  -- successful parents, so those generated proofs are selected directly above.
  for src in st.facts do
    if let some parent := src.instanceOf then
      if seenProofs.contains parent then
        if let some proof := src.proof then
          unless seenProofs.contains proof do
            seenProofs := seenProofs.insert proof
            out := out.push proof
  -- Preprocessing can make the negated assertion independent of the equations
  -- that produced it, so the solver omits them from the core. Supply the exact,
  -- specialized equality between the original and normalized negated goals
  -- rather than every raw polymorphic equation.
  for src in st.facts do
    if let some proof := src.reconstructionProof then
      unless seenProofs.contains proof do
        seenProofs := seenProofs.insert proof
        out := out.push proof
  return out

/-- Human-readable provenance for the core, for diagnostics. -/
def coreDescriptions (st : TranslateState) (coreIds : Array Nat) : Array String := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array String := #[]
  for id in coreIds do
    if seen.contains id then continue
    seen := seen.insert id
    if let some src := st.facts[id]? then
      out := out.push src.descr
  return out

/-- The finishing tactics tried, in order, on the core-restricted goal.

Reconstruction does not know *why* the solver said `unsat`, so the ladder is a fixed
set of closers, ordered by rising cost, each aimed at a goal shape the solver commonly
produces. `tryReconstruct` backtracks and takes the first that closes the goal; a
mis-fitting rung fails fast. `intros` heads every entry because the goal is the
implication `h₁ → … → hₙ → concl` built from the core.

The shape → rung map:

* **arithmetic / congruence / case-split** → `grind` (general closer), then `omega`
  (complete for linear `Int`/`Nat`, catching what `grind` may not finish).
* **propositional / rewriting** → `simp_all`.
* **function equality `f = g`** (a higher-order verdict — a Church-numeral identity,
  β-through-a-closure) → the `funext`/`ext` rungs: `funext` reduces it to the pointwise
  `f x̄ = g x̄`, then a first-order closer finishes the body. `repeat'` strips every
  arrow rather than a fixed one or two, so the rung is arity-general. The parentheses
  around it are load-bearing: `repeat' funext _ <;> simp_all` would parse as
  `repeat' (funext _ <;> simp_all)`, which only closes the arity-1 case. Harmless on a
  non-function equality (`funext` fails cleanly), hence after the common case.
* **WP state aliases** (`arr = arr' ∧ i = i'`) → `subst_vars; grind`, after direct
  `grind`/`simp_all` have declined.
* **ground evaluation** (`String.length "ab" = 2`) → `subst_vars` then `decide`/`rfl`.
  The reasoning closers rewrite and case-split but never *compute*; `subst_vars`
  replaces variables with the values the core's equations pin, then `decide`/`rfl`
  evaluates the now-closed term. Last, because `decide` is the costliest rung.

Kept as syntax rather than names so each is elaborated once, here, where a typo is
a build error instead of a runtime "unknown tactic". -/
def finisherTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| (intros; grind))),
    (← `(tactic| (intros; omega))),
    (← `(tactic| (intros; simp_all))),
    (← `(tactic| (intros; (repeat' funext _) <;> simp_all))),
    (← `(tactic| (intros; ext; grind))),
    (← `(tactic| (intros; subst_vars; grind))),
    (← `(tactic| (intros; subst_vars; decide))),
    (← `(tactic| (intros; subst_vars; rfl))),
    (← `(tactic| (intros; simp_all; decide)))]

/-- Finishers for constructor branches, ordered from cheap normalization to saturation.

`grind` is last because constructor normalization can expose nonlinear facts that it could
not use on the unsplit target. Candidate filtering and branch budgets keep that final rung
from being applied to hidden datatypes inside unrelated atomic terms. -/
private def structuralFinisherTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| omega)),
    (← `(tactic| simp_all)),
    (← `(tactic| rfl)),
    (← `(tactic| decide)),
    (← `(tactic| grind))]

/-- Cheap finishers used to validate an equality split.

The split is only useful when disequality turns a missing strict premise into a direct
arithmetic or simplification consequence. In particular, do not run `grind` here: a
quantified array invariant can match the target while still requiring substantial
unrelated reasoning, and speculative saturation for each equality pair is too costly. -/
private def equalityFinisherTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| omega)),
    (← `(tactic| simp_all)),
    (← `(tactic| rfl)),
    (← `(tactic| decide))]

/-- Cheap premise closers for selected backward rules.

This pre-SMT path must stay much cheaper than the full reconstruction portfolio:
exact assumptions and bounded rule chaining run inside `finishOne`; these tactics
cover the remaining arithmetic, conjunction-unpacking, and definitional premises
without invoking `grind` or constructor search. -/
private def selectedRuleFinisherTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| omega)),
    (← `(tactic| simp_all only)),
    (← `(tactic| rfl)),
    (← `(tactic| decide))]

/-- Cheap finishers for the pre-SMT one-level datatype split.

Unlike post-verdict reconstruction this path runs on ordinary solver-bound goals, so it
does not invoke `grind`. Constructor reduction plus `simp_all` covers recursive equations
at a concrete constructor, while `omega`, `rfl`, and `decide` handle the resulting leaves. -/
private def preStructuralFinisherTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| simp_all)),
    (← `(tactic| omega)),
    (← `(tactic| rfl)),
    (← `(tactic| decide))]

/-- Constructor finishers for contexts beyond the global-simp premise budget. -/
private def safePreStructuralFinisherTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| simp_all only)),
    (← `(tactic| omega)),
    (← `(tactic| rfl)),
    (← `(tactic| decide))]

/-- Full-context simplification is reserved for small, isolated pre-SMT proof problems.

The pre-pass is speculative, so its work must not grow with an arbitrary collection of
solver hints. Beyond this bound, the safe finishers use only definitional reduction and
selected local facts; the original goal then proceeds to SMT unchanged. -/
private def useGlobalSimpPrepass (proofs : Array Expr) : Bool :=
  proofs.size ≤ 6

/-! ## Bounded datatype case search

Some verdicts turn on a *constructor case analysis*: datatype exhaustiveness
(`t = .leaf ∨ ∃ l v r, t = .node l v r`) and structure eta
(`p.x = q.x → p.y = q.y → p = q`). No rung reaches these, because the step they need is
`cases t` — naming a variable a *fixed* tactic string cannot know.

The search is datatype-generic: it considers every constructor-bearing local value that
occurs in the target, including theory-backed inductives such as `Nat` and `Bool`. It tries
each candidate independently instead of committing to the first one; this is important for
goals such as `f (n - 1)`, where splitting another `Nat` in the target is useless but
splitting `n` exposes exactly the zero/successor boundary.

Depth, candidate, constructor, and branch caps make recursive or high-arity datatypes a
bounded fallback rather than an accidental induction procedure. -/

private def splittableFVars (g : MVarId) (onlyFiniteEnums := false)
    (onlyTargetArgumentTypes := false) :
    MetaM (Array FVarId) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  let mut targetArgumentTypes := #[]
  if onlyTargetArgumentTypes then
    for argument in target.getAppArgs do
      try
        targetArgumentTypes := targetArgumentTypes.push (← inferType argument)
      catch _ => pure ()
  let mut out := #[]
  for d in ← getLCtx do
    if out.size >= 8 then break
    if d.isImplementationDetail then continue
    unless target.containsFVar d.fvarId do continue
    let ty ← whnf d.type
    if onlyTargetArgumentTypes then
      let mut matchesArgumentType := false
      for argumentType in targetArgumentTypes do
        if ← isDefEqGuarded ty argumentType then
          matchesArgumentType := true
          break
      unless matchesArgumentType do continue
    let .const n _ := ty.getAppFn | continue
    let some (.inductInfo iv) := (← getEnv).find? n | continue
    if iv.ctors.length > 16 then continue
    if onlyFiniteEnums then
      let mut fieldFree := true
      for ctorName in iv.ctors do
        let some (.ctorInfo ctorInfo) := (← getEnv).find? ctorName
          | fieldFree := false; break
        if ctorInfo.numFields != 0 then
          fieldFree := false
          break
      unless fieldFree do continue
    out := out.push d.fvarId
  trace[crush.reconstruct] "constructor candidates: {out.map (·.name)}"
  return out

/-- Whether a target is small enough for speculative non-enum case analysis.

Logical constructors and recursor-headed targets receive a larger budget because case
analysis directly simplifies their shape. Atomic targets still benefit when constructor
normalization exposes a small arithmetic or datatype boundary, but large atomic terms such
as nested array updates are rejected before recursive splitting. `approxDepth` is stored on
`Expr`, so this gate is constant-time. Field-free finite enums are handled separately. -/
private def exposesConstructorStructure (target : Expr) : MetaM Bool := do
  -- Preserve logical wrappers before `whnf`: `Ne` and `Not` unfold to function
  -- types, which would otherwise make a disequality look like an atomic target and
  -- hide constructor-bearing values nested in its operands.
  let rawExposesStructure :=
    target.isEq || target.isHEq ||
    target.isAppOfArity ``Ne 3 || target.isAppOfArity ``Not 1 ||
    target.isAppOfArity ``And 2 || target.isAppOfArity ``Or 2 ||
    target.isAppOfArity ``Exists 2 || target.isAppOfArity ``Iff 2
  if rawExposesStructure then return true
  let target ← whnf target
  let exposesStructure := target.isEq || target.isHEq ||
      target.isAppOfArity ``And 2 || target.isAppOfArity ``Or 2 ||
      target.isAppOfArity ``Exists 2 || target.isAppOfArity ``Iff 2
  if exposesStructure then return true
  match target.getAppFn with
  | .const targetHead _ =>
    let env ← getEnv
    return match env.find? targetHead with
      | some (.recInfo _) => true
      | _ => false
  | _ => return false

private def supportsStructuralSplitting (target : Expr) : MetaM Bool := do
  let target ← whnf target
  let exposesStructure ← exposesConstructorStructure target
  let maxDepth := if exposesStructure then 64 else 24
  trace[crush.reconstruct] "structural target depth: {target.approxDepth}; budget: {maxDepth}"
  return target.approxDepth.toNat ≤ maxDepth

/-- Expose facts packed into conjunction-valued WP state hypotheses. This is bounded and
proposition-generic; it does not inspect the names or types of the conjuncts. -/
private partial def destructAndHypotheses (g : MVarId) (fuel : Nat := 8) :
    TacticM MVarId := g.withContext do
  if fuel == 0 then return g
  for localDecl in ← getLCtx do
    let type ← whnf localDecl.type
    unless type.isAppOfArity ``And 2 do continue
    let branches ← g.cases localDecl.fvarId
    let #[branch] := branches | return g
    return ← destructAndHypotheses branch.mvarId (fuel - 1)
  return g

/-- Decompose equalities between applications of the same constructor.

WP state is commonly packed into products or downstream structures. An equality between
two such states carries component aliases that `subst_vars` cannot see until constructor
injectivity has been exposed. Restricting this to constructor-headed equalities avoids
speculative case analysis on arbitrary equations. -/
private partial def destructConstructorEqualities (g : MVarId) (fuel : Nat := 8) :
    TacticM MVarId := g.withContext do
  if fuel == 0 then return g
  for localDecl in ← getLCtx do
    let type ← whnf localDecl.type
    unless type.isAppOfArity ``Eq 3 do continue
    let args := type.getAppArgs
    let .const lhsName _ := args[1]!.getAppFn | continue
    let .const rhsName _ := args[2]!.getAppFn | continue
    unless lhsName == rhsName do continue
    let some (.ctorInfo _) := (← getEnv).find? lhsName | continue
    let branches ← g.cases localDecl.fvarId
    let #[branch] := branches | return g
    return ← destructConstructorEqualities branch.mvarId (fuel - 1)
  return g

/-- The head constant of a proposition after removing all theorem premises. -/
private partial def conclusionHead? (type : Expr) : MetaM (Option Name) := do
  let type ← whnf type
  match type with
  | .forallE _ _ body _ => conclusionHead? body
  | .letE _ _ value body _ => conclusionHead? (body.instantiate1 value)
  | _ =>
    let .const name _ := type.getAppFn | return none
    return some name

/-- Whether a quantified local hypothesis can be applied to the current target.

This is a speculative unification check with full state rollback. It gates equality case
analysis so unrelated goals sharing only an outer relation such as `LE.le` do not branch. -/
private def hasApplicableLocalRule (g : MVarId) : TacticM Bool := g.withContext do
  let target ← instantiateMVars (← g.getType)
  let some targetHead ← conclusionHead? target | return false
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail || !localDecl.type.isForall then continue
    unless (← conclusionHead? localDecl.type) == some targetHead do continue
    let saved ← saveState
    try
      discard <| g.apply (mkFVar localDecl.fvarId)
      restoreState saved
      return true
    catch _ => restoreState saved
  return false

mutual

  /-- Close one goal by exact hypothesis, a bounded registered-rule chain, or a standard
  finisher, restoring every failed attempt. Rules precede the general tactics so a cheap
  domain bridge is not hidden behind an expensive failed `grind`. -/
  private partial def finishOne (g : MVarId) (finishers : Array (TSyntax `tactic))
      (ruleFuel : Nat := 2) : TacticM Bool := g.withContext do
    if ← g.isAssigned then return true
    unless ← isProp (← instantiateMVars (← g.getType)) do return false
    let saved ← saveState
    try
      if ← g.assumptionCore then
        let proof ← instantiateMVars (mkMVar g)
        unless proof.hasSorry || proof.hasMVar do return true
      restoreState saved
    catch _ => restoreState saved
    -- A premise with unconstrained theorem parameters must be anchored by an exact
    -- contextual fact before recursive search. Sending such a goal to `grind` can explore
    -- arbitrary instantiations and turn an unrelated generic rule into a major slowdown.
    if (← instantiateMVars (← g.getType)).hasMVar then
      trace[crush.reconstruct] "declined unanchored rule premise: {← g.getType}"
      return false
    if ruleFuel > 0 then
      if ← finishWithLocalRules g finishers ruleFuel then return true
      if ← finishWithRegisteredRules g finishers ruleFuel then return true
    for tac in finishers do
      let saved ← saveState
      try
        if (← Tactic.run g (evalTactic tac)).isEmpty then
          let proof ← instantiateMVars (mkMVar g)
          unless proof.hasSorry || proof.hasMVar do return true
        restoreState saved
      catch _ => restoreState saved
    if ruleFuel > 0 then
      if ← finishWithEqualitySplits g then return true
    return false

  /-- Split equality between target variables after direct finishers have failed.

  Quantified invariants often cover a strict index relation while the goal uses its
  reflexive closure. The equal branch reduces by reflexivity; the unequal branch lets
  arithmetic derive strictness and backward-apply the invariant. Candidate and recursion
  bounds keep this from becoming unrestricted excluded-middle search. -/
  private partial def finishWithEqualitySplits (g : MVarId) : TacticM Bool :=
    g.withContext do
    unless ← hasApplicableLocalRule g do return false
    let target ← instantiateMVars (← g.getType)
    let fvars := (Lean.collectFVars {} target).fvarIds
    let mut tried := 0
    for i in [0:fvars.size] do
      for j in [i + 1:fvars.size] do
        if tried >= 3 then return false
        let lhs := mkFVar fvars[i]!
        let rhs := mkFVar fvars[j]!
        unless ← isDefEqGuarded (← inferType lhs) (← inferType rhs) do continue
        let proposition ← mkEq lhs rhs
        let negation := mkNot proposition
        let mut alreadySplit := false
        for localDecl in ← getLCtx do
          if ← isDefEqGuarded localDecl.type proposition then
            alreadySplit := true
            break
          if ← isDefEqGuarded localDecl.type negation then
            alreadySplit := true
            break
        if alreadySplit then continue
        tried := tried + 1
        let saved ← saveState
        try
          let (equal, unequal) ← g.byCases proposition `hEq
          trace[crush.reconstruct] "split target equality {proposition}"
          let cheapFinishers ← equalityFinisherTactics
          -- The unequal branch must be justified by a quantified local rule whose
          -- premises become cheap consequences of the new disequality. Falling back to
          -- the full ladder here made speculative splits saturate unrelated array VCs.
          if (← finishOne equal.mvarId cheapFinishers 0) &&
              (← finishWithLocalRules unequal.mvarId cheapFinishers 1) then
            let proof ← instantiateMVars (mkMVar g)
            unless proof.hasSorry || proof.hasMVar do return true
          restoreState saved
        catch _ => restoreState saved
    return false

  /-- Backward-apply quantified core hypotheses with the same conclusion head.

  This recovers the common invariant pattern where SMT instantiates a local `∀`, but the
  unsat core contains only the quantified hypothesis. Head filtering and bounded recursion
  avoid handing the entire context to an unrestricted `solve_by_elim` search. -/
  private partial def finishWithLocalRules (g : MVarId)
      (finishers : Array (TSyntax `tactic)) (ruleFuel : Nat) : TacticM Bool :=
    g.withContext do
    let target ← instantiateMVars (← g.getType)
    let some targetHead ← conclusionHead? target | return false
    let mut tried := 0
    for localDecl in ← getLCtx do
      if tried >= 16 then break
      if localDecl.isImplementationDetail || !localDecl.type.isForall then continue
      unless (← conclusionHead? localDecl.type) == some targetHead do continue
      tried := tried + 1
      let saved ← saveState
      try
        let subgoals ← g.apply (mkFVar localDecl.fvarId)
        trace[crush.reconstruct] "applied local reconstruction rule {localDecl.userName} \
          with {subgoals.length} premise(s)"
        let mut closed := true
        for subgoal in subgoals do
          unless ← finishOne subgoal finishers (ruleFuel - 1) do
            closed := false
            break
        if closed then
          let proof ← instantiateMVars (mkMVar g)
          unless proof.hasSorry || proof.hasMVar do return true
        restoreState saved
      catch _ => restoreState saved
    return false

  /-- Apply one registered theorem at a time, then close each generated premise.

  This explicit bounded search avoids giving an unrelated global rule set to
  `solve_by_elim` or `grind`, where rules with a shared conclusion relation can
  combine exponentially. -/
  private partial def finishWithRegisteredRules (g : MVarId)
      (finishers : Array (TSyntax `tactic)) (ruleFuel : Nat) : TacticM Bool :=
    g.withContext do
    let target ← instantiateMVars (← g.getType)
    let candidates ← reconstructionLemmasFor target
    trace[crush.reconstruct] "registered-rule target: {target}; candidates: {candidates}"
    for ruleName in candidates do
      let saved ← saveState
      try
        let subgoals ← g.apply (← mkConstWithFreshMVarLevels ruleName)
        trace[crush.reconstruct] "applied reconstruction rule {ruleName} with \
          {subgoals.length} premise(s)"
        let mut closed := true
        for subgoal in subgoals do
          trace[crush.reconstruct] "rule premise: {← subgoal.getType}"
          unless ← finishOne subgoal finishers (ruleFuel - 1) do
            closed := false
            break
        if closed then
          let proof ← instantiateMVars (mkMVar g)
          unless proof.hasSorry || proof.hasMVar do return true
        restoreState saved
      catch _ => restoreState saved
    return false

end

/-- Reducible declarations visible in an expression, capped before unfolding.

This deliberately selects only declarations explicitly marked `@[reducible]`.
Regular definitions are not speculative normalization hints, and unfolding them
would make witness and constructor search depend on arbitrary implementation detail. -/
private partial def reducibleConstants (e : Expr) (names : Array Name := #[])
    (limit : Nat := 8) : MetaM (Array Name) := do
  if names.size >= limit then return names
  match e with
  | .const name _ =>
    if !names.contains name && (← Lean.isReducible name) then
      return names.push name
    return names
  | .app fn arg =>
    let names ← reducibleConstants fn names limit
    reducibleConstants arg names limit
  | .lam _ type body _ | .forallE _ type body _ =>
    let names ← reducibleConstants type names limit
    reducibleConstants body names limit
  | .letE _ type value body _ =>
    let names ← reducibleConstants type names limit
    let names ← reducibleConstants value names limit
    reducibleConstants body names limit
  | .mdata _ body | .proj _ _ body =>
    reducibleConstants body names limit
  | _ => return names

/-- Recursively expose explicitly reducible wrappers, with a hard depth bound.

`whnf` is run at reducible transparency, so regular definitions remain opaque.
Binders are opened with fresh local constants before recursively normalizing their
bodies; calling `whnf` directly on a body with loose de Bruijn variables is invalid. -/
private partial def reduceReducible (e : Expr) (depth : Nat := 8) : MetaM Expr := do
  if depth == 0 then return e
  let e ← withReducible <| whnf e
  let next := depth - 1
  match e with
  | .app fn arg =>
    return mkApp (← reduceReducible fn next) (← reduceReducible arg next)
  | .lam name type body binderInfo =>
    let type ← reduceReducible type next
    withLocalDecl name binderInfo type fun binder => do
      let body ← reduceReducible (body.instantiate1 binder) next
      mkLambdaFVars #[binder] body
  | .forallE name type body binderInfo =>
    let type ← reduceReducible type next
    withLocalDecl name binderInfo type fun binder => do
      let body ← reduceReducible (body.instantiate1 binder) next
      mkForallFVars #[binder] body
  | .letE _ _ value body _ =>
    reduceReducible (body.instantiate1 value) next
  | .mdata data body =>
    return .mdata data (← reduceReducible body next)
  | .proj typeName index body =>
    return .proj typeName index (← reduceReducible body next)
  | _ => return e

/-- Definitionally normalize reducible wrappers exposed by a concrete constructor. -/
private def unfoldReducibleTarget (g : MVarId) : TacticM MVarId := g.withContext do
  let target ← instantiateMVars (← g.getType)
  if (← reducibleConstants target).isEmpty then return g
  let reduced ← reduceReducible target
  if reduced == target then return g
  withReducible <| g.replaceTargetDefEq reduced

/-- Backtracking constructor search. Every branch must close; otherwise the attempted split
is rolled back before trying another target variable. -/
private partial def splitSearch (g : MVarId) (finishers : Array (TSyntax `tactic))
    (fuel : Nat) (branchBudget : IO.Ref Nat) (finishCurrent := true)
    (onlyFiniteEnums := false) (onlyTargetArgumentTypes := false)
    (ruleFuel : Nat := 2) : TacticM Bool :=
    g.withContext do
  if finishCurrent && (← finishOne g finishers ruleFuel) then return true
  if fuel == 0 then return false
  for fv in ← splittableFVars g onlyFiniteEnums onlyTargetArgumentTypes do
    if (← branchBudget.get) == 0 then return false
    let saved ← saveState
    try
      let branches := (← g.cases fv).map (·.mvarId)
      trace[crush.reconstruct] "split {fv.name} into {branches.size} branch(es)"
      let remaining ← branchBudget.get
      if branches.size > 16 || branches.size > remaining then
        restoreState saved
        continue
      branchBudget.set (remaining - branches.size)
      let mut closed := true
      for rawBranch in branches do
        let branch ← unfoldReducibleTarget rawBranch
        unless ← splitSearch branch finishers (fuel - 1) branchBudget
            (onlyFiniteEnums := onlyFiniteEnums)
            (onlyTargetArgumentTypes := onlyTargetArgumentTypes)
            (ruleFuel := ruleFuel) do
          closed := false
          break
      if closed then return true
      trace[crush.reconstruct] "split {fv.name} did not close every branch"
      restoreState saved
    catch e =>
      trace[crush.reconstruct] "constructor split declined: {e.toMessageData}"
      restoreState saved
  return false

/-! ## Constructor-guided existential witnesses

An SMT refutation can establish an existential goal without returning a witness, while a
direct Lean proof needs one. Hard-coding arithmetic witnesses does not generalize beyond
`Nat`. Instead, collect target-independent subterms from the predicate and close over the
witness type's constructors for two bounded rounds. For `∃ n, t < n`, this discovers
`Nat.succ t`; the same search builds `some x`, list constructors, or downstream inductive
values when their fields are present in the goal.
-/

private partial def collectSubterms (e : Expr) (terms : Array Expr := #[]) :
    Array Expr := Id.run do
  let mut terms := terms
  if terms.size < 48 && !e.hasLooseBVars && !e.hasMVar && !terms.contains e then
    match e with
    | .bvar _ | .mvar _ | .sort _ => pure ()
    | _ => terms := terms.push e
  if terms.size >= 48 then return terms
  match e with
  | .app f a =>
    terms := collectSubterms f terms
    terms := collectSubterms a terms
  | .lam _ type body _ | .forallE _ type body _ =>
    terms := collectSubterms type terms
    terms := collectSubterms body terms
  | .letE _ type value body _ =>
    terms := collectSubterms type terms
    terms := collectSubterms value terms
    terms := collectSubterms body terms
  | .mdata _ body | .proj _ _ body =>
    terms := collectSubterms body terms
  | _ => pure ()
  return terms

/-- Apply `ctor` to `fields` target-independent terms, retaining applications with the
expected result type. Constructor arity and result caps bound the Cartesian search. -/
private partial def buildConstructorApps (ctor ctorType expected : Expr)
    (fields : Nat) (pool : Array Expr) (limit : Nat := 16) : TacticM (Array Expr) := do
  if limit == 0 then return #[]
  if fields == 0 then
    return if ← isDefEqGuarded ctorType expected then #[ctor] else #[]
  let ctorType ← whnf ctorType
  let .forallE _ fieldType body _ := ctorType | return #[]
  let mut out := #[]
  let mut compatible := 0
  for candidate in pool do
    if out.size >= limit || compatible >= 12 then break
    try
      let candidateType ← inferType candidate
      if ← isDefEqGuarded candidateType fieldType then
        compatible := compatible + 1
        let apps ← buildConstructorApps (mkApp ctor candidate)
          (body.instantiate1 candidate) expected (fields - 1) pool (limit - out.size)
        for app in apps do
          unless out.contains app do out := out.push app
    catch _ => pure ()
  return out

private def termsOfType (pool : Array Expr) (type : Expr) (limit : Nat := 32) :
    TacticM (Array Expr) := do
  let mut out := #[]
  for candidate in pool do
    if out.size >= limit then break
    try
      if ← isDefEqGuarded (← inferType candidate) type then
        unless out.contains candidate do out := out.push candidate
    catch _ => pure ()
  return out

/-- Existing terms plus two constructor-closure rounds for an inductive witness type. -/
private def witnessCandidates (target witnessType : Expr) : TacticM (Array Expr) := do
  let witnessType ← whnf witnessType
  let mut pool := collectSubterms target
  trace[crush.reconstruct] "witness subterm pool: {pool.size} term(s)"
  let mut witnesses ← termsOfType pool witnessType
  let rawWitnessCount := witnesses.size
  let .const typeName levels := witnessType.getAppFn | return witnesses
  let some (.inductInfo inductInfo) := (← getEnv).find? typeName | return witnesses
  let typeArgs := witnessType.getAppArgs
  for _ in [0:2] do
    let roundPool := pool
    -- Constructors carrying target data are generally more informative witnesses than
    -- defaults (`succ t` before `zero`, `some x` before `none`, `cons` before `nil`).
    for withFields in [true, false] do
      for ctorName in inductInfo.ctors do
        if witnesses.size >= 32 then break
        let some (.ctorInfo ctorInfo) := (← getEnv).find? ctorName | continue
        if (ctorInfo.numFields > 0) != withFields then continue
        -- Larger constructors are still handled by datatype splitting. Witness synthesis
        -- limits field combinations because the target subterm pool is intentionally broad.
        if ctorInfo.numFields > 3 then continue
        let ctor := mkAppN (mkConst ctorName levels)
          typeArgs[*...min ctorInfo.numParams typeArgs.size]
        let apps ← buildConstructorApps ctor (← inferType ctor) witnessType
          ctorInfo.numFields roundPool (32 - witnesses.size)
        for app in apps do
          unless witnesses.contains app do witnesses := witnesses.push app
          unless pool.contains app do pool := pool.push app
  trace[crush.reconstruct] "witness candidates: {witnesses.size} term(s)"
  let generated := witnesses.extract rawWitnessCount witnesses.size
  return generated ++ witnesses.extract 0 rawWitnessCount

/-- Cheap finishers for speculative witness candidates. General `grind` is deliberately
excluded: most candidates are expected to fail, and saturating each failed body can dwarf
the bounded constructor search. Registered reconstruction rules are still available
through `finishOne`. -/
private def witnessFinisherTactics (useGlobalSimp := true) :
    CoreM (Array (TSyntax `tactic)) := do
  let simpTactic ←
    if useGlobalSimp then
      `(tactic| simp_all)
    else
      `(tactic| simp_all only)
  return #[
    (← `(tactic| assumption)),
    (← `(tactic| rfl)),
    (← `(tactic| (repeat' constructor) <;> rfl)),
    (← `(tactic| omega)),
    simpTactic,
    (← `(tactic| decide))]

/-- Try concrete constructor-generated witnesses for a top-level existential goal. -/
private def tryExistentialWitness (g : MVarId) (useGlobalSimp := true) :
    TacticM Bool := g.withContext do
  let target ← whnf (← g.getType)
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Exists && args.size == 2 do return false
  let witnessType := args[0]!
  let finishers ← witnessFinisherTactics useGlobalSimp
  trace[crush.reconstruct] "synthesizing witness of type {witnessType}"
  for witness in ← witnessCandidates target witnessType do
    let saved ← saveState
    try
      trace[crush.reconstruct] "trying witness {witness}"
      let proofGoal ← g.existsIntro witness
      -- A concrete constructor often exposes recursive `@[reducible]` wrappers that
      -- were stuck on the symbolic existential (`path h x [] y`, downstream tree
      -- predicates, and so on). Normalize definitionally before invoking the bounded
      -- closers; this is constructor-generic and emits no quantified SMT equations.
      let normalizedGoal ← unfoldReducibleTarget proofGoal
      trace[crush.reconstruct] "normalized witness target: {← normalizedGoal.getType}"
      if ← finishOne normalizedGoal finishers then return true
      trace[crush.reconstruct] "witness did not close the body"
      restoreState saved
    catch e =>
      trace[crush.reconstruct] "structured reconstruction declined: {e.toMessageData}"
      restoreState saved
  return false

/-- `t₁ → … → tₙ → concl`. The binders are non-dependent — each hypothesis is a
closed `Prop` — so a plain `mkForall` chain suffices. -/
def mkArrowChain (tys : Array Expr) (concl : Expr) : Expr := Id.run do
  let mut result := concl
  for ty in tys.reverse do
    result := mkForall `h .default ty result
  return result

/-- Try bounded constructor witnesses using only explicitly selected facts.

The original goal's context may contain propositions omitted by `crush [...]`. Build
and prove a closed implication exactly as core reconstruction does, then apply the
checked proof to the selected facts. This keeps witness synthesis cheap enough to run
before SMT under every trust policy without weakening strict hint selection. -/
private def trySelectedExistentialWitness (goal : MVarId) (proofs : Array Expr) :
    TacticM Bool := goal.withContext do
  let goalType ← instantiateMVars (← goal.getType)
  let targetHead ← whnf goalType
  unless targetHead.getAppFn.isConstOf ``Exists &&
      targetHead.getAppArgs.size == 2 do return false
  let hypTypes ← proofs.mapM fun proof => do instantiateMVars (← inferType proof)
  let target := mkArrowChain hypTypes goalType
  let used := Lean.collectFVars {} target
  let (_, _, params) ← Meta.removeUnused (← getLCtx).getFVars used
  let closedTarget ← mkForallFVars params target
  let saved ← saveState
  try
    let mv ← withLCtx {} {} do mkFreshExprMVar closedTarget
    let (_, g) ← mv.mvarId!.intros
    if ← tryExistentialWitness g (useGlobalSimpPrepass proofs) then
      let assigned ← instantiateMVars mv
      unless assigned.hasSorry || assigned.hasMVar do
        check assigned
        goal.assign (mkAppN (mkAppN assigned params) proofs)
        return true
    restoreState saved
    return false
  catch e =>
    trace[crush.reconstruct] "pre-SMT witness synthesis declined: {e.toMessageData}"
    restoreState saved
    return false

/-- Try one bounded datatype split using only explicitly selected facts.

Recursive definitions over a symbolic datatype are intentionally not emitted as unbounded
SMT axioms. A single Lean constructor split often exposes exactly the equations needed for
goals involving operations such as lookup, erase, or downstream reducible predicates. The
attempt is restricted to small logically structured targets, one split level, and a fixed
branch budget; failure restores all metavariable state before the query reaches SMT. -/
private def trySelectedConstructorSplit (goal : MVarId) (proofs : Array Expr) :
    TacticM Bool := goal.withContext do
  let goalType ← instantiateMVars (← goal.getType)
  let goalHead ← whnf goalType
  if goalHead.getAppFn.isConstOf ``Exists then return false
  unless ← exposesConstructorStructure goalType do return false
  unless ← supportsStructuralSplitting goalType do return false
  let hypTypes ← proofs.mapM fun proof => do instantiateMVars (← inferType proof)
  let target := mkArrowChain hypTypes goalType
  let used := Lean.collectFVars {} target
  let (_, _, params) ← Meta.removeUnused (← getLCtx).getFVars used
  let closedTarget ← mkForallFVars params target
  let saved ← saveState
  try
    let mv ← withLCtx {} {} do mkFreshExprMVar closedTarget
    let (_, g) ← mv.mvarId!.intros
    if (← splittableFVars g).isEmpty then
      restoreState saved
      return false
    let useGlobalSimp :=
      useGlobalSimpPrepass proofs && goalType.approxDepth.toNat ≤ 8
    let finishers ←
      if useGlobalSimp then
        preStructuralFinisherTactics
      else
        safePreStructuralFinisherTactics
    trace[crush.reconstruct] "pre-SMT constructor global simp: {useGlobalSimp}"
    let branchBudget ← IO.mkRef 24
    if ← splitSearch g finishers 1 branchBudget
        (finishCurrent := false) (ruleFuel := 0) then
      let assigned ← instantiateMVars mv
      unless assigned.hasSorry || assigned.hasMVar do
        check assigned
        goal.assign (mkAppN (mkAppN assigned params) proofs)
        return true
    restoreState saved
    return false
  catch e =>
    trace[crush.reconstruct] "pre-SMT constructor split declined: {e.toMessageData}"
    restoreState saved
    return false

/-- Apply selected theorem templates before invoking SMT.

`proofs` contains every selected fact available as a premise; `candidateIndices`
identifies the local hypotheses, explicit hints, or premise-selector results that may be
used as the top-level backward rule. The proof is built in the same isolated context as
ordinary core reconstruction, so an ambient proposition omitted from `crush [...]`
cannot discharge a generated premise.

The search is intentionally narrow: at most sixteen candidates, one top-level
application, configurable but bounded rule chaining for premises, and no `grind`,
datatype splitting, or existential witness search. Pre-SMT callers currently use
zero premise-rule fuel; recursive chaining is reserved for post-verdict reconstruction. -/
private def trySelectedFactRules (goal : MVarId) (proofs : Array Expr)
    (candidateIndices : Array Nat) (ruleFuel : Nat := 1) : TacticM Bool :=
    goal.withContext do
  if candidateIndices.isEmpty then return false
  let goalType ← goal.getType
  let hypTypes ← proofs.mapM fun proof => do instantiateMVars (← inferType proof)
  let target := mkArrowChain hypTypes goalType
  let used := Lean.collectFVars {} target
  let (_, _, params) ← Meta.removeUnused (← getLCtx).getFVars used
  let closedTarget ← mkForallFVars params target
  let saved ← saveState
  try
    let mv ← withLCtx {} {} do mkFreshExprMVar closedTarget
    let (introduced, g) ← mv.mvarId!.intros
    if introduced.size < proofs.size then
      restoreState saved
      return false
    let proofFVars := introduced.extract (introduced.size - proofs.size) introduced.size
    let finishers ← selectedRuleFinisherTactics
    for candidateIndex in candidateIndices.extract 0 (min candidateIndices.size 16) do
      let some candidateFVar := proofFVars[candidateIndex]? | continue
      let candidateSaved ← saveState
      try
        let subgoals ← g.apply (mkFVar candidateFVar)
        if subgoals.length > 16 then
          restoreState candidateSaved
          continue
        trace[crush.reconstruct] "pre-SMT selected rule {candidateIndex} generated \
          {subgoals.length} premise(s)"
        let mut closed := true
        for subgoal in subgoals do
          unless ← finishOne subgoal finishers ruleFuel do
            closed := false
            break
        if closed then
          let assigned ← instantiateMVars mv
          unless assigned.hasSorry || assigned.hasMVar do
            check assigned
            goal.assign (mkAppN (mkAppN assigned params) proofs)
            return true
        restoreState candidateSaved
      catch _ =>
        restoreState candidateSaved
    restoreState saved
    return false
  catch e =>
    trace[crush.reconstruct] "pre-SMT selected-rule reconstruction declined: {e.toMessageData}"
    restoreState saved
    return false

/-- Try to prove `goal` using **only** the hypotheses in `coreProofs`.

Rather than running the finisher on the ambient context, we prove the closed
implication `h₁ → … → hₙ → goal` and then apply it to the hypotheses' proof terms.
That guarantees the finisher cannot reach for context the solver did not need —
which is the whole point, since irrelevant hypotheses are what make these tactics
time out.

Returns `true` if the goal was closed; leaves `goal` untouched otherwise. -/
def tryReconstruct (goal : MVarId) (coreProofs : Array Expr)
    (finishers : Array (TSyntax `tactic)) : TacticM Bool :=
  goal.withContext do
    let goalType ← goal.getType
    let hypTypes ← coreProofs.mapM fun p => do instantiateMVars (← inferType p)
    let target := mkArrowChain hypTypes goalType
    -- Abstract exactly the local data/type variables that occur in the target
    -- (plus their dependencies). Proposition hypotheses not selected by the SMT
    -- core are absent from `target` and therefore cannot enter the finisher's
    -- context through metavariable creation.
    let used := Lean.collectFVars {} target
    let (_, _, params) ← Meta.removeUnused (← getLCtx).getFVars used
    let closedTarget ← mkForallFVars params target
    -- Try conclusion-indexed domain rules before the general tactic ladder. This path is
    -- especially important for nonlinear or datatype-specific bridges: `grind` may spend
    -- the whole command budget without discovering a theorem the user explicitly
    -- registered for this purpose.
    let saved ← saveState
    try
      let mv ← withLCtx {} {} do mkFreshExprMVar closedTarget
      let (_, initialGoal) ← mv.mvarId!.intros
      let g ← destructAndHypotheses initialGoal
      let g ← destructConstructorEqualities g
      let unpackedFacts := g != initialGoal
      let substGoals ← Tactic.run g (evalTactic (← `(tactic| subst_vars)))
      let mut closed := true
      for substGoal in substGoals do
        let subgoalClosed ←
          if ← finishWithLocalRules substGoal finishers 2 then
            pure true
          else if ← finishWithRegisteredRules substGoal finishers 2 then
            pure true
          else if unpackedFacts then
            finishOne substGoal finishers
          else
            pure false
        unless subgoalClosed do
          closed := false
          break
      if closed then
        let assigned ← instantiateMVars mv
        unless assigned.hasSorry || assigned.hasMVar do
          check assigned
          goal.assign (mkAppN (mkAppN assigned params) coreProofs)
          return true
      restoreState saved
    catch _ =>
      restoreState saved
    for tac in finishers do
      -- Each attempt gets a fresh metavariable and a saved state, so a failed
      -- finisher leaves nothing behind for the next one to trip over.
      let saved ← saveState
      try
        trace[crush.reconstruct] "trying finisher: {tac}"
        let mv ← withLCtx {} {} do mkFreshExprMVar closedTarget
        let gs ← Tactic.run mv.mvarId! (evalTactic tac)
        if gs.isEmpty then
          let assigned ← instantiateMVars mv
          unless assigned.hasSorry || assigned.hasMVar do
            check assigned
            goal.assign (mkAppN (mkAppN assigned params) coreProofs)
            return true
        restoreState saved
      catch _ =>
        restoreState saved
    -- Last resort: intro the core hypotheses, synthesize constructor-shaped existential
    -- witnesses, then search bounded datatype splits. Only reached after every fixed rung
    -- fails, so these more expensive generic searches strictly add reach.
    trace[crush.reconstruct] "trying structured reconstruction"
    let saved ← saveState
    try
      let mv ← withLCtx {} {} do mkFreshExprMVar closedTarget
      let (_, g) ← mv.mvarId!.intros
      let structuralFinishers ← structuralFinisherTactics
      let closed ←
        if ← tryExistentialWitness g then
          pure true
        else do
          -- Field-free finite datatypes admit deeper exhaustive search without becoming an
          -- induction procedure. The branch budget still bounds products of enum sizes.
          let enumCandidates ← splittableFVars g (onlyFiniteEnums := true)
          let enumFuel := min enumCandidates.size 6
          let enumBudget ← IO.mkRef 256
          if enumFuel > 0 &&
              (← splitSearch g structuralFinishers enumFuel enumBudget
                (finishCurrent := false) (onlyFiniteEnums := true)) then
            pure true
          else
            let target ← instantiateMVars (← g.getType)
            unless ← supportsStructuralSplitting target do
              trace[crush.reconstruct] "declined structural splitting for large target: {target}"
              return false
            let exposesStructure ← exposesConstructorStructure target
            let structuralBudget ← IO.mkRef 64
            splitSearch g structuralFinishers 2 structuralBudget (finishCurrent := false)
              (onlyTargetArgumentTypes := !exposesStructure)
      if closed then
        let assigned ← instantiateMVars mv
        trace[crush.reconstruct] "structured result: sorry={assigned.hasSorry}, \
          metavariables={assigned.hasMVar}"
        unless assigned.hasSorry || assigned.hasMVar do
          check assigned
          goal.assign (mkAppN (mkAppN assigned params) coreProofs)
          return true
      restoreState saved
    catch e =>
      trace[crush.reconstruct] "structured reconstruction declined: {e.toMessageData}"
      restoreState saved
    return false

/-- Try the checked Lean cases required before SMT for sound-but-incomplete encodings.

First eliminate locals of empty inductive types: SMT sorts are nonempty, so translating
such a context can produce a spurious `sat`. Explicitly selected theorem templates then get
a bounded backward-application attempt; quantified local invariants receive the same
non-recursive direct-reuse check first. Any top-level existential receives the cheap,
constructor-guided witness pass. Small logically structured targets get one bounded datatype
split, exposing concrete recursive equations without asserting them as universal SMT axioms.
Function-valued existential goals finally get the full bounded reconstruction attempt
because first-order defunctionalization does not imply that every pointwise choice has a
member in its encoded function sort. Other goals proceed directly to SMT, avoiding the full
reconstruction ladder on the normal path. -/
def tryPreReconstruct (goal : MVarId) (facts : Array Fact) : TacticM Bool :=
    goal.withContext do
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail then continue
    let type ← whnf localDecl.type
    let .const typeName _ := type.getAppFn | continue
    let some (.inductInfo inductInfo) := (← getEnv).find? typeName | continue
    unless inductInfo.ctors.isEmpty do continue
    let saved ← saveState
    try
      if (← goal.cases localDecl.fvarId).isEmpty then
        let proof ← instantiateMVars (mkMVar goal)
        unless proof.hasSorry || proof.hasMVar do
          check proof
          return true
      restoreState saved
    catch _ => restoreState saved
  let mut selectedProofs : Array Expr := #[]
  let mut localCandidateIndices : Array Nat := #[]
  let mut explicitCandidateIndices : Array Nat := #[]
  for fact in facts do
    let some proof := fact.proof | continue
    let index := selectedProofs.size
    selectedProofs := selectedProofs.push proof
    if proof.isFVar && fact.prop.isForall then
      localCandidateIndices := localCandidateIndices.push index
    if fact.instantiateTerms then
      explicitCandidateIndices := explicitCandidateIndices.push index
  trace[crush.reconstruct] "pre-SMT selected proofs: {selectedProofs.size}; \
    local rules: {localCandidateIndices.size}; explicit rules: {explicitCandidateIndices.size}; \
    global simp: {useGlobalSimpPrepass selectedProofs}"
  -- Reusing a quantified local invariant should not require a solver query. Keep this
  -- first pass non-recursive: each generated premise must already be an assumption or a
  -- cheap definitional/arithmetic consequence of the selected context.
  if ← trySelectedFactRules goal selectedProofs localCandidateIndices 0 then return true
  if ← trySelectedFactRules goal selectedProofs explicitCandidateIndices 0 then return true
  if ← trySelectedExistentialWitness goal selectedProofs then return true
  if ← trySelectedConstructorSplit goal selectedProofs then return true
  let target ← whnf (← goal.getType)
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Exists && args.size == 2 do return false
  unless (← whnf args[0]!).isForall do return false
  tryReconstruct goal selectedProofs #[]

end Crush
