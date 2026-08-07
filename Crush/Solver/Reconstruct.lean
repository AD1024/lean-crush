import Lean
import Crush.Frontend.Config
import Crush.Reify.Collect
import Crush.SMT.Result
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
  `f x = g x`, then a first-order closer finishes the body. Harmless on a non-function
  equality (`funext` fails cleanly), hence after the common case.
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
    (← `(tactic| (intros; funext _; simp_all))),
    (← `(tactic| (intros; funext _ _; simp_all))),
    (← `(tactic| (intros; ext; grind))),
    (← `(tactic| (intros; subst_vars; decide))),
    (← `(tactic| (intros; subst_vars; rfl))),
    (← `(tactic| (intros; simp_all; decide)))]

/-! ## The case-split pre-pass

Some verdicts turn on a *constructor case analysis*: datatype exhaustiveness
(`t = .leaf ∨ ∃ l v r, t = .node l v r`) and structure eta
(`p.x = q.x → p.y = q.y → p = q`). No rung reaches these, because the step they need is
`cases t` — naming a variable a *fixed* tactic string cannot know.

Hence a programmatic pass: split the goal's datatype variables, then run the ordinary ladder
per branch. It runs only after every rung has failed, so it can add closures but never take
one away. -/

/-- A local hypothesis worth case-splitting: a datatype with constructors, occurring in the
goal. Theory sorts are excluded — `Nat`'s constructors would trigger an induction-shaped
split `omega` handles better, and `Int`/`Bool`/`String` are the solver's theories. -/
private def firstSplittable (g : MVarId) : MetaM (Option FVarId) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless target.containsFVar d.fvarId do continue
    let ty ← whnf d.type
    let .const n _ := ty.getAppFn | continue
    if n == ``Nat || n == ``Int || n == ``Bool || n == ``String then continue
    let some (.inductInfo iv) := (← getEnv).find? n | continue
    if iv.ctors.isEmpty then continue
    if iv.numIndices != 0 then continue
    return some d.fvarId
  return none

/-- Case-split every goal's datatype variables, up to `fuel` rounds.

`fuel` is the termination argument: splitting a *recursive* datatype exposes fields of the
same type (`cases` on a `Tree` leaves `l r : Tree`), so an unbounded loop would descend
forever. Two rounds cover the target shapes — one for exhaustiveness, two for a structure
equality with a variable on each side. -/
private partial def splitRounds (gs : List MVarId) (fuel : Nat) : MetaM (List MVarId) := do
  if fuel == 0 then return gs
  -- Branch cap, so a context with many datatype variables cannot explode.
  if gs.length > 16 then return gs
  let mut out : List MVarId := []
  let mut progress := false
  for g in gs do
    match ← firstSplittable g with
    | none => out := out ++ [g]
    | some fv =>
      try
        let subs ← g.cases fv
        out := out ++ subs.toList.map (·.mvarId)
        progress := true
      catch _ => out := out ++ [g]
  if progress then splitRounds out (fuel - 1) else return out

/-- Close every goal in `gs` with the first finisher that works on it. All must close, else
the attempt is abandoned. -/
private def finishAll (gs : List MVarId) (finishers : Array (TSyntax `tactic)) :
    TacticM Bool := do
  for g in gs do
    if ← g.isAssigned then continue
    let mut closed := false
    for tac in finishers do
      let saved ← saveState
      try
        if (← Tactic.run g (evalTactic tac)).isEmpty then
          closed := true
          break
        restoreState saved
      catch _ => restoreState saved
    unless closed do return false
  return true

/-- `t₁ → … → tₙ → concl`. The binders are non-dependent — each hypothesis is a
closed `Prop` — so a plain `mkForall` chain suffices. -/
def mkArrowChain (tys : Array Expr) (concl : Expr) : Expr := Id.run do
  let mut result := concl
  for ty in tys.reverse do
    result := mkForall `h .default ty result
  return result

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
    for tac in finishers do
      -- Each attempt gets a fresh metavariable and a saved state, so a failed
      -- finisher leaves nothing behind for the next one to trip over.
      let saved ← saveState
      try
        let mv ← mkFreshExprMVar target
        let gs ← Tactic.run mv.mvarId! (evalTactic tac)
        if gs.isEmpty then
          let assigned ← instantiateMVars mv
          unless assigned.hasSorry || assigned.hasExprMVar do
            goal.assign (mkAppN assigned coreProofs)
            return true
        restoreState saved
      catch _ =>
        restoreState saved
    -- Last resort: intro the hypotheses, case-split the datatype variables, run the ladder
    -- per branch. Only reached once every rung has failed, so it strictly adds reach.
    let saved ← saveState
    try
      let mv ← mkFreshExprMVar target
      let (_, g) ← mv.mvarId!.intros
      let branches ← splitRounds [g] 2
      -- One branch means nothing was split, so the ladder has already seen this goal.
      if branches.length > 1 || (branches.length == 1 && branches[0]! != g) then
        if ← finishAll branches finishers then
          let assigned ← instantiateMVars mv
          unless assigned.hasSorry || assigned.hasExprMVar do
            check assigned
            goal.assign (mkAppN assigned coreProofs)
            return true
      restoreState saved
    catch _ =>
      restoreState saved
    return false

end Crush
