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

The alternative — parsing the solver's own proof object (Alethe for cvc5, the
`(proof …)` term z3 emits) and replaying it inference by inference — gives a
stronger guarantee, since it does not depend on a Lean tactic being able to
re-find the argument. It is also far more work and is solver-specific. This is the
cheaper 80% and is a strict improvement on trusting.
-/

namespace Crush

/-- The hypotheses named by an unsat core, deduplicated and in context order.

Fact ids index `TranslateState.facts`; entries with no `proof` (the negated goal)
are skipped, since the goal is not a hypothesis to feed the finisher. Ids that fall
outside the table are ignored rather than fatal: a solver is free to name anything
in its core, and a malformed name should not crash the tactic. -/
def coreHypotheses (st : TranslateState) (coreIds : Array Nat) : Array Expr := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Expr := #[]
  for id in coreIds do
    if seen.contains id then continue
    seen := seen.insert id
    if let some src := st.facts[id]? then
      if let some proof := src.proof then
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

`intros` first introduces the hypotheses of the implication we build, then:
* `grind` — Lean's general-purpose closer: congruence, case-splitting, arithmetic;
* `omega` — complete for linear integer/natural arithmetic, so it lands the shape
  the solver most often reports `unsat` for and `grind` may not finish;
* `simp_all` — cheap normalization that closes propositional and rewriting goals;
* `funext`-prefixed variants — for a **higher-order** verdict whose goal is a
  *function equality* `f = g`, which the first-order finishers cannot touch. `funext`
  reduces it to the pointwise `f x = g x`, then `simp_all`/`grind` close the body — so
  a higher-order `unsat` (a Church-numeral identity, funext) becomes a kernel-checked
  proof rather than a trusted verdict. `funext` fails cleanly on a non-function
  equality, so these cost nothing on the common case, hence last.

Kept as syntax rather than names so each is elaborated once, here, where a typo is
a build error instead of a runtime "unknown tactic". -/
def finisherTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| (intros; grind))),
    (← `(tactic| (intros; omega))),
    (← `(tactic| (intros; simp_all))),
    (← `(tactic| (intros; funext _; simp_all))),
    (← `(tactic| (intros; funext _ _; simp_all))),
    (← `(tactic| (intros; ext; grind)))]

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
    return false

end Crush
