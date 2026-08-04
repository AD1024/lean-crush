import Lean
import Crush.Translation.Monad
import Crush.Translation.Unfold
open Lean Meta

/-!
# Collecting facts from the goal

Gathers the propositions to send to the solver: local hypotheses (those of type
`Prop`), explicit user-provided term hints, equation lemmas from unfold/defeq hints,
and the goal itself. The goal is *negated* — `crush` proves `G` by asserting the
hypotheses together with `¬G` and checking for `unsat`, the standard refutation
setup.

The set of facts is governed by `Hints` (parsed from the tactic's argument grammar,
see `Crush/Frontend/Tactic.lean`):

* bare `crush` collects **all** local `Prop` hypotheses (the common case);
* `crush [t₁, …]` collects only the listed terms (plus the goal), matching
  Sledgehammer/`auto` semantics where an explicit list is a *restriction*;
* `crush [t₁, …, *]` collects the listed terms **and** all local hypotheses;
* `crush u[f]` adds `f`'s equation lemmas (definitional unfolding);
* `crush d[f]` adds `f`'s unfold equation (`f x = …`) as a definitional equality.

Each collected fact carries a `descr` for provenance, so an unsat core or a failure
message can name its source. Premise selection (Lean core `LibrarySuggestions`) is
the remaining unwired source.
-/

namespace Crush

/-- A proposition to assert, with its provenance. `negated` marks the (single)
negated goal so diagnostics can distinguish it. -/
structure Fact where
  /-- The proposition (a `Prop`-typed `Expr`). -/
  prop    : Expr
  /-- The proof of `prop`, when it is a hypothesis (none for the negated goal). -/
  proof   : Option Expr
  descr   : String
  negated : Bool := false
  deriving Inhabited

/-- The resolved fact sources requested by the tactic's argument grammar. Produced
by the tactic front-end; `collectFacts` turns it into the actual `Fact` array.

`terms` are proof terms the user named explicitly (lemmas or hypotheses); `eqnLemma`
names are equation lemmas already resolved from `u[…]`/`d[…]` hints. `allHyps`
requests every local `Prop` hypothesis — the default when no `[…]` list is given, or
when the list contains `*`. -/
structure Hints where
  /-- Explicit proof terms (already elaborated) with a description each. -/
  terms    : Array (Expr × String) := #[]
  /-- Equation-lemma constant names gathered from `u[…]`/`d[…]`. -/
  eqnLemmas : Array Name := #[]
  /-- Whether to sweep in every local `Prop` hypothesis. -/
  allHyps  : Bool := true
  deriving Inhabited

/-- Collect assertable facts from `goal` under `hints`, plus the (negated) goal.
Returns the facts and leaves the goal untouched (the tactic decides how to close
it). Only `Prop` propositions are collected; the goal's type is negated. -/
def collectFacts (goal : MVarId) (hints : Hints := {}) (autoUnfold : Bool := true) :
    MetaM (Array Fact) :=
  goal.withContext do
    let mut facts := #[]
    -- Constants seen across goal + hypotheses + hints, seeding auto-unfold relevance.
    -- The goal/hyp types are instantiated first: after a tactic like `induction` the
    -- goal type carries unassigned metavariables that `getUsedConstants` does not
    -- traverse, so without this a constant like the recursive function under proof is
    -- invisible to relevance and its `@[crush_unfold]` equations never get folded in.
    let mut seeds : Array Name := #[]
    let goalType ← instantiateMVars (← goal.getType)
    seeds := seeds ++ goalType.getUsedConstants
    -- Local hypotheses, unless an explicit `[…]` list without `*` restricts us.
    if hints.allHyps then
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let ty ← instantiateMVars decl.type
        if (← isProp ty) then
          seeds := seeds ++ ty.getUsedConstants
          facts := facts.push {
            prop := ty
            proof := decl.toExpr
            descr := s!"hyp {decl.userName}" }
    -- Explicit term hints (lemmas or hypotheses the user named).
    for (proof, descr) in hints.terms do
      let ty ← inferType proof
      if (← isProp ty) then
        seeds := seeds ++ ty.getUsedConstants
        facts := facts.push { prop := ty, proof := proof, descr }
      else
        throwError "crush: {descr} has type `{ty}`, which is not a `Prop`; \
                    only propositions can be asserted as facts."
    -- Equation lemmas from `u[…]`/`d[…]` hints. Fresh level metavariables so a
    -- universe-polymorphic equation lemma instantiates at use.
    let mut eqnLemmas := hints.eqnLemmas
    -- Auto-unfold: equation lemmas of `@[crush_unfold]`/`@[crush_defeq]` definitions
    -- reachable from the collected constants. Relevance-filtered so an unrelated marked
    -- definition contributes nothing (see `relevantAutoUnfoldLemmas`). Explicit hints
    -- still win — a name already requested by `u[…]`/`d[…]` is de-duplicated below.
    if autoUnfold then
      eqnLemmas := eqnLemmas ++ (← relevantAutoUnfoldLemmas seeds)
    let mut seenEqn : Std.HashSet Name := {}
    for lemName in eqnLemmas do
      if seenEqn.contains lemName then continue
      seenEqn := seenEqn.insert lemName
      let proof ← mkConstWithFreshMVarLevels lemName
      let ty ← inferType proof
      if (← isProp ty) then
        facts := facts.push { prop := ty, proof := proof, descr := s!"eqn {lemName}" }
    -- The negated goal.
    facts := facts.push {
      prop := mkNot goalType
      proof := none
      descr := "negated goal"
      negated := true }
    return facts

end Crush
