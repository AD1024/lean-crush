import Lean
import Crush.Translation.Monad
open Lean Meta

/-!
# Collecting facts from the goal

Gathers the propositions to send to the solver: the local hypotheses (those of
type `Prop`) plus explicit user-provided term hints, and the goal itself. The
goal is *negated* — `crush` proves `G` by asserting the hypotheses together with
`¬G` and checking for `unsat`, the standard refutation setup.

Currently collects local `Prop` hypotheses and the goal. Explicit hint terms,
lemma databases, unfold/defeq hints, and premise selection are not yet wired in.
Each collected fact carries a `descr` for provenance, so an unsat core or a
failure message can name its source.
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

/-- Collect assertable facts from `goal`'s local context and the (negated) goal.
Returns the facts and leaves the goal untouched (the tactic decides how to close
it). Only `Prop` hypotheses are collected; the goal's type is negated. -/
def collectFacts (goal : MVarId) : MetaM (Array Fact) := goal.withContext do
  let mut facts := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty := decl.type
    if (← isProp ty) then
      facts := facts.push {
        prop := ty
        proof := decl.toExpr
        descr := s!"hyp {decl.userName}" }
  -- The negated goal.
  let goalType ← goal.getType
  facts := facts.push {
    prop := mkNot goalType
    proof := none
    descr := "negated goal"
    negated := true }
  return facts

end Crush
