import Crush.Solver.Alethe
import Crush.Solver.AletheTerm
import Crush.Translation.Monad
open Lean Meta Elab Tactic

/-!
# Replaying an Alethe proof as a Lean proof

The core-directed finisher (`Crush/Solver/Reconstruct.lean`) hands the *whole* goal to one
Lean tactic. That works surprisingly often, but it fails when the argument needs a long
chain of small inferences the tactic cannot re-find in one shot — a Boolean pigeonhole, an
EUF conflict several congruences deep.

An Alethe proof is exactly that chain, already found: cvc5 reports ~20–60 steps, each a
*trivial* clause following from one or two earlier ones. So instead of re-searching, we
replay: for each step, restate its clause as a Lean proposition, prove it from the
premises' proofs, and carry the result forward. The final step's clause is the empty
clause (`False`), which contradicts the negated goal.

## Why this is sound regardless of rule coverage

Each step is discharged by a Lean tactic and the result is a **real proof term the kernel
checks**. The Alethe rule name is used only as a *hint* for which tactic to try first — a
wrong guess makes the step fail, never succeed wrongly. Concretely, the trusted base is
unchanged: the kernel plus the tactics we invoke. If any step cannot be replayed (rule we
do not handle, term we cannot map back, tactic that fails), `replay?` returns `none` and
the caller falls back to the finisher ladder. There is no path in which an unreplayed step
closes a goal.

This is the phase-3 "real reconstruction" of `Doc/PLAN.md` §9 M4, but done per *step*
rather than per *rule*: we do not prove each Alethe rule sound once and for all (that is
lean-auto's reflective-checker approach, ~12k lines); we let the kernel check each of the
proof's concrete instances. That trades a soundness meta-theorem for per-call work, and
needs no verified checker.

## Known limits

* Steps under an `anchor`/`subproof` block (used for quantifier instantiation) are not
  replayed; a proof containing one is declined. Those need local-assumption scoping.
* A `hole` step is cvc5 admitting an untranslated rewrite — declined.
* Terms crush cannot map back (`ite`, anything not in `AletheTerm`'s table) decline.
-/

namespace Crush.Alethe

open Crush.SMT

/-- Tactics tried on a step, in order. The rule name selects which to try *first*; all are
tried, so an unrecognized rule still gets a chance.

These are deliberately cheap and local: a step is a trivial consequence of its premises
(that is what makes an Alethe proof long), so anything needing real search means we mapped
the step wrong and should decline rather than grind. -/
private def stepTactics : CoreM (Array (TSyntax `tactic)) := do
  return #[
    (← `(tactic| simp_all)),
    (← `(tactic| grind)),
    (← `(tactic| omega)),
    (← `(tactic| rfl)),
    (← `(tactic| decide))]

/-- Tactic tried first for a given Alethe rule, when we have a good guess. Purely a
performance hint — see the module comment on soundness. -/
private def ruleHint? (rule : String) : CoreM (Option (TSyntax `tactic)) := do
  match rule with
  | "refl" | "evaluate" | "false" => return some (← `(tactic| decide))
  | "cong" | "trans" => return some (← `(tactic| simp_all))
  | "resolution" | "not_or" | "or" | "and" | "equiv_pos2" | "contraction"
  | "reordering" | "implies" => return some (← `(tactic| grind))
  | _ => return none

/-- Prove `target` from the proofs in `premises`, trying the rule's hinted tactic first.

Builds the closed implication `p₁ → … → pₙ → target`, proves *that*, then applies it to the
premise proofs — the same technique as `tryReconstruct`, so the tactic cannot reach for
ambient context that the step does not license. -/
private def proveStep (target : Expr) (premises : Array Expr) (rule : String) :
    TacticM (Option Expr) := do
  let hypTypes ← premises.mapM fun p => do instantiateMVars (← inferType p)
  let impl := hypTypes.foldr (fun ty acc => mkForall `h .default ty acc) target
  let hint ← ruleHint? rule
  let tactics := (match hint with | some t => #[t] | none => #[]) ++ (← stepTactics)
  for tac in tactics do
    let saved ← saveState
    try
      let mv ← mkFreshExprMVar impl
      let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| (intros; $tac))))
      if gs.isEmpty then
        let assigned ← instantiateMVars mv
        unless assigned.hasSorry || assigned.hasExprMVar do
          return some (mkAppN assigned premises)
      restoreState saved
    catch _ =>
      restoreState saved
  return none

/-- Replay a parsed Alethe proof into a Lean proof of `False`.

`facts` maps a `crush_fact_<n>` assumption id to the Lean proof of that hypothesis (from
`TranslateState.facts`); `symbols` is the emitted-symbol → Lean-term map. Returns `none`
the moment any step cannot be replayed. -/
def replay? (proof : AletheProof) (rawSexps : Array Sexp)
    (facts : Std.HashMap String Expr) (symbols : Std.HashMap String Expr) :
    TacticM (Option Expr) := do
  -- `:named` bindings must be collected from the *unstripped* text: the parser drops the
  -- annotations, which is exactly the information `@p_k` references need.
  let named := rawSexps.foldl (fun acc s => collectNamed s acc) {}
  let ctx : TermCtx := { symbols, named }
  let fuel := 64
  -- A subproof block needs local-assumption scoping we do not implement; decline early
  -- rather than replay its steps out of context.
  if proof.commands.any (fun | .anchor .. => true | _ => false) then
    trace[crush.result] "alethe replay: declined (proof contains a subproof/anchor)"
    return none
  let mut env : Std.HashMap String Expr := {}
  for cmd in proof.commands do
    match cmd with
    | .assume id _ =>
      -- An assumption is one of our asserted facts; its Lean proof is already in hand.
      let some p := facts.get? id
        | trace[crush.result] "alethe replay: declined (unknown assumption {id})"
          return none
      env := env.insert id p
    | .anchor .. => return none
    | .step id clause rule premises _ =>
      if rule == "hole" then
        trace[crush.result] "alethe replay: declined (hole step {id})"
        return none
      let some target ← clauseToExpr? ctx fuel clause
        | trace[crush.result] "alethe replay: declined (untranslatable clause at {id})"
          return none
      let mut prems := #[]
      for p in premises do
        let some pf := env.get? p
          | trace[crush.result] "alethe replay: declined (missing premise {p} of {id})"
            return none
        prems := prems.push pf
      let some pf ← proveStep target prems rule
        | trace[crush.result] "alethe replay: declined (rule `{rule}` at {id} not replayed)"
          return none
      env := env.insert id pf
      -- The empty clause is `False`: the refutation is complete.
      if clause.isEmpty then
        trace[crush.result] "alethe replay: succeeded at {id}"
        return some pf
  trace[crush.result] "alethe replay: declined (no empty-clause step)"
  return none

end Crush.Alethe
