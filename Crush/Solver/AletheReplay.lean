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

## Subproof blocks

`(anchor :step t) (assume t.a0 φ) … (step t … :rule subproof :discharge (t.a0))` proves the
block's conclusion under a *local* assumption `φ` and then discharges it. Replay binds `φ`
as a real Lean hypothesis (`withLocalDeclD`), replays the inner steps under it, abstracts it
back out with `mkLambdaFVars`, and proves the closing clause from that implication — so the
discharge itself is kernel-checked rather than assumed.

## Known limits

* Rules whose justification is in their `:args` rather than their premises —
  `forall_inst` (the quantifier-instantiation witness), `bind`, `sko_ex`, `sko_forall` — are
  **declined**, since a tactic handed such a step has no honest way to close it. Consuming
  the witness to instantiate directly is the next extension; until then a proof needing one
  falls back to the finisher ladder (which handles the common instantiation shapes anyway).
* A `hole` step is cvc5 admitting an untranslated rewrite — declined.
* Terms crush cannot map back (`ite`, anything not in `AletheTerm`'s table) decline.
* Nested anchors are declined.
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
  -- Rules whose conclusion does **not** follow from their premises alone: the
  -- justification lives in the rule's `:args` (the instantiation witness for
  -- `forall_inst`), which we do not yet consume. A tactic handed such a step has no
  -- honest way to close it, and empirically one "succeeds" with a term the *kernel* later
  -- rejects — a failure that surfaces after replay reports success, with no fallback. So
  -- decline them up front and let the finisher ladder handle the goal.
  if rule == "forall_inst" || rule == "bind" || rule == "sko_ex" || rule == "sko_forall" then
    return none
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
          -- Type-check the step's term *here*, before it is built into the final proof.
          -- A tactic can produce a term the elaborator accepts but the kernel rejects —
          -- `decide` on `Int` literals emits an `eagerReduce` the kernel will not replay —
          -- and without this check that term poisons the assembled proof, surfacing as an
          -- opaque "(kernel) application type mismatch" at the *end*. Checking per step
          -- turns it into a clean decline that the next tactic (or the ladder) handles.
          check assigned
          return some (mkAppN assigned premises)
      restoreState saved
    catch _ =>
      restoreState saved
  return none

/-- Replay a parsed Alethe proof into a Lean proof of `False`.

`facts` maps a `crush_fact_<n>` assumption id to the Lean proof of that hypothesis (from
`TranslateState.facts`); `symbols` is the emitted-symbol → Lean-term map. Returns `none`
the moment any step cannot be replayed. -/
partial def replay? (proof : AletheProof) (rawSexps : Array Sexp)
    (facts : Std.HashMap String Expr) (symbols : Std.HashMap String Expr) :
    TacticM (Option Expr) := do
  -- `:named` bindings must be collected from the *unstripped* text: the parser drops the
  -- annotations, which is exactly the information `@p_k` references need.
  let named := rawSexps.foldl (fun acc s => collectNamed s acc) {}
  let ctx : TermCtx := { symbols, named }
  go ctx facts proof.commands 0 {}
where
  /-- Replay `cmds` from index `i` under proof environment `env`, returning the proof of
  the first empty clause reached (or `none`). Written as an explicit index walk so a
  subproof block can hand back the index just past its closing step. -/
  go (ctx : TermCtx) (facts : Std.HashMap String Expr) (cmds : Array Command)
      (i : Nat) (env : Std.HashMap String Expr) : TacticM (Option Expr) := do
    let fuel := 64
    let mut i := i
    let mut env := env
    while h : i < cmds.size do
      match cmds[i] with
      | .assume id _ =>
        -- An assumption at top level is one of our asserted facts, so its Lean proof is
        -- already in hand. (A *local* assumption inside a block is bound by `anchor`
        -- below, never reached here.)
        let some p := facts.get? id
          | trace[crush.result] "alethe replay: declined (unknown assumption {id})"
            return none
        env := env.insert id p
        i := i + 1
      | .anchor stepId _ =>
        -- A subproof block: `(anchor :step t) (assume t.a0 φ) … (step t … :rule subproof
        -- :discharge (t.a0))`. Bind `φ` as a real local hypothesis, replay the block
        -- under it, then abstract it back out so the conclusion is an implication.
        let some (.assume localId localTerm) := cmds[i + 1]?
          | trace[crush.result] "alethe replay: declined (anchor {stepId} without assume)"
            return none
        let some hypTy ← toExpr? ctx fuel localTerm
          | trace[crush.result] "alethe replay: declined (untranslatable local assume \
                                 {localId})"
            return none
        let hypTy ← toPropM hypTy
        -- Find the closing `subproof` step for this anchor.
        let some close := findClose cmds (i + 2) stepId
          | trace[crush.result] "alethe replay: declined (anchor {stepId} unclosed)"
            return none
        let .step _ closeClause _ _ _ _ := cmds[close]!
          | return none
        let some concl ← clauseToExpr? ctx fuel closeClause
          | trace[crush.result] "alethe replay: declined (untranslatable subproof \
                                 conclusion {stepId})"
            return none
        -- Under `h : φ`, replay the inner steps to the block's conclusion, then
        -- `fun h => …`. Discharging is what turns "concl under φ" into `φ → concl`; the
        -- closing clause already states the discharged form (`¬φ ∨ …`), so the two are
        -- reconciled by one final step proof.
        let inner ← (do
          withLocalDeclD (`hsub ++ localId.toName) hypTy fun h => do
            let innerEnv := env.insert localId h
            let some body ← goInner ctx facts cmds (i + 2) close innerEnv
              | pure none
            let lam ← mkLambdaFVars #[h] body
            pure (some lam) : TacticM (Option Expr))
        let some lam := inner
          | trace[crush.result] "alethe replay: declined (subproof {stepId} body)"
            return none
        -- `lam : φ → innerConcl`. The closing clause is the discharged statement; prove it
        -- from `lam` with the step tactics, so the kernel checks the discharge.
        let some pf ← (proveStep concl #[lam] "subproof" : TacticM (Option Expr))
          | trace[crush.result] "alethe replay: declined (subproof {stepId} discharge)"
            return none
        env := env.insert stepId pf
        if closeClause.isEmpty then
          trace[crush.result] "alethe replay: succeeded at {stepId}"
          return some pf
        i := close + 1
      | .step id clause rule premises _ _ =>
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
        let some pf ← (proveStep target prems rule : TacticM (Option Expr))
          | trace[crush.result] "alethe replay: declined (rule `{rule}` at {id} not \
                                 replayed)"
            return none
        env := env.insert id pf
        -- The empty clause is `False`: the refutation is complete.
        if clause.isEmpty then
          trace[crush.result] "alethe replay: succeeded at {id}"
          return some pf
        i := i + 1
    trace[crush.result] "alethe replay: declined (no empty-clause step)"
    return none

  /-- Replay the steps of a subproof block, `[from, upto)`, returning the proof of the
  step just before `upto` (the block's last inner conclusion). -/
  goInner (ctx : TermCtx) (facts : Std.HashMap String Expr) (cmds : Array Command)
      («from» upto : Nat) (env : Std.HashMap String Expr) : TacticM (Option Expr) := do
    let fuel := 64
    let mut i := «from»
    let mut env := env
    let mut last : Option Expr := none
    while i < upto do
      match cmds[i]! with
      | .step id clause rule premises _ _ =>
        if rule == "hole" then return none
        let some target ← clauseToExpr? ctx fuel clause | return none
        let mut prems := #[]
        for p in premises do
          let some pf := env.get? p | return none
          prems := prems.push pf
        let some pf ← (proveStep target prems rule : TacticM (Option Expr)) | return none
        env := env.insert id pf
        last := some pf
      -- Nested anchors and stray assumes inside a block are not handled.
      | _ => return none
      i := i + 1
    return last

  /-- Index of the `step` whose id is `stepId` (the `subproof` closing an anchor), at or
  after `from`. -/
  findClose (cmds : Array Command) («from» : Nat) (stepId : String) : Option Nat := Id.run do
    let mut i := «from»
    while i < cmds.size do
      if let .step id _ _ _ _ _ := cmds[i]! then
        if id == stepId then return some i
      i := i + 1
    return none

  /-- `AletheTerm.toProp` is private; this mirrors it for the local-assumption type. -/
  toPropM (e : Expr) : TacticM Expr := do
    let ty ← whnf (← inferType e)
    if ty.isProp then return e
    else if ty.isConstOf ``Bool then mkEq e (mkConst ``Bool.true)
    else return e

end Crush.Alethe
