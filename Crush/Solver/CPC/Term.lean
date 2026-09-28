import Crush.Solver.Replay.Term

/-! Inverse handlers for CPC's internal terms. These definitions are used only to
state Lean propositions: each occurrence still needs a checked proof. -/

namespace Crush.CPC
open Lean Meta Crush

@[crush_replay "@purify"]
def replayPurification : ReplayTermHandler := fun ctx => do
  let #[value] := ctx.args | return none
  unless ctx.indices.isEmpty do return none
  return some value

@[crush_replay "div_total", crush_replay "mod_total"]
def replayTotalIntDivision : ReplayTermHandler := fun ctx => do
  let #[left, right] := ctx.args | return none
  unless ctx.indices.isEmpty && (← inferType left).isConstOf ``Int do return none
  -- Only nonzero concrete divisors avoid depending on the internal zero convention.
  let some divisor ← getIntValue? right | return none
  if divisor == 0 then return none
  let operation := if ctx.head == "div_total" then ``HDiv.hDiv else ``HMod.hMod
  return some (← mkAppM operation #[left, right])

@[crush_replay "@quantifiers_skolemize"]
def replayQuantifierSkolem : ReplayTermHandler := fun ctx => do
  let #[quantifier, index] := ctx.args | return none
  unless ctx.indices.isEmpty && (← getIntValue? index) == some 0 do return none
  let .forallE name type body info := quantifier | return none
  unless ← isProp quantifier do return none
  let predicate := Expr.lam name type (mkApp (mkConst ``Not) body) info
  try
    return some (← mkAppM ``Classical.epsilon #[predicate])
  catch _ => return none

end Crush.CPC
