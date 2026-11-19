import Lean

/-!
# Local budgets for optional preprocessing

Normalization and ground instantiation run `simp` as an optimization. A looping simp
set, a large term, or a heartbeat limit inside such a call must not abort `crush`:
the step is skipped and its input kept unchanged.
-/

open Lean Meta

namespace Crush

/-- Step limit for crush's own optional `simp` calls. -/
def localSimpMaxSteps : Nat := 1000

/-- Heartbeat budget for one optional step, capped at half of what remains. -/
def localHeartbeatBudget : Nat := 2000000

/-- Run an optional step under a local heartbeat budget. Any failure, including a
runtime limit such as heartbeats or recursion depth, restores the state and returns
`none`. Interrupts still propagate. -/
def withLocalBudget {α : Type} (action : MetaM α) : MetaM (Option α) := do
  let saved ← saveState
  tryCatchRuntimeEx (do
    let now ← IO.getNumHeartbeats
    let ctx ← readThe Core.Context
    let remaining := ctx.maxHeartbeats - (now - ctx.initHeartbeats)
    let budget := if ctx.maxHeartbeats == 0 then localHeartbeatBudget
      else min localHeartbeatBudget (remaining / 2)
    if budget == 0 then
      throwError "crush: an optional preprocessing step exhausted its local budget"
    withTheReader Core.Context
      ({ · with maxHeartbeats := budget, initHeartbeats := now }) do
        return some (← action)) fun _ => do
    saved.restore
    return none

end Crush
