import Lean

/-!
# Lightweight per-phase profiling

A tiny wall-clock profiler for the `crush` pipeline, enabled by `crush.profile`. It
records how long each phase (collect, normalize, monomorphize, instantiate,
translate, solve, reconstruct) takes and prints a breakdown, so optimization
targets the phase that actually dominates rather than a guess.

Design notes:

* **Wall-clock, not CPU.** `IO.monoMsNow` is a monotonic millisecond clock. The solver
  runs in a child process, so only wall time captures it; and the Lean-side phases are
  single-threaded, so wall ≈ CPU for them anyway.
* **Zero cost when off.** The tactic checks `cfg.profile` before timing, so a
  non-profiling run pays nothing beyond the branch. The profiler value is threaded
  explicitly rather than kept in a reader state to keep this independent of `TranslateM`.
* **Millisecond granularity** is enough: the phases we care about are tens to thousands
  of ms. Sub-ms phases show as `0ms`, which is the right message (not the bottleneck).
-/

namespace Crush

/-- A phase timing: its label and elapsed milliseconds. -/
structure PhaseTime where
  label : String
  ms    : Nat
  deriving Inhabited

/-- Accumulated phase timings, newest last. A plain structure threaded through the
tactic; `nil` when profiling is off so nothing is allocated on the hot path. -/
structure Profiler where
  /-- Whether timing is active. When `false`, `time` skips the clock reads. -/
  enabled : Bool := false
  phases  : Array PhaseTime := #[]
  deriving Inhabited

namespace Profiler

/-- A profiler that records nothing (profiling disabled). -/
def off : Profiler := { enabled := false }

/-- A fresh, active profiler. -/
def on : Profiler := { enabled := true }

/-- Run `act`, and if profiling is enabled, record its wall-clock duration under
`label`. Returns the action's result and the updated profiler. When disabled, this is
just `act` plus a struct copy — no clock reads. -/
def time {m : Type → Type} {α : Type} [MonadLiftT BaseIO m] [Monad m]
    (p : Profiler) (label : String) (act : m α) : m (α × Profiler) := do
  if !p.enabled then
    let a ← act
    return (a, p)
  let t0 ← (IO.monoMsNow : BaseIO Nat)
  let a ← act
  let t1 ← (IO.monoMsNow : BaseIO Nat)
  return (a, { p with phases := p.phases.push { label, ms := t1 - t0 } })

/-- Total recorded time across all phases. -/
def total (p : Profiler) : Nat := p.phases.foldl (fun acc ph => acc + ph.ms) 0

/-- A one-line-per-phase report with a total, e.g.
```
crush profile (total 812ms):
  collect        3ms
  monomorphize  41ms
  translate     18ms
  solve        740ms
  reconstruct   10ms
```
Each phase also shows its share of the total, so the dominant one is obvious. -/
def report (p : Profiler) : String := Id.run do
  let tot := p.total
  let mut lines : Array String := #[s!"crush profile (total {tot}ms):"]
  -- Pad labels to a common width for a readable column.
  let width := p.phases.foldl (fun w ph => max w ph.label.length) 0
  for ph in p.phases do
    let pad := String.ofList (List.replicate (width - ph.label.length) ' ')
    let pct := if tot == 0 then 0 else ph.ms * 100 / tot
    lines := lines.push s!"  {ph.label}{pad}  {ph.ms}ms ({pct}%)"
  return String.intercalate "\n" lines.toList

end Profiler

end Crush
