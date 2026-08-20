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
  nanos : Nat
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
  let t0 ← (IO.monoNanosNow : BaseIO Nat)
  let a ← act
  let t1 ← (IO.monoNanosNow : BaseIO Nat)
  let nanos := t1 - t0
  return (a, {
    p with phases := p.phases.push { label, ms := nanos / 1_000_000, nanos } })

/-- Total recorded time across all phases. -/
def total (p : Profiler) : Nat := p.phases.foldl (fun acc ph => acc + ph.ms) 0

/-- Total recorded time across all phases at the profiler's native resolution. -/
def totalNanos (p : Profiler) : Nat :=
  p.phases.foldl (fun acc ph => acc + ph.nanos) 0

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

/-- An optional mutable profiler used by long pipelines.

The disabled session is `none`, so timing a phase retains the profiler's
single-branch disabled cost without allocating or touching an `IO.Ref`. -/
abbrev Session := Option (IO.Ref Profiler)

namespace Session

def start (enabled : Bool) : IO Session :=
  if enabled then return some (← IO.mkRef Profiler.on) else return none

def time {m : Type → Type} {α : Type}
    [MonadLiftT BaseIO m] [MonadLiftT (ST IO.RealWorld) m] [Monad m]
    (session : Session) (label : String) (act : m α) : m α := do
  let some ref := session | return ← act
  let profiler ← ref.get
  let (result, profiler) ← profiler.time label act
  ref.set profiler
  return result

def get (session : Session) : IO Profiler := do
  let some ref := session | return Profiler.off
  ref.get

end Session

private def sanitizeField (value : String) : String :=
  value.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " "

/-- Emit one stable TSV record for benchmark tooling.

The final two fields contain comma-separated `phase=nanos` and
`metric=value` entries. Their names are controlled by Crush. -/
def machineRecord (p : Profiler) (decl : String) (goalHash : UInt64)
    (outcome replay detail : String)
    (metrics : Array (String × Nat) := #[]) : String :=
  let phases := p.phases.toList.map fun phase => s!"{phase.label}={phase.nanos}"
  let metrics := metrics.toList.map fun (name, value) => s!"{name}={value}"
  s!"CRUSH_PROFILE\t2\t{sanitizeField decl}\t{goalHash}\t\
{sanitizeField outcome}\t{sanitizeField replay}\t{sanitizeField detail}\t\
{p.totalNanos}\t{String.intercalate "," phases}\t{String.intercalate "," metrics}"

end Profiler

end Crush
