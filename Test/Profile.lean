import Crush.Util.Profile

/-!
Unit tests for the profiling infrastructure (`crush.profile` / `Crush.Profiler`).

These are solver-free and deterministic: they check the profiler's bookkeeping (that
`time` records phases when enabled and skips them when off, that `total` sums, and
that `report` renders), not wall-clock values, which are inherently machine-dependent.
The end-to-end profiling is exercised by any `set_option crush.profile true` run.
-/

open Crush

-- When enabled, `time` records one phase per call; the labels appear in the report.
/-- info: (2, true) -/
#guard_msgs in
#eval do
  let p := Profiler.on
  let (_, p) ← p.time "aphase" (pure (α := Nat) 1)
  let (_, p) ← p.time "bphase" (pure (α := Nat) 2)
  -- Two phases recorded; the report mentions both labels (values are machine-dependent
  -- wall-clock, so we do not assert on them).
  let mentionsBoth := (p.report.splitOn "aphase").length > 1 && (p.report.splitOn "bphase").length > 1
  return (p.phases.size, mentionsBoth)

-- When disabled, `time` records nothing and adds no overhead beyond running the action.
/-- info: 0 -/
#guard_msgs in
#eval do
  let p := Profiler.off
  let (r, p) ← p.time "x" (pure (α := Nat) 41)
  let (_, p) ← p.time "y" (pure (α := Nat) (r + 1))
  return p.phases.size

-- The action's result is threaded through unchanged, enabled or not.
/-- info: 42 -/
#guard_msgs in
#eval do
  let p := Profiler.on
  let (r, _) ← p.time "compute" (pure (α := Nat) 42)
  return r

-- `report` on an empty profiler is well-formed (the "total 0ms" header, no phases).
/-- info: "crush profile (total 0ms):" -/
#guard_msgs in
#eval (Profiler.on.report)

-- Machine records retain nanosecond phase data and stable outcome fields.
/-- info: (true, true) -/
#guard_msgs in
#eval do
  let (_, p) ← Profiler.on.time "phase" (pure ())
  let record := p.machineRecord "Profile.test" 17 "verified" "not-requested" "ok"
    #[("commands", 3)]
  return (record.startsWith "CRUSH_PROFILE\t2\tProfile.test\t17\tverified",
    record.contains "phase=" && record.endsWith "commands=3")
