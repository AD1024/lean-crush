import Crush

/-!
# What each query asks the solver for (review round 3, P1)

A query requests an unsat core only when a reconstructing policy or the
`trace.crush.result` line reads it, and a proof only for cvc5 Alethe replay. The
prologue and the solver's argv follow the request, so a saved script reproduces the
query that was run.
-/

open Lean Crush Crush.Solver

namespace SolverRequests

private def request (backend : Backend) (policy : TrustMode)
    (reconstruct : ReconstructMode := .auto) (trace := false) : SolverRequest :=
  SolverRequest.ofConfig { backend, trust := policy, reconstruct } trace

private def expect (label : String) (actual expected : SolverRequest) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: got {repr actual}, expected {repr expected}"

#eval show IO Unit from do
  let none : SolverRequest := {}
  let cores : SolverRequest := { cores := true }
  let both : SolverRequest := { cores := true, proofs := true }
  -- Trust: the verdict only, unless the result trace reads the core.
  for backend in [Backend.z3, .cvc5, .bitwuzla] do
    for mode in [ReconstructMode.auto, .alethe, .core] do
      expect s!"{backend} trust {repr mode}" (request backend .trust mode) none
  expect "z3 trust traced" (request .z3 .trust (trace := true)) cores
  expect "cvc5 trust traced" (request .cvc5 .trust (trace := true)) cores
  expect "bitwuzla trust traced" (request .bitwuzla .trust (trace := true)) none
  -- Reconstructing policies always need a core; only cvc5 replays a proof.
  for policy in [TrustMode.reconstruct, .reconstructOrTrust] do
    for mode in [ReconstructMode.auto, .alethe, .core] do
      expect s!"z3 {repr policy} {repr mode}" (request .z3 policy mode) cores
      expect s!"bitwuzla {repr policy} {repr mode}" (request .bitwuzla policy mode) none
    expect s!"cvc5 {repr policy} auto" (request .cvc5 policy .auto) both
    expect s!"cvc5 {repr policy} alethe" (request .cvc5 policy .alethe) both
    expect s!"cvc5 {repr policy} core" (request .cvc5 policy .core) cores
  expect "no backend" (request .none .reconstruct) none

-- The prologue and follow-up commands follow the request.
#eval show IO Unit from do
  let render (cmds : Array SMT.Command) := SMT.scriptToString cmds
  unless (prologue {}).isEmpty && (unsatFollowUp {}).isEmpty do
    throw <| IO.userError "a verdict-only request sent options or follow-ups"
  unless render (prologue { cores := true }) == "(set-option :produce-unsat-cores true)" do
    throw <| IO.userError s!"cores prologue: {render (prologue { cores := true })}"
  unless render (prologue { cores := true, proofs := true }) ==
      "(set-option :produce-unsat-cores true)\n(set-option :produce-proofs true)" do
    throw <| IO.userError "cores and proofs prologue drifted"
  unless render (unsatFollowUp { cores := true, proofs := true }) ==
      "(get-unsat-core)\n(get-proof)" do
    throw <| IO.userError "unsat follow-up drifted"

-- The argv follows the request; cvc5 no longer runs in incremental mode.
#eval show IO Unit from do
  let args (backend : Backend) (req : SolverRequest) (ms := 5000) :=
    (backendArgs { backend } ms req).getD #[]
  unless args .z3 {} == #["-in", "-smt2", "-T:5"] do
    throw <| IO.userError s!"z3 argv: {args .z3 {}}"
  unless args .z3 { cores := true } (ms := 1500) == #["-in", "-smt2", "-T:2"] do
    throw <| IO.userError "z3 argv does not round the limit up to whole seconds"
  unless args .cvc5 {} == #["--tlimit=5000", "--produce-models", "--enum-inst"] do
    throw <| IO.userError s!"cvc5 verdict-only argv: {args .cvc5 {}}"
  unless args .cvc5 { cores := true } ==
      #["--tlimit=5000", "--produce-models", "--enum-inst", "--produce-unsat-cores"] do
    throw <| IO.userError s!"cvc5 core argv: {args .cvc5 { cores := true }}"
  unless args .cvc5 { cores := true, proofs := true } ==
      #["--tlimit=5000", "--produce-models", "--enum-inst", "--produce-unsat-cores",
        "--proof-format-mode=alethe", "--proof-granularity=dsl-rewrite"] do
    throw <| IO.userError "cvc5 proof argv drifted"
  unless args .bitwuzla {} == #["--produce-models", "--time-limit", "5000"] do
    throw <| IO.userError s!"bitwuzla argv: {args .bitwuzla {}}"
  unless (backendArgs { backend := .none } 5000 {}).isNone do
    throw <| IO.userError "backend none produced an argv"
  for (backend, req) in [(Backend.z3, ({} : SolverRequest)), (.cvc5, { cores := true, proofs := true })] do
    if (args backend req).contains "--incremental" then
      throw <| IO.userError s!"{backend} still requests incremental mode"

-- A saved script carries the request's prologue.
set_option crush.save ".lake/crush-solver-requests-test.smt2" in
set_option crush.backend "cvc5" in
set_option crush.trust "reconstruct" in
set_option crush.reconstruct "core" in
example (a b : Int) (h : a = b) : b = a := by
  crush

#eval show IO Unit from do
  let saved ← IO.FS.readFile ".lake/crush-solver-requests-test.smt2"
  unless (saved.splitOn "produce-unsat-cores").length == 2 &&
      (saved.splitOn "produce-proofs").length == 1 do
    throw <| IO.userError "the saved script does not reproduce the core-only request"

end SolverRequests
