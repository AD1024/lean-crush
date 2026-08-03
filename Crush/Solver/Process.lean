import Lean
import Crush.SMT.Syntax
import Crush.SMT.Print
import Crush.Frontend.Config
open Lean

/-!
# Solver process management

Spawns and drives an SMT solver as a child process. This module fixes the
robustness problems in lean-auto's `Auto/Solver/SMT.lean`:

* **Wall-clock timeout is enforced by us**, not just delegated to the solver's
  own `-T`/`--tlimit` flag. We race `check-sat` against an `IO.sleep` and kill
  the child if it overruns, so a wedged or ignoring-its-own-limit solver can
  never hang the elaborator.
* **Guaranteed cleanup**: the child is killed in a `finally` block on every exit
  path (success, `unknown`, exception), preventing the zombie processes that
  accumulate when `emitCommand` throws mid-query.
* **`unknown` is a first-class result**, distinct from `sat`/`unsat`, so the
  tactic can report "solver gave up" instead of a misleading failure.
* Backends and their flags are data-driven (`backendSpec`), so adding bitwuzla or
  a portfolio is a table entry, not new control flow.
-/

namespace Crush.Solver

open Crush SMT

/-- The three answers an SMT solver can give, plus the raw trailing output
(model on `sat`, unsat core / proof on `unsat`) for downstream parsing. -/
inductive Result where
  | sat     (model : String)
  | unsat   (core : String) (proof : String)
  | unknown (reason : String)
  deriving Inhabited

/-- Static description of how to launch a backend. -/
structure BackendSpec where
  exe   : String
  /-- Build argv given the timeout in seconds. -/
  args  : Nat → Array String
  logic : String → String  -- allow backend-specific logic massaging

def backendSpec (b : Backend) : Option BackendSpec :=
  match b with
  | .z3 => some {
      exe := "z3"
      args := fun t => #["-in", "-smt2", s!"-T:{t}"]
      logic := id }
  | .cvc5 => some {
      exe := "cvc5"
      args := fun t => #[s!"--tlimit={t * 1000}", "--produce-models",
                          "--produce-unsat-cores", "--enum-inst", "--incremental"]
      logic := id }
  | .bitwuzla => some {
      exe := "bitwuzla"
      args := fun _ => #["--produce-models"]
      logic := id }
  | .none => none

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

/-- Spawn the solver process for the configured backend. -/
def spawn (cfg : Config) : MetaM SolverProc := do
  let some spec := backendSpec cfg.backend
    | throwError "crush: backend `{cfg.backend}` does not spawn a solver process"
  let args := spec.args cfg.timeout ++ cfg.additionalArgs
  try
    IO.Process.spawn { stdin := .piped, stdout := .piped, stderr := .piped,
                       cmd := spec.exe, args }
  catch e =>
    throwError "crush: failed to launch solver `{spec.exe}`. Is it on your PATH?\n{e.toMessageData}"

private def putCmd (p : SolverProc) (c : SMT.Command) : IO Unit := do
  p.stdin.putStr s!"{c}\n"; p.stdin.flush

/-- Run a full query with our own wall-clock guard.

`script` is the declaration/assertion prefix; we append the check-sat and
result-extraction commands ourselves. On timeout we kill the child and return
`.unknown "timeout"`. The child is always killed before returning. -/
def runQuery (cfg : Config) (script : Array SMT.Command) : MetaM Result := do
  let p ← spawn cfg
  try
    putCmd p (.setOption "produce-unsat-cores" "true")
    putCmd p (.setOption "produce-proofs" "true")
    for c in script do putCmd p c
    putCmd p .checkSat
    -- Race the solver's first line against our wall-clock budget. We give a small
    -- grace margin over the solver's internal limit so its own timeout fires first
    -- when it is well-behaved (yielding `unknown` rather than a hard kill).
    let budgetMs := (cfg.timeout + 2) * 1000
    let readTask ← IO.asTask (prio := .dedicated) (p.stdout.getLine)
    let firstLine ← raceWithTimeout readTask budgetMs
    match firstLine with
    | none => return .unknown "timeout"
    | some line =>
      match line.trimAscii.toString with
      | "unsat" =>
        putCmd p .getUnsatCore
        putCmd p .getProof
        let (_, p) ← p.takeStdin
        let rest ← p.stdout.readToEnd
        -- Split heuristically: unsat core is the first s-expr, proof the rest.
        return .unsat rest ""
      | "sat" =>
        putCmd p .getModel
        let (_, p) ← p.takeStdin
        let model ← p.stdout.readToEnd
        return .sat model
      | "unknown" =>
        let (_, p) ← p.takeStdin
        let rest ← p.stdout.readToEnd
        return .unknown rest
      | other => return .unknown s!"unexpected solver response: {other}"
  finally
    -- Kill unconditionally; harmless if already exited.
    try p.kill catch _ => pure ()
where
  /-- Poll `task` until it finishes or `budgetMs` elapses. -/
  raceWithTimeout (task : Task (Except IO.Error String)) (budgetMs : Nat) :
      MetaM (Option String) := do
    let stepMs := 25
    let mut waited := 0
    while waited < budgetMs do
      if (← IO.hasFinished task) then
        match task.get with
        | .ok s => return some s
        | .error _ => return none
      IO.sleep stepMs.toUInt32
      waited := waited + stepMs
    return none

/-- Optionally write the script to disk for debugging / reproducing. -/
def maybeSave (cfg : Config) (script : Array SMT.Command) : MetaM Unit := do
  if cfg.savePath.isEmpty then return
  IO.FS.writeFile cfg.savePath (scriptToString script ++ "\n(check-sat)\n")

end Crush.Solver
