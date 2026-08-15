import Lean
import Crush.SMT.Syntax
import Crush.SMT.Print
import Crush.SMT.Sexp
import Crush.Frontend.Config
open Lean

/-!
# Solver process management

Spawns and drives an SMT solver as a child process. The design points, each
guarding against a way this layer commonly goes wrong:

* **Wall-clock timeout is enforced by us**, not just delegated to the solver's
  own `-T`/`--tlimit` flag. One deadline covers the whole query — the verdict line and
  the model / core / proof that follows it — so a wedged or ignoring-its-own-limit
  solver can never hang the elaborator and the worst case matches `crush.timeout`.
* **Both output pipes are drained concurrently with the script write.** Writing to the
  child's stdin while nothing reads its stdout deadlocks once the solver's replies fill
  the pipe buffer; cvc5 answers `(error …)` per unsupported command, and z3 warns to
  stderr for every unsupported construct.
* **Guaranteed cleanup**: the child is killed in a `finally` block on every exit
  path (success, `unknown`, exception), preventing the zombie processes that
  accumulate when `emitCommand` throws mid-query.
* **`unknown` is a first-class result**, distinct from `sat`/`unsat`, so the
  tactic can report "solver gave up" instead of a misleading failure.
* Backends and their flags are data-driven (`backendSpec`), so adding bitwuzla or
  a portfolio is a table entry, not new control flow. A backend declares which optional
  features it has, and only those options and follow-up queries are sent.
* Solver output is parsed **once**, here, and handed downstream as S-expressions.
-/

namespace Crush.Solver

open Crush SMT

/-- The three answers an SMT solver can give.

`unsat` carries the parsed follow-up output split into the core (the first list
S-expression of the response) and the proof (whatever follows it). Keeping them apart
is what makes `crush_fact_<n>` scanning find the core rather than the proof's internal
references to facts outside it. -/
inductive Result where
  | sat     (model : String)
  | unsat   (core : Option SMT.Sexp) (proof : Array SMT.Sexp)
  | unknown (reason : String)
  deriving Inhabited

/-- Static description of how to launch a backend. -/
structure BackendSpec where
  exe   : String
  /-- Build argv given the timeout in seconds. -/
  args  : Nat → Array String
  /-- Backend-specific massaging of the resolved `set-logic` string. -/
  logic : String → String
  /-- Whether `:produce-unsat-cores` and `(get-unsat-core)` are supported. Core-directed
  reconstruction is unavailable on a backend without them. -/
  unsatCores : Bool := true
  /-- Whether `:produce-proofs` and `(get-proof)` are supported. -/
  proofs : Bool := true

def backendSpec (b : Backend) : Option BackendSpec :=
  match b with
  | .z3 => some {
      exe := "z3"
      args := fun t => #["-in", "-smt2", s!"-T:{t}"]
      logic := id }
  | .cvc5 => some {
      exe := "cvc5"
      -- `--proof-format-mode=alethe` makes `(get-proof)` emit the format
      -- `Crush.Alethe` parses (cvc5's native format is a different language), and
      -- `--proof-granularity=dsl-rewrite` expands the coarse `hole` steps
      -- ("untranslated rewrite") into checkable ones — measured 4 holes → 0 on a small
      -- linear goal. A `hole` is a gap replay must reject, so the granularity flag is
      -- what makes proofs replayable at all.
      args := fun t => #[s!"--tlimit={t * 1000}", "--produce-models",
                          "--produce-unsat-cores", "--enum-inst", "--incremental",
                          "--proof-format-mode=alethe", "--proof-granularity=dsl-rewrite"]
      logic := id }
  | .bitwuzla => some {
      exe := "bitwuzla"
      args := fun t => #["--produce-models", "--time-limit", toString (t * 1000)]
      -- bitwuzla implements the bit-vector/array/UF fragment and rejects `ALL`.
      logic := fun _ => "QF_AUFBV"
      unsatCores := false
      proofs := false }
  | .none => none

/-- The options `runQuery` sends before the script, given the backend's capabilities.
`maybeSave` writes these too, so a saved script reproduces the same query. -/
def prologue (spec : BackendSpec) : Array SMT.Command :=
  let cores := if spec.unsatCores then #[SMT.Command.setOption "produce-unsat-cores" "true"] else #[]
  let proofs := if spec.proofs then #[SMT.Command.setOption "produce-proofs" "true"] else #[]
  cores ++ proofs

/-- Split a parsed solver response according to the backend's enabled follow-ups.
Leading atoms (a status token some solvers repeat) are skipped, matching the
S-expression parser rather than slicing the text. -/
def splitCoreAndProof (hasCore hasProof : Bool) (response : Array SMT.Sexp) :
    Option SMT.Sexp × Array SMT.Sexp :=
  match response.findIdx? SMT.Sexp.isList with
  | some i =>
    if hasCore then
      (response[i]?, if hasProof then response.extract (i + 1) response.size else #[])
    else
      (none, if hasProof then response.extract i response.size else #[])
  | none => (none, #[])

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

/-- Render commands as the text to feed the solver, newline-terminated. Sent in one
`putStr` rather than a write and flush per command. -/
private def commandText (cmds : Array SMT.Command) : String :=
  if cmds.isEmpty then "" else scriptToString cmds ++ "\n"

/-- Read stdout until the verdict token appears, returning it with the lines that
preceded it.

Those lines are diagnostics emitted while the script was consumed (cvc5 answers
`(error …)` for a command it cannot process). The scan runs inside one task so a query
holds a single reader thread rather than one per line. -/
private def readVerdictLine (h : IO.FS.Handle) : IO (String × Array String) := do
  let mut noise : Array String := #[]
  -- A bound on lines keeps the loop total; the caller's deadline is the real limit.
  for _ in [0:4096] do
    let line ← h.getLine
    if line.isEmpty then return ("", noise)
    let token := line.trimAscii.toString
    -- `getLine` returns "" only at EOF.
    if token.isEmpty then continue
    if token == "sat" || token == "unsat" || token == "unknown" then return (token, noise)
    noise := noise.push token
  return ("", noise)

/-- Wait for `task`, giving up when the query's shared timer finishes. -/
private def awaitBy {α : Type} (task : Task (Except IO.Error α))
    (timer : Task (Except IO.Error Unit)) :
    BaseIO (Option α) := do
  let reader := task.map (sync := true) fun
    | .ok value => some value
    | .error _ => none
  let timer := timer.map (sync := true) fun _ => (none : Option α)
  IO.waitAny [reader, timer]

/-- Run a full query with our own wall-clock guard.

`script` is the declaration/assertion prefix; we append the check-sat and
result-extraction commands ourselves. On timeout we kill the child and return
`.unknown "timeout"`. The child is always killed before returning. -/
def runQuery (cfg : Config) (script : Array SMT.Command) : MetaM Result := do
  let some spec := backendSpec cfg.backend
    | throwError "crush: backend `{cfg.backend}` does not spawn a solver process"
  let p ← spawn cfg
  -- A small grace margin over the solver's internal limit, so a well-behaved solver's
  -- own timeout fires first (yielding `unknown` rather than a hard kill). One deadline
  -- for the whole query, verdict line and follow-up output together.
  let start ← IO.monoMsNow
  let deadline := start + (cfg.timeout + 2) * 1000
  let timerTask ← IO.asTask (prio := .dedicated) do
    let now ← IO.monoMsNow
    if now < deadline then IO.sleep (deadline - now).toUInt32
  -- Drained for the child's whole lifetime; see the module comment.
  let errTask ← IO.asTask (prio := .dedicated) p.stderr.readToEnd
  try
    -- Fed from a task, so stdout is drained while the script is still going in.
    let text := commandText (prologue spec ++ script ++ #[.checkSat])
    let writeTask ← IO.asTask (prio := .dedicated) (do
      p.stdin.putStr text
      p.stdin.flush)
    let readTask ← IO.asTask (prio := .dedicated) (readVerdictLine p.stdout)
    match ← awaitBy readTask timerTask with
    | none => return .unknown "timeout"
    | some (token, noise) =>
      -- The solver cannot answer `check-sat` before receiving it, but the writer may
      -- still be flushing. Finish it before sending follow-up commands on the same pipe.
      let wrote ← awaitBy writeTask timerTask
      match token with
      | "unsat" =>
        if wrote.isNone then return .unknown "writing the solver script failed or timed out"
        let follow :=
          (if spec.unsatCores then #[SMT.Command.getUnsatCore] else #[])
            ++ (if spec.proofs then #[SMT.Command.getProof] else #[])
        let rest ← drainResponse p follow timerTask
        let (core, proof) :=
          splitCoreAndProof spec.unsatCores spec.proofs (SMT.parseSexpPrefix rest)
        return .unsat core proof
      | "sat" =>
        if wrote.isNone then return .unknown "writing the solver script failed or timed out"
        return .sat (← drainResponse p #[.getModel] timerTask)
      | "unknown" =>
        if wrote.isNone then return .unknown "writing the solver script failed or timed out"
        return .unknown (← drainResponse p #[] timerTask)
      | _ =>
        let detail := String.intercalate " " noise.toList
        if wrote.isNone then
          return .unknown "solver exited without a verdict; writing the script failed or timed out"
        if detail.isEmpty then
          return .unknown "solver exited without a verdict"
        else
          return .unknown s!"solver exited without a verdict: {detail}"
  finally
    IO.cancel timerTask
    -- Kill unconditionally; harmless if already exited.
    try p.kill catch _ => pure ()
    -- Reap the process after killing it; otherwise repeated tactic calls can
    -- accumulate zombies on Unix.
    try discard p.wait catch _ => pure ()
    -- `errTask` is left to finish on its own: the kill above closes stderr, so it reaches
    -- EOF, and its content is only ever needed to keep the child from blocking on a full
    -- pipe.
    pure ()
where
  /-- Send the follow-up queries, then read the rest of the response.

  `(exit)` and closing stdin come *before* reading, so the child terminates and the
  stdout pipe reaches EOF instead of `readToEnd` waiting out the solver's own timeout.
  `(exit)` is the fast path; closing stdin is the EOF for a solver that ignores it.

  A solver that has already exited makes the write fail; the verdict still stands, so
  the response is simply empty. -/
  drainResponse (p : SolverProc) (follow : Array SMT.Command)
      (timerTask : Task (Except IO.Error Unit)) :
      MetaM String := do
    try
      p.stdin.putStr (commandText (follow ++ #[.exit]))
      p.stdin.flush
    catch _ => return ""
    let (_, p) ← p.takeStdin
    let readTask ← IO.asTask (prio := .dedicated) p.stdout.readToEnd
    match ← awaitBy readTask timerTask with
    | some response => return response
    | none =>
      try p.kill catch _ => pure ()
      throwError "crush: timed out reading solver output after its verdict"

/-- Optionally write the script to disk for debugging / reproducing.

Includes the same option prologue `runQuery` sends, so replaying the file reproduces the
core and certificate too. -/
def maybeSave (cfg : Config) (script : Array SMT.Command) : MetaM Unit := do
  if cfg.savePath.isEmpty then return
  let prefixCmds := (backendSpec cfg.backend).map prologue |>.getD #[]
  IO.FS.writeFile cfg.savePath
    (scriptToString (prefixCmds ++ script) ++ "\n(check-sat)\n")

end Crush.Solver
