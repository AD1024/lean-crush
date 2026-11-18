import Lean
import Crush.SMT.Syntax
import Crush.SMT.Print
import Crush.SMT.Sexp
import Crush.Frontend.Config

/-!
# Solver process management

Run the solver queries of one `crush` call under one wall-clock budget covering
each verdict and its follow-up output. Drain stdout and stderr concurrently with stdin
writes to avoid pipe deadlocks, then kill and reap the child on every exit path.
Resolve the executable before launch, distinguish missing backends and process errors
from solver unknown results, and request only what the configuration uses: an unsat
core when a reconstructing policy or the result trace reads it, and a proof only for
cvc5 Alethe replay. Parse the captured output once for downstream verdict, model,
core, and certificate handling.
-/

open Lean

namespace Crush.Solver

open Crush SMT

/-- The three answers an SMT solver can give.

`unsat` carries the parsed follow-up output split into the core (the first list
S-expression of the response) and the proof (whatever follows it). Keeping them apart
is what makes `crush_fact_<n>` scanning find the core rather than the proof's internal
references to facts outside it. -/
inductive Result where
  /-- `diagnostics` carries commands the solver refused; see `rejectionDiagnostics`. -/
  | sat     (model : String) (diagnostics : String)
  | unsat   (core : Option SMT.Sexp) (proof : Array SMT.Sexp)
  | unknown (reason : String)
  deriving Inhabited

/-- What a query asks the solver for beyond its verdict. -/
structure SolverRequest where
  /-- `:produce-unsat-cores` and `(get-unsat-core)`. -/
  cores : Bool := false
  /-- `:produce-proofs` and `(get-proof)`; for cvc5 also the Alethe proof flags. -/
  proofs : Bool := false
  deriving BEq, Repr, Inhabited

/-- Static description of how to launch a backend. -/
structure BackendSpec where
  exe   : String
  /-- Build argv given the solver's time limit in milliseconds and the request. -/
  args  : Nat → SolverRequest → Array String
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
      -- `-T` takes whole seconds; the wall-clock guard enforces the exact deadline.
      args := fun ms _ => #["-in", "-smt2", s!"-T:{max 1 ((ms + 999) / 1000)}"]
      logic := id
      -- z3's proofs are never replayed (replay reads cvc5's Alethe format only).
      proofs := false }
  | .cvc5 => some {
      exe := "cvc5"
      -- Each process issues one `check-sat`, so `--incremental` is not needed. Alethe
      -- certificates with expanded rewrite steps improve checked replay coverage; replay
      -- must independently prove any remaining holes.
      args := fun ms request =>
        #[s!"--tlimit={ms}", "--produce-models", "--enum-inst"]
          ++ (if request.cores then #["--produce-unsat-cores"] else #[])
          ++ (if request.proofs then
                #["--proof-format-mode=alethe", "--proof-granularity=dsl-rewrite"]
              else #[])
      logic := id }
  | .bitwuzla => some {
      exe := "bitwuzla"
      args := fun ms _ => #["--produce-models", "--time-limit", toString ms]
      -- bitwuzla implements the bit-vector/array/UF fragment and rejects `ALL`.
      logic := fun _ => "QF_AUFBV"
      unsatCores := false
      proofs := false }
  | .none => none

/-- Locate an executable the way process launch does: a name containing a path separator
is taken as a path, a bare name is searched on `PATH`. -/
def resolveExe (exe : String) : BaseIO (Option System.FilePath) := do
  let candidate? (path : System.FilePath) : BaseIO (Option System.FilePath) := do
    let variants :=
      if System.FilePath.exeExtension.isEmpty then #[path]
      else #[path, path.addExtension System.FilePath.exeExtension]
    for p in variants do
      if (← p.pathExists) && !(← p.isDir) then return some p
    return none
  if System.FilePath.pathSeparators.any (fun sep => exe.contains sep) then
    return ← candidate? exe
  let some searchPath ← IO.getEnv "PATH" | return none
  for dir in System.SearchPath.parse searchPath do
    if let some found ← candidate? (dir / exe) then return some found
  return none

/-- Substring of the Lean runtime's message for a child that could not `exec`. Catches what
`resolveExe` cannot predict: a file that exists but is not executable or is built for
another platform. -/
private def launchFailureMarker : String := "could not execute external process"

/-- One-line, length-capped excerpt of solver output. A child that fails to `exec` inherits
the elaborator's own output, which is why the cap is not optional. -/
private def excerpt (text : String) : String :=
  let lines := text.splitOn "\n" |>.filterMap fun line =>
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then none else some trimmed
  let joined := String.intercalate "; " (lines.take 3)
  if joined.length > 240 then (joined.take 240).toString ++ "..." else joined

/-- Pre-verdict output naming a command the solver refused.

z3 and cvc5 answer an unsupported command with `(error …)` and keep reading, so the verdict
covers only the fragment they accepted. `unsat` survives that — a subset being unsatisfiable
implies the whole is — while `sat` and `unknown` describe that fragment, not the goal. -/
private def rejectionDiagnostics (noise : Array String) : String :=
  let errors := noise.filter fun line => line.trimAscii.toString.startsWith "(error"
  if errors.isEmpty then "" else excerpt (String.intercalate "\n" errors.toList)

/-- The executable a backend launches, or `none` for a backend that runs no process. -/
def backendExe (backend : Backend) : Option String := (backendSpec backend).map (·.exe)

/-- Whether the backend's solver executable can be located. -/
def backendAvailable (backend : Backend) : BaseIO Bool := do
  let some exe := backendExe backend | return false
  return (← resolveExe exe).isSome

/-- Diagnostic for a selected backend whose executable is not installed. It names the other
installed backends, since switching is usually the faster fix than installing. -/
private def missingSolverMessage (backend : Backend) (exe : String) : BaseIO MessageData := do
  let mut installed : Array String := #[]
  for other in Backend.all do
    if other != backend && (← backendAvailable other) then
      installed := installed.push (toString other)
  let advice :=
    if installed.isEmpty then
      m!"No supported solver was found on `PATH`."
    else
      m!"Installed here: {String.intercalate ", " installed.toList}; select one with \
         `set_option crush.backend \"{installed[0]!}\"`."
  return m!"crush: backend `{backend}` needs the `{exe}` executable, which was not found \
            on `PATH`. Install {exe}, or switch backends. {advice}"

/-- What a configuration asks the solver for (decision 5).

* Cores: a reconstructing policy reads them. Under `trust` only the
  `trace.crush.result` line reads the core, and the trusted proof uses every asserted
  fact, so a core is requested only when that trace is on.
* Proofs: only cvc5's Alethe certificate is replayed, under a reconstructing policy
  whose `crush.reconstruct` is not `core`.

Both also require the backend to support the feature. -/
def SolverRequest.ofConfig (cfg : Config) (traceResult : Bool) : SolverRequest :=
  let spec? := backendSpec cfg.backend
  { cores := spec?.any (·.unsatCores) && (cfg.trust != .trust || traceResult)
    proofs := spec?.any (·.proofs) && cfg.trust != .trust && cfg.backend == .cvc5
      && cfg.reconstruct != .core }

/-- The request for `cfg` under the current options. -/
def SolverRequest.current (cfg : Config) : CoreM SolverRequest := do
  return .ofConfig cfg (← isTracingEnabledFor `crush.result)

/-- The options `runQuery` sends before the script for a request. `maybeSave` writes
these too, so a saved script reproduces the query that was run. -/
def prologue (request : SolverRequest) : Array SMT.Command :=
  let cores := if request.cores then #[SMT.Command.setOption "produce-unsat-cores" "true"] else #[]
  let proofs := if request.proofs then #[SMT.Command.setOption "produce-proofs" "true"] else #[]
  cores ++ proofs

/-- The follow-up commands sent after an `unsat` verdict for a request. -/
def unsatFollowUp (request : SolverRequest) : Array SMT.Command :=
  (if request.cores then #[SMT.Command.getUnsatCore] else #[])
    ++ (if request.proofs then #[SMT.Command.getProof] else #[])

/-- The argv for a backend, a solver time limit in milliseconds, and a request. -/
def backendArgs (cfg : Config) (limitMs : Nat) (request : SolverRequest) :
    Option (Array String) :=
  (backendSpec cfg.backend).map fun spec => spec.args limitMs request ++ cfg.additionalArgs

/-- Kill margin past the solver's own limit, so a solver that honours its limit can
still print its verdict. -/
def killGraceMs : Nat := 2000

/-- A wall-clock budget shared by the solver queries of one `crush` call:
`crush.timeout` is a per-call limit. The first query gets `crush.timeout` as its own
limit; every query is killed at one deadline, `killGraceMs` after that limit, and a
later query gets only the time left before it. -/
structure QueryBudget where
  /-- When every query of the call is killed (`IO.monoMsNow` milliseconds). -/
  deadline : Nat
  deriving Inhabited

/-- Start the budget for a call now. -/
def QueryBudget.start (cfg : Config) : BaseIO QueryBudget := do
  return { deadline := (← IO.monoMsNow) + cfg.timeout * 1000 + killGraceMs }

/-- Milliseconds left before the deadline. -/
def QueryBudget.remainingMs (budget : QueryBudget) : BaseIO Nat := do
  return budget.deadline - (← IO.monoMsNow)

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
def spawn (cfg : Config) (limitMs : Nat) (request : SolverRequest) : MetaM SolverProc := do
  let some spec := backendSpec cfg.backend
    | throwError "crush: backend `{cfg.backend}` does not spawn a solver process"
  unless ← backendAvailable cfg.backend do
    throwError (← missingSolverMessage cfg.backend spec.exe)
  let args := spec.args limitMs request ++ cfg.additionalArgs
  -- Keep OS lookup at launch; prior resolution only checks availability.
  try
    IO.Process.spawn { stdin := .piped, stdout := .piped, stderr := .piped,
                       cmd := spec.exe, args }
  catch e =>
    throwError "crush: backend `{cfg.backend}` failed to launch the `{spec.exe}` \
                executable.\n{e.toMessageData}"

/-- Render commands as the text to feed the solver, newline-terminated. Sent in one
`putStr` rather than a write and flush per command. -/
private def commandText (cmds : Array SMT.Command) : String :=
  if cmds.isEmpty then "" else scriptToString cmds ++ "\n"

/-- Read stdout until the verdict token appears, returning it with the lines that
preceded it.

Those lines are diagnostics emitted while the script was consumed (cvc5 answers
`(error …)` for a command it cannot process). The scan runs inside one task so a query
holds a single reader thread rather than one per line. -/
private partial def readVerdictLine (h : IO.FS.Handle) : IO (String × Array String) := do
  let mut noise : Array String := #[]
  while true do
    let line ← h.getLine
    if line.isEmpty then return ("", noise)
    let token := line.trimAscii.toString
    -- `getLine` returns "" only at EOF.
    if token.isEmpty then continue
    if token == "sat" || token == "unsat" || token == "unknown" then return (token, noise)
    if noise.size < 32 then
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
result-extraction commands ourselves. The solver's own limit is `limitMs`
(`crush.timeout` by default), and the child is killed at the deadline of `budget` (a
fresh call budget by default), which also covers the follow-up output. On timeout
before a verdict we return `.unknown "timeout"`. A timeout while reading the follow-up
output keeps the verdict: `unsat` then carries no core or proof. Without `getModel`, `sat`
returns at once with no model. The child is always killed before returning. -/
def runQuery (cfg : Config) (script : Array SMT.Command)
    (budget? : Option QueryBudget := none) (limitMs? : Option Nat := none)
    (getModel := true) : MetaM Result := do
  let some _ := backendSpec cfg.backend
    | throwError "crush: backend `{cfg.backend}` does not spawn a solver process"
  let request ← SolverRequest.current cfg
  let budget ← budget?.getDM (QueryBudget.start cfg)
  let limitMs := max 1 (limitMs?.getD (cfg.timeout * 1000))
  let p ← spawn cfg limitMs request
  let deadline := budget.deadline
  let timerTask ← IO.asTask (prio := .dedicated) do
    let now ← IO.monoMsNow
    if now < deadline then IO.sleep (deadline - now).toUInt32
  -- Drained for the child's whole lifetime; see the module comment.
  let errTask ← IO.asTask (prio := .dedicated) p.stderr.readToEnd
  try
    -- Fed from a task, so stdout is drained while the script is still going in.
    let text := commandText (prologue request ++ script ++ #[.checkSat])
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
        let some rest ← drainResponse p (unsatFollowUp request) timerTask
          | trace[crush.result] "timed out reading the core and proof after `unsat`; \
              keeping the verdict without them"
            return .unsat none #[]
        let (core, proof) :=
          splitCoreAndProof request.cores request.proofs (SMT.parseSexpPrefix rest)
        return .unsat core proof
      | "sat" =>
        if wrote.isNone then return .unknown "writing the solver script failed or timed out"
        unless getModel do return .sat "" (rejectionDiagnostics noise)
        let some model ← drainResponse p #[.getModel] timerTask
          | trace[crush.result] "timed out reading the model after `sat`"
            return .sat "" (rejectionDiagnostics noise)
        return .sat model (rejectionDiagnostics noise)
      | "unknown" =>
        if wrote.isNone then return .unknown "writing the solver script failed or timed out"
        let reason := (← drainResponse p #[] timerTask).getD "timeout"
        let rejected := rejectionDiagnostics noise
        return .unknown (if rejected.isEmpty then reason else s!"{reason}; {rejected}")
      | _ =>
        -- Report startup or process failure from stderr when no verdict was produced.
        let errDetail ← stderrExcerpt errTask timerTask
        if errDetail.contains launchFailureMarker then
          let exe := (backendExe cfg.backend).getD "solver"
          throwError "crush: backend `{cfg.backend}` could not run the `{exe}` \
                      executable: {errDetail}. Check that it is installed, executable, \
                      and built for this platform."
        let details :=
          #[excerpt (String.intercalate "\n" noise.toList), errDetail].filter (!·.isEmpty)
            |>.toList
        let detail := if details.isEmpty then "" else s!": {String.intercalate "; " details}"
        if wrote.isNone then
          return .unknown
            s!"solver exited without a verdict; writing the script failed or timed out{detail}"
        return .unknown s!"solver exited without a verdict{detail}"
  finally
    IO.cancel timerTask
    -- Kill unconditionally; harmless if already exited.
    try p.kill catch _ => pure ()
    -- Reap the process after killing it; otherwise repeated tactic calls can
    -- accumulate zombies on Unix.
    try discard p.wait catch _ => pure ()
    -- Killing closes stderr; its drain task can finish at EOF without blocking cleanup.
    pure ()
where
  /-- Excerpt of the child's stderr; empty when it cannot be read before the query's
  deadline. -/
  stderrExcerpt (errTask : Task (Except IO.Error String))
      (timerTask : Task (Except IO.Error Unit)) : BaseIO String := do
    let some text ← awaitBy errTask timerTask | return ""
    return excerpt text

  /-- Send the follow-up queries, then read the rest of the response.

  `(exit)` and closing stdin come *before* reading, so the child terminates and the
  stdout pipe reaches EOF instead of `readToEnd` waiting out the solver's own timeout.
  `(exit)` is the fast path; closing stdin is the EOF for a solver that ignores it.

  A solver that has already exited makes the write fail; the verdict still stands, so
  the response is simply empty. `none` means the deadline passed while reading: the
  child is killed, and the caller keeps the verdict. -/
  drainResponse (p : SolverProc) (follow : Array SMT.Command)
      (timerTask : Task (Except IO.Error Unit)) :
      MetaM (Option String) := do
    try
      p.stdin.putStr (commandText (follow ++ #[.exit]))
      p.stdin.flush
    catch _ => return some ""
    let (_, p) ← p.takeStdin
    let readTask ← IO.asTask (prio := .dedicated) p.stdout.readToEnd
    match ← awaitBy readTask timerTask with
    | some response => return some response
    | none =>
      try p.kill catch _ => pure ()
      return none

/-- Optionally write the script to disk for debugging / reproducing.

Includes the same option prologue `runQuery` sends, so replaying the file reproduces the
core and certificate too. -/
def maybeSave (cfg : Config) (script : Array SMT.Command) : MetaM Unit := do
  if cfg.savePath.isEmpty then return
  let prefixCmds := prologue (← SolverRequest.current cfg)
  IO.FS.writeFile cfg.savePath
    (scriptToString (prefixCmds ++ script) ++ "\n(check-sat)\n")

end Crush.Solver
