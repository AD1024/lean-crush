import Lean
import Crush.SMT.Syntax
import Crush.SMT.Print
import Crush.Frontend.Config
open Lean

/-!
# Solver process management

Spawns and drives an SMT solver as a child process. The design points, each
guarding against a way this layer commonly goes wrong:

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
      args := fun _ => #["--produce-models"]
      logic := id }
  | .none => none

/-- Split off the first complete parenthesized s-expression, returning it and the
remaining text. Used to separate a `get-unsat-core` response from the
`get-proof` output that follows it on the same stream.

Tracks nesting depth and skips over string literals so a `)` inside a quoted string
cannot end the expression early. Text before the first `(` is dropped (it is
whitespace or a stray token); if no balanced expression is found, everything is
returned as the first component so the caller still sees the output. -/
def splitFirstSexp (s : String) : String × String := Id.run do
  let cs := s.toList
  let mut depth : Nat := 0
  let mut started := false
  let mut inStr := false
  let mut acc : List Char := []
  let mut rest : List Char := []
  let mut done := false
  for c in cs do
    if done then
      rest := c :: rest
    else if inStr then
      acc := c :: acc
      if c == '"' then inStr := false
    else if c == '"' then
      acc := c :: acc; inStr := true
    else if c == '(' then
      started := true; depth := depth + 1; acc := c :: acc
    else if c == ')' then
      acc := c :: acc
      depth := depth - 1
      if started && depth == 0 then done := true
    else if started then
      acc := c :: acc
  let first := String.ofList acc.reverse
  let remaining := String.ofList rest.reverse
  if done then (first, remaining) else (s, "")

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
        let rest ← drainResponse p
        -- The core is the *first* s-expression of the response, the proof is
        -- whatever follows. They must be separated here: a proof term mentions the
        -- asserted fact names many times over, so scanning the concatenation for
        -- `crush_fact_<n>` yields the proof's internal references rather than the
        -- core, complete with duplicates and facts that are not in the core at all.
        let (core, proof) := splitFirstSexp rest
        return .unsat core proof
      | "sat" =>
        putCmd p .getModel
        return .sat (← drainResponse p)
      | "unknown" =>
        return .unknown (← drainResponse p)
      | other => return .unknown s!"unexpected solver response: {other}"
  finally
    -- Kill unconditionally; harmless if already exited.
    try p.kill catch _ => pure ()
where
  /-- Read the solver's remaining response after the verdict line, then let it exit.
  Sends `(exit)` and closes stdin *before* reading so the child terminates and the
  stdout pipe reaches EOF — otherwise `readToEnd` blocks until the solver's own
  timeout (`-T`/`--tlimit`) kills it, adding the full budget to every call. `(exit)`
  is the fast path; `takeStdin` (closing stdin) is the belt-and-suspenders EOF for a
  solver that ignores it. Only the follow-up queries (`get-model`/`get-unsat-core`/
  `get-proof`) have been sent at this point, so nothing after `(exit)` is lost. -/
  drainResponse (p : SolverProc) : MetaM String := do
    putCmd p .exit
    let (_, p) ← p.takeStdin
    p.stdout.readToEnd
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
