import Crush.SMT.Sexp

/-!
# Parsing Alethe proof certificates

cvc5, run with `--dump-proofs --proof-format-mode=alethe`, emits its refutation as an
**Alethe** proof: a list of `assume`/`step`/`anchor` commands over clauses, ending in
the empty clause. This module turns that text into a structured `AletheProof` so a
replay pass can walk it. It does **not** check the proof — parsing decides nothing, so
this layer is sound on its own; a checker is a separate, later phase.

## Why a parser, and what consumes it

A sound Lean *checker* for Alethe is a large undertaking: even a single small
nonlinear goal produces ~200 steps across ~30 distinct rules (`resolution`, `cong`,
`la_generic`, `rare_rewrite`, …), nested subproofs, and requires mapping the proof's
SMT terms back to Lean `Expr`s (our translation is one-directional). Each rule needs a
soundness argument. So M4 is staged: this parser is the foundation, checked against
real cvc5 output; anything built on it holds the invariant that **any step the replay
cannot discharge is a hard failure, never a trusted gap** — so partial coverage stays
sound, it just falls back to the core-directed finisher (or errors under `reconstruct`).

The current consumer is `Crush/Solver/ProofGuide.lean`, which reads the proof as a
*guide* for choosing reconstruction finishers rather than replaying it rule by rule.
That is where the `hole`-means-unusable policy lives.

## The Alethe surface we parse

An Alethe proof is a sequence of commands (SMT-LIB S-expressions):

* `(assume H term)` — an input assumption `H` with its formula.
* `(step id (cl t₁ … tₙ) :rule R :premises (…) :args (…))` — a derived clause `id`,
  the disjunction `t₁ ∨ … ∨ tₙ` (empty = `false`), justified by rule `R` from the
  named premises and arguments.
* `(anchor :step id …)` opening a subproof, matched by a later `step id` whose rule is
  `subproof`. We record anchors so the block structure survives, but flatten steps
  into one list keyed by their (possibly dotted, e.g. `t17.t10.t16`) ids.

`:named` annotations (`(! term :named @p_1)`) appear throughout to share subterms; we
keep the term and drop the annotation when normalizing, so a `@p_k` reference and its
definition are the same parsed term.
-/

namespace Crush.Alethe

open Crush.SMT

/-- One command in an Alethe proof. Terms are kept as `Sexp` — the replay layer, not
the parser, is what eventually interprets them. -/
inductive Command where
  /-- `(assume id term)`. -/
  | assume (id : String) (term : Sexp)
  /-- `(step id (cl …) :rule R :premises (…) :args (…))`. `clause` is the list of
  disjunct terms (empty ⇒ the empty clause, i.e. `false`). -/
  | step (id : String) (clause : Array Sexp) (rule : String)
         (premises : Array String) (args : Array Sexp)
  /-- `(anchor :step id …)` — opens a subproof closed by `step id … :rule subproof`. -/
  | anchor (id : String) (args : Array Sexp)
  deriving Inhabited, Repr

/-- A parsed Alethe proof: the commands in order. The last `step` derives the empty
clause; `emptyClauseStep?` finds it. -/
structure AletheProof where
  commands : Array Command
  deriving Inhabited, Repr

/-- Strip an Alethe `(! term :named @p) ` / `:pattern …` annotation down to `term`.
Named-term sharing is purely a printing device, so a consumer should see the term. -/
partial def stripAnnot : Sexp → Sexp
  | .list xs =>
    match xs[0]? with
    | some (Sexp.atom "!") =>
      -- `(! t :kw v …)` — the payload is the second element; recurse into it.
      match xs[1]? with
      | some t => stripAnnot t
      | none => .list (xs.map stripAnnot)
    | _ => .list (xs.map stripAnnot)
  | s => s

/-- The keyword-tagged tail of a `step`, as an assoc list from `:kw` to the following
S-expression. `:rule R :premises (…) :args (…)` → `[("rule", R), …]`. A keyword with
no following value maps to an empty list. -/
private def keywordArgs (rest : Array Sexp) : Array (String × Sexp) := Id.run do
  let mut out : Array (String × Sexp) := #[]
  let mut i := 0
  while h : i < rest.size do
    match rest[i] with
    | Sexp.atom kw =>
      if kw.startsWith ":" then
        let key : String := (kw.drop 1).toString
        if let some v := rest[i+1]? then
          out := out.push (key, v)
          i := i + 2
        else
          out := out.push (key, Sexp.list #[])
          i := i + 1
      else
        i := i + 1
    | _ => i := i + 1
  return out

/-- Element atoms of a list `Sexp` (for `:premises (t1 t2)`), or `#[]`. -/
private def atomList (s : Sexp) : Array String :=
  match s with
  | .list xs => xs.filterMap (·.atom?)
  | _ => #[]

/-- The disjuncts of a `(cl t₁ … tₙ)` clause, annotations stripped. A bare `cl` with
no terms is the empty clause. -/
private def parseClause (s : Sexp) : Array Sexp :=
  match s with
  | .list xs =>
    match xs[0]? with
    | some (Sexp.atom "cl") => (xs.extract 1 xs.size).map stripAnnot
    | _ => #[]
  | _ => #[]

/-- Parse one top-level Alethe command S-expression, if it is one we recognize. -/
def parseCommand (s : Sexp) : Option Command :=
  match s with
  | .list xs =>
    match xs[0]? with
    | some (Sexp.atom "assume") =>
      match xs[1]?, xs[2]? with
      | some (Sexp.atom id), some term => some (.assume id (stripAnnot term))
      | _, _ => none
    | some (Sexp.atom "step") =>
      match xs[1]?, xs[2]? with
      | some (Sexp.atom id), some clause =>
        let kw := keywordArgs (xs.extract 3 xs.size)
        let ruleOf := (kw.find? (·.1 == "rule")).map (·.2)
        let rule := match ruleOf with | some (Sexp.atom r) => r | _ => ""
        let premises := match (kw.find? (·.1 == "premises")).map (·.2) with
          | some p => atomList p | none => #[]
        let args := match (kw.find? (·.1 == "args")).map (·.2) with
          | some (.list a) => a.map stripAnnot | _ => #[]
        some (.step id (parseClause clause) rule premises args)
      | _, _ => none
    | some (Sexp.atom "anchor") =>
      let kw := keywordArgs (xs.extract 1 xs.size)
      let id := match (kw.find? (·.1 == "step")).map (·.2) with
        | some (Sexp.atom i) => i | _ => ""
      some (.anchor id (xs.extract 1 xs.size))
    | _ => none
  | _ => none

/-- Parse a full Alethe proof from cvc5's `--dump-proofs` output.

The output begins with the `unsat` status line and then a single parenthesized list
of commands: `unsat\n( (assume …) (step …) … )`. We parse every S-expression and keep
the commands from the largest list found (the proof body), tolerating the leading
`unsat` atom. Returns `none` if no command list is present (e.g. cvc5 emitted an
`(error …)` because the proof is unsupported by Alethe — as it does for
datatype-exhaustiveness goals). -/
def parseProof (text : String) : Option AletheProof := Id.run do
  let tops := parseSexps text
  -- cvc5 emits the proof as one big list of commands. An `(error …)` list means no
  -- proof; detect it so the caller can fall back rather than mis-parse.
  for top in tops do
    if let .list xs := top then
      if let some (Sexp.atom "error") := xs[0]? then
        return none
  -- Find the command list: the list whose elements parse as commands. In practice
  -- there is exactly one, the proof body.
  for top in tops do
    if let .list xs := top then
      let cmds := xs.filterMap parseCommand
      if cmds.size > 0 then
        return some { commands := cmds }
  return none

/-- The `step` deriving the empty clause `(cl)`, if present — the proof's conclusion.
Its existence is a cheap structural sanity check that a proof actually refutes. -/
def AletheProof.emptyClauseStep? (p : AletheProof) : Option Command :=
  p.commands.find? fun
    | .step _ clause _ _ _ => clause.isEmpty
    | _ => false

/-- Count of each command kind, for diagnostics: `(assumes, steps, anchors)`. -/
def AletheProof.stats (p : AletheProof) : Nat × Nat × Nat := Id.run do
  let mut a := 0; let mut s := 0; let mut n := 0
  for c in p.commands do
    match c with
    | .assume .. => a := a + 1
    | .step .. => s := s + 1
    | .anchor .. => n := n + 1
  return (a, s, n)

/-- The distinct rule names used by the proof's steps, for diagnostics and for
deciding whether a replay can handle the proof (an unknown rule ⇒ cannot replay). -/
def AletheProof.rules (p : AletheProof) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  for c in p.commands do
    if let .step _ _ rule _ _ := c then
      unless seen.contains rule do
        seen := seen.insert rule
        out := out.push rule
  return out

end Crush.Alethe
