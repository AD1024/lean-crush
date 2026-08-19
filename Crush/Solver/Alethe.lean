import Crush.SMT.Sexp

/-!
# Parsing Alethe proof certificates

cvc5, run with `--dump-proofs --proof-format-mode=alethe`, emits its refutation as an
**Alethe** proof: a list of `assume`/`step`/`anchor` commands over clauses, ending in
the empty clause. This module turns that text into a structured `AletheProof`, and stops
there: parsing decides nothing, so this layer is sound on its own. Checking a proof is
`Crush/Solver/AletheReplay.lean`'s job — it turns a parsed proof into a kernel-checked
Lean term.

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
  /-- `(step id (cl …) :rule R :premises (…) :args (…) :discharge (…))`. `clause` is the
  list of disjunct terms (empty ⇒ the empty clause, i.e. `false`).

  `discharge` names the local assumptions a `subproof` step releases; it is what makes a
  subproof's conclusion an implication rather than a claim under an open hypothesis, so
  replay needs it (an ignored `:discharge` would silently drop the antecedent). -/
  | step (id : String) (clause : Array Sexp) (rule : String)
         (premises : Array String) (args : Array Sexp)
         (discharge : Array String := #[])
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
        let discharge := match (kw.find? (·.1 == "discharge")).map (·.2) with
          | some d => atomList d | none => #[]
        some (.step id (parseClause clause) rule premises args discharge)
      | _, _ => none
    | some (Sexp.atom "anchor") =>
      let kw := keywordArgs (xs.extract 1 xs.size)
      let id := match (kw.find? (·.1 == "step")).map (·.2) with
        | some (Sexp.atom i) => i | _ => ""
      some (.anchor id (xs.extract 1 xs.size))
    | _ => none
  | _ => none

/-- Find cvc5's explanation for refusing to serialize a proof in Alethe format. -/
private partial def proofErrorIn? : Sexp → Option String
  | .list xs => Id.run do
    match xs[0]?, xs[1]? with
    | some (Sexp.atom "error"), some (Sexp.str message) => return some message
    | _, _ =>
      for item in xs do
        if let some message := proofErrorIn? item then
          return some message
      return none
  | _ => none

/-- cvc5's proof-generation error, if the response contains one. -/
def proofError? (tops : Array Sexp) : Option String := Id.run do
  for top in tops do
    if let some message := proofErrorIn? top then
      return some message
  return none

/-- Structure an Alethe proof out of already-parsed solver output.

The output begins with the `unsat` status line and then a single parenthesized list
of commands: `unsat\n( (assume …) (step …) … )`. We keep the commands from the first
list that parses as commands (the proof body), tolerating the leading `unsat` atom.
Returns `none` if no command list is present (e.g. cvc5 emitted an `(error …)`
because the proof is unsupported by Alethe — as it does for
datatype-exhaustiveness goals).

Takes parsed S-expressions, which the caller shares with the `:named` term table
replay builds from the same certificate. -/
def parseProofSexps (tops : Array Sexp) : Option AletheProof := Id.run do
  if (proofError? tops).isSome then return none
  -- Find the command list: the list whose elements parse as commands. In practice
  -- there is exactly one, the proof body.
  for top in tops do
    if let .list xs := top then
      let cmds := xs.filterMap parseCommand
      if cmds.size > 0 then
        return some { commands := cmds }
  return none

/-- Parse a full Alethe proof from cvc5's `--dump-proofs` output text. -/
def parseProof (text : String) : Option AletheProof :=
  parseProofSexps (parseSexps text)

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

/-- Theory features occurring in certificate terms. Indexed operators retain their
base name separately so coverage does not depend on a particular width or index. -/
structure CertificateFeatures where
  operators        : Array String := #[]
  indexedOperators : Array String := #[]
  sorts            : Array String := #[]
  rules            : Array String := #[]
  deriving Inhabited, Repr

private structure FeatureCollector where
  operators        : Array String := #[]
  operatorSet      : Std.HashSet String := {}
  indexedOperators : Array String := #[]
  indexedSet       : Std.HashSet String := {}
  sorts            : Array String := #[]
  sortSet          : Std.HashSet String := {}

private def FeatureCollector.addOperator
    (collector : FeatureCollector) (name : String) : FeatureCollector :=
  if collector.operatorSet.contains name then collector
  else { collector with
    operators := collector.operators.push name
    operatorSet := collector.operatorSet.insert name }

private def FeatureCollector.addIndexed
    (collector : FeatureCollector) (name : String) : FeatureCollector :=
  if collector.indexedSet.contains name then collector
  else { collector with
    indexedOperators := collector.indexedOperators.push name
    indexedSet := collector.indexedSet.insert name }

private def FeatureCollector.addSort
    (collector : FeatureCollector) (name : String) : FeatureCollector :=
  if collector.sortSet.contains name then collector
  else { collector with
    sorts := collector.sorts.push name
    sortSet := collector.sortSet.insert name }

private partial def collectSortFeature
    (sort : Sexp) (collector : FeatureCollector) : FeatureCollector :=
  match sort with
  | .atom name => collector.addSort name
  | .str _ => collector
  | .list parts =>
    match parts[0]? with
    | some (Sexp.atom "_") =>
      match parts[1]? with
      | some (Sexp.atom name) => collector.addSort name
      | _ => collector
    | some (Sexp.atom name) =>
      (parts.extract 1 parts.size).foldl
        (fun current part => collectSortFeature part current)
        (collector.addSort name)
    | _ => parts.foldl (fun current part => collectSortFeature part current) collector

private partial def collectTermFeatures
    (term : Sexp) (collector : FeatureCollector) : FeatureCollector :=
  match term with
  | .atom _ | .str _ => collector
  | .list parts =>
    match parts[0]? with
    | none => collector
    | some (Sexp.list ident) =>
      let collector :=
        if ident[0]? == some (.atom "_") then
          match ident[1]? with
          | some (Sexp.atom name) => collector.addIndexed name
          | _ => collector
        else collector
      (parts.extract 1 parts.size).foldl
        (fun current arg => collectTermFeatures arg current) collector
    | some (Sexp.atom head) =>
      if head == "!" then
        match parts[1]? with
        | some body => collectTermFeatures body collector
        | none => collector
      else if head == "forall" || head == "exists" || head == "choice" ||
          head == "lambda" then
        let collector := collector.addOperator head
        let collector :=
          match parts[1]? with
          | some (Sexp.list binders) =>
            binders.foldl (fun current binder =>
              match binder with
              | .list pair =>
                match pair[1]? with
                | some sort => collectSortFeature sort current
                | none => current
              | _ => current) collector
          | _ => collector
        match parts[2]? with
        | some body => collectTermFeatures body collector
        | none => collector
      else if head == "let" then
        let collector := collector.addOperator head
        let collector :=
          match parts[1]? with
          | some (Sexp.list bindings) =>
            bindings.foldl (fun current binding =>
              match binding with
              | .list pair =>
                match pair[1]? with
                | some value => collectTermFeatures value current
                | none => current
              | _ => current) collector
          | _ => collector
        match parts[2]? with
        | some body => collectTermFeatures body collector
        | none => collector
      else
        let collector :=
          if head == "_" || head.startsWith ":" then collector
          else collector.addOperator head
        (parts.extract 1 parts.size).foldl
          (fun current arg => collectTermFeatures arg current) collector
    | some _ =>
      parts.foldl (fun current part => collectTermFeatures part current) collector

/-- Inventory the operators, indexed operators, sorts, and rules that occur in a
parsed certificate. This is diagnostic data, not a replay allowlist. -/
def AletheProof.features (proof : AletheProof) : CertificateFeatures := Id.run do
  let mut collector : FeatureCollector := {}
  for command in proof.commands do
    match command with
    | .assume _ term =>
      collector := collectTermFeatures term collector
    | .step _ clause _ _ args _ =>
      for term in clause do
        collector := collectTermFeatures term collector
      for arg in args do
        collector := collectTermFeatures arg collector
    | .anchor _ args =>
      for arg in args do
        collector := collectTermFeatures arg collector
  return {
    operators := collector.operators
    indexedOperators := collector.indexedOperators
    sorts := collector.sorts
    rules := proof.rules
  }

end Crush.Alethe
