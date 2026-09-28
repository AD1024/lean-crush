import Crush.SMT.Sexp

/-! Shared certificate commands and diagnostic inventories. Parsing never establishes
validity: the replay engine must construct a Lean proof for every used conclusion. -/

namespace Crush.Replay
open Crush.SMT

/-- One command in a normalized certificate. Terms are kept as `Sexp` — the replay layer, not
the parser, is what eventually interprets them. -/
inductive Command where
  /-- `(assume id term)`. -/
  | assume (id : String) (term : Sexp)
  /-- `(step id (cl …) :rule R :premises (…) :args (…) :discharge (…))`. `clause` is the
  list of disjunct terms (empty ⇒ the empty clause, i.e. `false`).

  `discharge` names the local assumptions a scope-closing step releases; it is what makes a
  subproof's conclusion an implication rather than a claim under an open hypothesis, so
  replay needs it (an ignored `:discharge` would silently drop the antecedent). -/
  | step (id : String) (clause : Array Sexp) (rule : String)
         (premises : Array String) (args : Array Sexp)
         (discharge : Array String := #[])
  /-- `(anchor :step id …)` — opens a subproof closed by a step with the same id. -/
  | anchor (id : String) (args : Array Sexp)
  deriving Inhabited, Repr

/-- A parsed certificate proof: the commands in order. The last `step` derives the empty
clause; `emptyClauseStep?` finds it. -/
structure Proof where
  commands : Array Command
  /-- CPC assumption ids mapped to assertion provenance names. -/
  factAliases : Std.HashMap String String := {}
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

/-- Find cvc5's explanation for refusing to serialize a proof in the requested format. -/
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

/-- The `step` deriving the empty clause `(cl)`, if present — the proof's conclusion.
Its existence is a cheap structural sanity check that a proof actually refutes. -/
def Proof.emptyClauseStep? (p : Proof) : Option Command :=
  p.commands.find? fun
    | .step _ clause _ _ _ => clause.isEmpty
    | _ => false

/-- Count of each command kind, for diagnostics: `(assumes, steps, anchors)`. -/
def Proof.stats (p : Proof) : Nat × Nat × Nat := Id.run do
  let mut a := 0; let mut s := 0; let mut n := 0
  for c in p.commands do
    match c with
    | .assume .. => a := a + 1
    | .step .. => s := s + 1
    | .anchor .. => n := n + 1
  return (a, s, n)

/-- The distinct rule names used by the proof's steps, for diagnostics and for
deciding whether a replay can handle the proof (an unknown rule ⇒ cannot replay). -/
def Proof.rules (p : Proof) : Array String := Id.run do
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
def Proof.features (proof : Proof) : CertificateFeatures := Id.run do
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

end Crush.Replay
