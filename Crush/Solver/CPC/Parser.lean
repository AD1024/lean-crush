import Crush.Solver.Replay.Certificate

/-!
CPC parsing for cvc5's explicit-conclusion output. Terms are normalized to the
shared SMT term language; rule names and arguments remain CPC names and payloads.
Each `assume-push`/`step-pop` pair becomes a scoped implication. Free proof
variables in rewrite conclusions are universally closed, never assumed inhabited.
-/

namespace Crush.CPC
open Crush.SMT

private structure ParseState where
  definitions : Std.HashMap String Sexp := {}
  variables : Array (String × Sexp) := #[]

private abbrev ParseM := StateT ParseState (Except String)

private partial def normalize (term : Sexp) (fuel : Nat := 256) : ParseM Sexp := do
  if fuel == 0 then throw "CPC term sharing exceeds the expansion limit"
  match term with
  | .atom name =>
    match (← get).definitions.get? name with
    | some value => normalize value (fuel - 1)
    | none => return term
  | .str _ => return term
  | .list parts =>
    if parts[0]? == some (Sexp.atom "@var") then
      let #[_, .str name, sort] := parts
        | throw "malformed CPC bound variable"
      let sort ← normalize sort (fuel - 1)
      if let some (_, previous) := (← get).variables.find? (·.1 == name) then
        unless previous == sort do throw "CPC variable name reused at different sorts"
      else
        modify fun s => { s with variables := s.variables.push (name, sort) }
      return .atom name
    let parts ← parts.mapM fun part => normalize part (fuel - 1)
    if parts[0]? == some (Sexp.atom "forall") || parts[0]? == some (Sexp.atom "exists") ||
        parts[0]? == some (Sexp.atom "lambda") then
      let #[head, .list binders, body] := parts
        | throw "malformed CPC binder"
      let binders ← if binders[0]? == some (Sexp.atom "@list") then
        (binders.extract 1 binders.size).mapM fun binder => do
          let .atom name := binder | throw "malformed CPC binder variable"
          let some (_, sort) := (← get).variables.find? (·.1 == name)
            | throw "unknown CPC binder variable"
          return Sexp.list #[.atom name, sort]
      else
        -- Shared definitions have already had their CPC binders normalized.
        binders.mapM fun binder => do
          let .list #[.atom _, _] := binder | throw "malformed CPC binder list"
          return binder
      return .list #[head, .list binders, body]
    if let #[.atom "@bit", index, value] := parts then
      return .list #[.list #[.atom "_", .atom "@bit_of", index], value]
    if parts[0]? == some (Sexp.atom "@from_bools") then
      return .list (#[.atom "@bbterm"] ++ parts.extract 1 parts.size)
    return Replay.stripAnnot (.list parts)

private partial def occursFree (name : String) : Sexp → Bool
  | .atom value => name == value
  | .str _ => false
  | .list parts =>
    if parts[0]? == some (Sexp.atom "forall") || parts[0]? == some (Sexp.atom "exists") ||
        parts[0]? == some (Sexp.atom "lambda") then
      match (parts[1]? : Option Sexp), (parts[2]? : Option Sexp) with
      | some (Sexp.list binders), some body =>
        if binders.any (fun b => b.list?.any (fun xs => xs[0]? == some (Sexp.atom name))) then
          false
        else occursFree name body
      | _, _ => parts.any (occursFree name)
    else parts.any (occursFree name)

private def closeVariables (term : Sexp) : ParseM Sexp := do
  let vars := (← get).variables.filter (fun (name, _) => occursFree name term)
  if vars.isEmpty then return term
  return .list #[.atom "forall", .list (vars.map fun (name, sort) =>
    .list #[.atom name, sort]), term]

/-- CPC proves formulas; top-level disjunctions become clauses for structural replay. -/
def formulaClause (term : Sexp) : Array Sexp :=
  match term with
  | .atom "false" => #[]
  | .list parts =>
    if parts[0]? == some (Sexp.atom "or") then parts.extract 1 parts.size
    else #[term]
  | _ => #[term]

private def keywords (parts : Array Sexp) : Except String (Std.HashMap String Sexp) := do
  if parts.size % 2 != 0 then throw "malformed CPC step attributes"
  let mut out := {}
  for i in [:parts.size / 2] do
    let .atom key := parts[2 * i]! | throw "malformed CPC attribute name"
    unless key.startsWith ":" do throw "malformed CPC attribute name"
    if out.contains key then throw "duplicate CPC step attribute"
    out := out.insert key parts[2 * i + 1]!
  return out

private def atomArray (term : Sexp) : Except String (Array String) := do
  let .list values := term | throw "CPC premises must be a list"
  values.mapM fun
    | .atom name => pure name
    | _ => throw "unsupported CPC parameterized proof reference"

private structure Scope where
  anchor : Nat
  assumptionId : String
  assumption : Sexp
  conclusions : Std.HashMap String Sexp

private def parseBody (body : Array Sexp) : ParseM Replay.Proof := do
  let mut commands := #[]
  let mut conclusions : Std.HashMap String Sexp := {}
  let mut scopes : Array Scope := #[]
  for command in body do
    let Sexp.list parts := command | throw "CPC command must be a list"
    let some (Sexp.atom head) := parts[0]? | throw "missing CPC command name"
    if head == "declare-const" || head == "declare-sort" ||
        head == "declare-datatypes" || head == "declare-datatype" then
      continue
    if head == "define" then
      let #[_, .atom name, .list params, value] := parts
        | throw "malformed CPC definition"
      unless params.isEmpty do throw "unsupported CPC parameterized definition"
      if (← get).definitions.contains name then throw "duplicate CPC definition"
      -- Expand available definitions before storing; recursive sharing is bounded.
      let value ← normalize value
      modify fun s => { s with definitions := s.definitions.insert name value }
      continue
    let some (Sexp.atom id) := parts[1]? | throw "missing CPC proof identifier"
    if conclusions.contains id then throw s!"duplicate CPC proof identifier `{id}`"
    if head == "assume" || head == "assume-push" then
      let #[_, _, term] := parts | throw "malformed CPC assumption"
      let term ← normalize term
      if head == "assume-push" then
        scopes := scopes.push {
          anchor := commands.size
          assumptionId := id
          assumption := term
          conclusions := conclusions }
        commands := commands.push (.anchor id #[])
      else if !scopes.isEmpty then
        throw "unscoped CPC assumption inside a subproof"
      commands := commands.push (.assume id term)
      conclusions := conclusions.insert id term
      continue
    unless head == "step" || head == "step-pop" do
      throw s!"unsupported CPC command `{head}`"
    let offset := if head == "step" then 3 else 2
    if parts.size < offset then throw "missing CPC step conclusion"
    let attrs ← keywords (parts.extract offset parts.size)
    let some (Sexp.atom rule) := attrs.get? ":rule" | throw "missing CPC rule"
    let premises ← atomArray (attrs.getD ":premises" (.list #[]))
    for premise in premises do
      unless conclusions.contains premise do
        throw s!"CPC premise `{premise}` is missing or out of scope"
    let .list args := attrs.getD ":args" (.list #[]) | throw "malformed CPC arguments"
    let args ← args.mapM normalize
    if head == "step-pop" then
      unless rule == "scope" && premises.size == 1 do
        throw "unsupported CPC scope closing rule"
      let some scope := scopes.back? | throw "CPC scope close without an assumption"
      scopes := scopes.pop
      let inner := conclusions.getD premises[0]! (.atom "false")
      let conclusion := Sexp.list #[.atom "=>", scope.assumption, inner]
      -- The closing premise need not be the last command in the block.
      let bodyId := id ++ ".body"
      if conclusions.contains bodyId then throw "CPC scope helper identifier collision"
      commands := commands.push (.step bodyId (formulaClause inner) "scope_body" premises #[])
      commands := commands.set! scope.anchor (.anchor id #[])
      commands := commands.push (.step id #[conclusion] "scope" #[] #[] #[scope.assumptionId])
      conclusions := scope.conclusions.insert id conclusion
    else
      let conclusion ← closeVariables (← normalize parts[2]!)
      commands := commands.push (.step id (formulaClause conclusion) rule premises args)
      conclusions := conclusions.insert id conclusion
  unless scopes.isEmpty do throw "unclosed CPC assumption scope"
  if commands.isEmpty then throw "empty CPC certificate"
  return { commands }

/-- Parse one CPC certificate, refusing missing conclusions and unsupported proof macros. -/
def parseProofSexps (tops : Array Sexp) : Except String Replay.Proof := do
  if let some message := Replay.proofError? tops then throw message
  for top in tops do
    if let .list body := top then
      if body.any (fun command => command.list?.any fun parts =>
          parts[0]? == some (Sexp.atom "assume") || parts[0]? == some (Sexp.atom "step")) then
        return (← (parseBody body).run {}).1
  throw "no CPC command list found"

def parseProof (text : String) : Except String Replay.Proof :=
  parseProofSexps (parseSexps text)

end Crush.CPC
