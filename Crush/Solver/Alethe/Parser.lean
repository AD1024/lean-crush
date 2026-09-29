import Crush.Solver.Replay.Certificate

namespace Crush.Alethe
open Crush.SMT
export Crush.Replay (Command stripAnnot proofError? CertificateFeatures)
abbrev AletheProof := Crush.Replay.Proof

namespace AletheProof
abbrev emptyClauseStep? (proof : AletheProof) : Option Command :=
  Crush.Replay.Proof.emptyClauseStep? proof
abbrev stats (proof : AletheProof) : Nat × Nat × Nat := Crush.Replay.Proof.stats proof
abbrev rules (proof : AletheProof) : Array String := Crush.Replay.Proof.rules proof
abbrev features (proof : AletheProof) : CertificateFeatures := Crush.Replay.Proof.features proof
end AletheProof

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

end Crush.Alethe
