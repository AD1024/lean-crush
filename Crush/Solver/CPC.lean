import Crush.Solver.CPC.Parser
import Crush.Solver.CPC.ReplayRules
import Crush.Solver.Replay.Engine
import Crush.SMT.Print

namespace Crush.CPC
open Crush.SMT

/-- Link CPC's private assumption ids to named source assertions. Unmatched
assumptions still require independent Lean proofs in the shared replay engine. -/
def withFactAliases (proof : Replay.Proof) (commands : Array SMT.Command) : Replay.Proof := Id.run do
  let mut aliases := {}
  let mut assertions : Array (Sexp × String) := #[]
  for command in commands do
    if let .assert (.annot term attrs) := command then
      for attr in attrs do
        if let .named name := attr then
          if let some sexp := (parseSexps (termToString [] term))[0]? then
            assertions := assertions.push (Replay.stripAnnot sexp, name)
  for command in proof.commands do
    if let .assume id term := command then
      if let some (_, name) := assertions.find? (fun (assertion, _) => assertion == term) then
        aliases := aliases.insert id name
  return { proof with factAliases := aliases }

end Crush.CPC
