import Lean

/-!
# Extensible proof-reconstruction lemmas

`@[crush_reconstruct]` registers domain lemmas used only while rebuilding an SMT
`unsat` verdict as a checked Lean proof. The lemmas are not sent to the solver and
do not affect tactics outside `crush`.
-/

open Lean Meta Elab

namespace Crush

private abbrev ReconstructionKey := Array DiscrTree.Key

private structure ReconstructionIndex where
  rules : Array Name := #[]
  tree : DiscrTree Name := {}
  deriving Inhabited

private def ReconstructionIndex.insert (index : ReconstructionIndex)
    (entry : ReconstructionKey × Name) : ReconstructionIndex :=
  if index.rules.contains entry.2 then
    index
  else
    { rules := index.rules.push entry.2
      tree := index.tree.insertKeyValue entry.1 entry.2 }

initialize crushReconstructLemmaExt :
    SimplePersistentEnvExtension (ReconstructionKey × Name) ReconstructionIndex ←
  registerSimplePersistentEnvExtension {
    addEntryFn := ReconstructionIndex.insert
    addImportedFn := fun arrays =>
      arrays.foldl (init := {}) fun index entries =>
        entries.foldl (init := index) ReconstructionIndex.insert
  }

/-- Register a theorem as a reconstruction-only proof-search rule.

This is the domain extension point for facts such as monotonicity of a user-defined
ordered datatype. Registered theorems are supplied to bounded backward proof search;
every resulting proof is still checked by Lean's kernel. -/
syntax (name := crushReconstructAttr) "crush_reconstruct" : attr

initialize registerBuiltinAttribute {
  name := `crushReconstructAttr
  descr := "Register a theorem for lean-crush proof reconstruction."
  applicationTime := .afterTypeChecking
  add := fun declName _ _ => do
    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration {declName}"
    let key ← MetaM.run' do
      unless ← isProp info.type do
        throwError "@[crush_reconstruct] expects a theorem, but {declName} has type\
          {indentExpr info.type}"
      let (_, _, conclusion) ← forallMetaTelescope info.type
      DiscrTree.mkPath conclusion
    modifyEnv fun env => crushReconstructLemmaExt.addEntry env (key, declName)
}

/-- Registered reconstruction lemmas in deterministic import order. -/
def reconstructionLemmas : CoreM (Array Name) := do
  return (crushReconstructLemmaExt.getState (← getEnv)).rules

/-- Registered rules whose conclusions structurally match `target`.

The discrimination tree treats theorem parameters as wildcards while retaining constants,
applications, constructors, and projections from the conclusion. Thus rules over a shared
outer relation such as `LE.le` are still separated by their operand structure and datatype. -/
def reconstructionLemmasFor (target : Expr) : MetaM (Array Name) := do
  (crushReconstructLemmaExt.getState (← getEnv)).tree.getMatch target

end Crush
