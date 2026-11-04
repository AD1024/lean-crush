import Crush

/-!
Translation may resolve unused universes in copied lemma instances, but must not
assign the caller's goal or hypothesis universes. Retained provenance shares the
copy's universe choices, including when translation later refuses a fact.
-/

open Lean Meta Crush

namespace SoundnessUniverses

example : True := by
  have h : ∀ (α : Sort _) (x : α), x = x := by crush
  have := h Nat 0
  trivial

example : True := by
  have h : ∀ (α : Sort _) (x : α), x = x := by crush
  have := h (Type 1) (Type 0)
  trivial

example : True := by
  have h : ∀ (α : Sort _) (x y z : α), x = y ∧ y = z → x = z := by crush
  have := h Nat 0 0 0 ⟨rfl, rfl⟩
  trivial

private def checkUnassigned (level : Level) : MetaM Unit := do
  if ← isLevelMVarAssigned level.mvarId! then
    throwError "translation assigned an original universe metavariable"

universe u
theorem unusedUniverse : (PUnit.{u+1} = PUnit.{u+1}) := rfl

run_meta do
  let level ← mkFreshLevelMVar
  let proof := mkConst ``unusedUniverse [level]
  let prop ← inferType proof
  let (_, state) ← buildScript {} #[{
    prop, proof := some proof, descr := "unused lemma universe"
    negationTransform := some proof, reconstructionProof := some proof
    instanceOf := some proof }]
  checkUnassigned level
  unless state.facts.size == 1 do
    throwError "unused lemma universe prevented fact translation"
  let fact := state.facts[0]!
  for expression in #[fact.prop, fact.proof, fact.negationTransform,
      fact.reconstructionProof, fact.instanceOf] do
    let some expression := expression | throwError "lost fact provenance"
    if expression.hasLevelMVar then
      throwError "a copied lemma retained an unresolved universe"
  unless ← isDefEqRigid (← inferType fact.proof.get!) fact.prop.get! do
    throwError "copied proposition and proof chose different universes"

run_meta do
  let level ← mkFreshLevelMVar
  withLocalDeclD `α (mkSort level) fun α => do
    withLocalDeclD `x α fun x => do
      let prop ← mkEq x x
      let (_, state) ← buildScript {} #[{
        prop, proof := some (← mkEqRefl x), descr := "polymorphic context" }]
      unless state.facts[0]!.prop == some prop do
        throwError "translation specialized a hypothesis universe"
      checkUnassigned level
      let negative : Fact := {
        prop := mkNot prop, proof := none, descr := "negated goal", negated := true }
      discard <| buildScript {} #[negative]
      checkUnassigned level
      checkDependencyUniverses (← mkEqRefl x)
      checkUnassigned level
      -- A failing negated goal must not commit universe choices either.
      let unsupported ← mkForallFVars #[α, x] prop
      let failed ← try
        discard <| buildScript {} #[{ negative with prop := mkNot unsupported }]
        pure false
      catch _ => pure true
      unless failed do throwError "accepted a type-dependent quantified sort"
      checkUnassigned level

-- This proof becomes well-typed only by solving the caller's level to one.
run_meta do
  let level ← mkFreshLevelMVar
  let proof := mkApp2 (mkConst ``Eq.refl [level]) (mkConst ``Nat) (mkNatLit 0)
  let failed ← try
    checkDependencyUniverses proof
    pure false
  catch _ => pure true
  unless failed do throwError "dependency validation solved a universe constraint"
  checkUnassigned level

end SoundnessUniverses
