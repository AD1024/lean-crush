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

/-! ## Datatype sorts are keyed on universe levels (review round 3, S1)

`T.{0}` has at most two values and `T.{1}` at least three. Sharing one SMT sort
between them, or reading the field `Sort v` at the inductive's own parameter `v`,
refutes the two true facts below and proves `False`. -/

set_option crush.timeout 5

inductive T.{v} : Type (v+1)
  | mk : Sort v → T

theorem t0_small : ∀ a b c : T.{0}, a = b ∨ b = c ∨ a = c := by
  intro a b c
  cases a with | mk p => cases b with | mk q => cases c with | mk r =>
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp_all [T.mk.injEq]

theorem t1_big : ∃ a b c : T.{1}, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨.mk PEmpty, .mk PUnit, .mk Bool, ?_, ?_, ?_⟩
  · intro h; injection h with h; exact (h ▸ PUnit.unit : PEmpty).elim
  · intro h; injection h with h
    have : ∀ x y : PUnit, x = y := fun _ _ => rfl
    have h2 : ∀ x y : Bool, x = y := h ▸ this
    exact absurd (h2 true false) (by decide)
  · intro h; injection h with h; exact (h ▸ true : PEmpty).elim

-- The declaration's own universe is named `v`, like `T`'s parameter.
/-- error: crush: could not prove the goal -/
#guard_msgs (substring := true) in
theorem univ_same_name.{v} (_x : PUnit.{v+1}) : False := by
  have h0 := t0_small
  have h1 := t1_big
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs (substring := true) in
theorem univ_no_param : False := by
  have h0 := t0_small
  have h1 := t1_big
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs (substring := true) in
set_option crush.trust "reconstructOrTrust" in
theorem univ_fallback.{v} (_x : PUnit.{v+1}) : False := by
  have h0 := t0_small
  have h1 := t1_big
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs (substring := true) in
set_option crush.trust "reconstruct" in
theorem univ_reconstruct.{v} (_x : PUnit.{v+1}) : False := by
  have h0 := t0_small
  have h1 := t1_big
  crush

-- The emitted script declares one datatype per universe instantiation of `T`.
run_meta do
  let facts : Array Fact := #[
    { prop := ← inferType (mkConst ``t0_small), proof := some (mkConst ``t0_small),
      descr := "t0_small" },
    { prop := ← inferType (mkConst ``t1_big), proof := some (mkConst ``t1_big),
      descr := "t1_big" }]
  let (script, _) ← buildScript { backend := .none } facts
  let datatypes := script.filterMap fun
    | .declDatatypes decls => some (decls.map (·.1))
    | _ => none
  let tSorts := datatypes.flatten.filter (·.startsWith "T")
  unless tSorts.size == 2 do
    throwError "expected two datatypes for `T`, got {tSorts}"

-- Goals over datatypes at higher universes still prove.
example (a b : Option Type) (h : a = b) : b = a := by crush
example (a : Type) (o : Option Type) (h : o = some a) : o ≠ none := by crush
example (xs : List Type) (x : Type) (h : xs = [x]) : xs ≠ [] := by crush
theorem poly_option (a b : Option (Sort u)) (x : Sort u) (h : a = some x) (h2 : b = a) :
    b ≠ none := by crush
set_option crush.trust "reconstruct" in
example (a b : Option Type) (h : a = b) : b = a := by crush

-- A universe parameter that is not the caller's is rejected in trusted dependencies.
run_meta do
  let foreign := mkConst ``PUnit.unit [.param `notACallerUniverse]
  let failed ← try
    checkDependencyLevelParams (some [`u]) "test dependency" foreign
    pure false
  catch _ => pure true
  unless failed do throwError "a foreign universe parameter was accepted"
  checkDependencyLevelParams (some [`notACallerUniverse]) "test dependency" foreign
  checkDependencyLevelParams none "test dependency" foreign

end SoundnessUniverses
