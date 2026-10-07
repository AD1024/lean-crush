import Crush

/-! Possibly empty carriers must not create Lean inhabitants. -/
set_option linter.unusedVariables false
set_option crush.timeout 2

example (α : Type) : True := by
  fail_if_success have : ∃ x : α, x = x := by crush
  trivial

structure SoundnessEmptyStruct where
  e : Empty
  n : Int

example : True := by
  have h : ∀ s : SoundnessEmptyStruct, s.n ≠ s.n := fun s => s.e.elim
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : ∀ s : Empty × Int, s.2 ≠ s.2 := fun s => s.1.elim
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : ∀ s : Int → Empty, s ≠ s := fun s => (s 0).elim
  fail_if_success have : False := by crush
  trivial

inductive SoundnessNoBase where
  | mk : SoundnessNoBase → Int → SoundnessNoBase

example : True := by
  have h : ∀ s : SoundnessNoBase, s ≠ s := fun s => by
    induction s with
    | mk t n ih => exact (ih rfl).elim
  fail_if_success have : False := by crush
  trivial

-- Hypothetical binders and constructor fields are not inhabitation evidence.
example : True := by
  fail_if_success have : ∃ x : Empty, x = x := by crush
  fail_if_success have : ∃ x : Option Empty, x ≠ none := by crush
  fail_if_success have : ∃ f : Int → Empty, f = f := by crush
  trivial

-- Padding must retain useful reasoning about actual values.
example (α : Type) (x : α) : ∃ y : α, y = x := by crush
example (x : Option Empty) : x = none := by crush
example (x : Nat) (f : Nat → Nat) : f x ≥ 0 := by crush
example (x : Array Empty) : x.size = 0 := by crush

-- Alethe must decode validity guards back over actual Lean values, including
-- datatype guards introduced because a type parameter may be empty.
open Lean Meta Elab Tactic Crush in
elab "replay_carrier_assumption " source:term : tactic => withMainContext do
  let source ← elabTerm source none
  let goal ← getMainGoal
  let target ← goal.getType
  let ((positive, negative), state) ← TranslateM.run {} do
    let positive ← emitTerm (← inferType source)
    let negative ← emitTerm (mkNot target)
    return (positive, negative)
  let certificate := s!"unsat ((assume source {positive}) (assume negated {negative}) \
    (step done (cl) :rule resolution :premises (source negated)))"
  let some parsed := Alethe.parseProof certificate | throwError "bad carrier test certificate"
  let snapshot ← KernelCheckSnapshot.capture
  let implication ← withLocalDeclD `negated (mkNot target) fun negated => do
    let facts := ({} : Std.HashMap String Expr)
      |>.insert "source" source |>.insert "negated" negated
    match ← Alethe.replay parsed (SMT.parseSexps certificate) facts state.nameToExpr with
    | .ok proof => mkLambdaFVars #[negated] proof
    | .error failure => throwError "carrier assumption replay failed: {failure.toMessageData}"
  let proof ← mkAppOptM ``Classical.byContradiction #[some target, some implication]
  goal.assign (← kernelCheckProof snapshot target proof)
  replaceMainGoal []

example {α : Type} (p : List α → Prop) (h : ∃ xs : List α, p xs) :
    ∃ xs : List α, p xs := by
  replay_carrier_assumption h

example {α : Type} (p : α → Prop) (h : ∀ xs : List α, ∀ x : α, x ∈ xs → p x) :
    ∀ xs : List α, ∀ x : α, x ∈ xs → p x := by
  replay_carrier_assumption h
