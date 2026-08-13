import Crush

/-!
Regression tests for the reconstruction gaps exposed by Velvet's root examples.

The arithmetic cases use `Nat`, but the mechanisms under test are not Nat-specific:
registered domain lemmas feed a generic reconstruction pass, datatype splitting considers
all inductives, and existential witnesses are synthesized from constructors. The tests
below also cover `Int`, a downstream recursive datatype, a parameterized datatype,
`Option`, and an indexed family.
-/

open Crush

set_option crush.timeout 10
set_option crush.trust "reconstruct"
set_option crush.reconstruct "core"

section RootVCs

theorem squareInvariantStep (x i : Nat)
    (invariant : ∀ j < i, j * j ≤ x) (current : i * i ≤ x) :
    ∀ j < i + 1, j * j ≤ x := by
  crush

theorem cubeInvariantStep (x i : Nat)
    (invariant : ∀ j < i, j * j * j ≤ x) (current : i * i * i ≤ x) :
    ∀ j < i + 1, j * j * j ≤ x := by
  crush

theorem squarePredecessorProjection (x i : Nat)
    (invariant : ∀ j < i, j * j ≤ x) :
    ∀ j ≤ i - 1, j * j ≤ x := by
  crush

theorem cubePredecessorEndpoint (x i : Nat)
    (invariant : ∀ j < i, j * j * j ≤ x) :
    (i - 1) * (i - 1) * (i - 1) ≤ x := by
  crush

theorem squareMaximality (x i : Nat) (done : x < i * i) :
    ∀ j, j * j ≤ x → j ≤ i - 1 := by
  crush

theorem cubeMaximality (x i : Nat) (done : x < i * i * i) :
    ∀ j, j * j * j ≤ x → j ≤ i - 1 := by
  crush

theorem squareDecreases (x i : Nat) (current : i * i ≤ x) :
    x + 8 - (i + 1) < x + 8 - i := by
  crush

theorem cubeDecreases (x i : Nat) (current : i * i * i ≤ x) :
    x + 8 - (i + 1) < x + 8 - i := by
  crush

theorem squareInterval (x m : Nat) (endpoint : m * m ≤ x) :
    ∀ i ≤ m, i * i ≤ x := by
  crush

theorem squareClosedIntervalMax (x lower upper value : Nat)
    (upperBound : x < upper * upper)
    (done : ¬1 < upper - lower)
    (valueBound : value * value ≤ x) :
    value ≤ lower := by
  crush

theorem squareClosedIntervalMaxAliased (x lower upper output upperOutput value : Nat)
    (upperBound : x < upper * upper)
    (done : ¬1 < upper - lower)
    (state : lower = output ∧ upper = upperOutput)
    (valueBound : value * value ≤ x) :
    value ≤ output := by
  crush

-- The broad gap rule also matches this conclusion shape, but its hidden upper bound has no
-- contextual anchor. Reconstruction must reject that rule before invoking expensive tactics.
theorem unanchoredRuleDeclinesQuickly (n : Nat) (h : n = 0) : n ≤ 0 := by
  crush

theorem unboundedNatWitness (n : Nat) : ∃ m, m > n + 200 := by
  crush

@[crush_reconstruct]
theorem intHasLargerWitness (x : Int) : ∃ y, x < y := by
  exact ⟨x + 1, by omega⟩

-- Algebraic SMT sorts do not have useful successor constructors. A downstream
-- reconstruction rule can provide the domain operation without changing the engine.
theorem unboundedIntWitness (x : Int) : ∃ y, x < y := by
  crush

-- This should be closed before translation, not sent to a nonlinear quantified query.
theorem selectedIdentity (x i : Nat) (invariant : ∀ j < i, j * j * j ≤ x) :
    ∀ j < i, j * j * j ≤ x := by
  crush

private theorem selectedStateBridge {α : Type} (left middle right : α)
    (state : left = middle ∧ middle = right) : left = right := by
  exact state.1.trans state.2

-- Velvet's generated root proof applies a selected `goalN` theorem and discharges
-- its premises from the VC context. Crush should perform that bounded backward step
-- before translating the helper theorem and its unrelated quantified parameters.
theorem selectedHelperApplication {α : Type} (left middle right : α)
    (state : left = middle ∧ middle = right) : left = right := by
  crush [selectedStateBridge, state]

theorem packedStatePrefix (arr output : Array Int) (bound outputBound : Nat)
    (invariant : ∀ i j, i < j → j ≤ bound - 1 → arr[i]! ≤ arr[j]!)
    (done : bound = arr.size)
    (state : (arr, bound) = (output, outputBound)) :
    ∀ i j, i ≤ j → j < output.size → output[i]! ≤ output[j]! := by
  crush

end RootVCs

section GenericDatatype

inductive Stage where
  | base
  | next (previous : Stage)
  deriving DecidableEq

axiom Advances : Stage → Stage → Prop
axiom advancesNext (stage : Stage) : Advances stage (.next stage)

theorem stageExhaustive (stage : Stage) :
    stage = .base ∨ ∃ previous, stage = .next previous := by
  crush

-- The target contains `stage`, but not the required witness `Stage.next stage`.
-- Constructor closure must create it before the selected axiom can finish the body.
theorem stageWitness (stage : Stage) : ∃ later, Advances stage later := by
  crush [advancesNext]

inductive Payload (α : Type) where
  | empty
  | value (contents : α)

theorem payloadExhaustive {α : Type} (payload : Payload α) :
    payload = .empty ∨ ∃ contents, payload = .value contents := by
  crush

theorem optionWitness {α : Type} (value : α) :
    ∃ result : Option α, result = some value := by
  crush

inductive Tagged : Bool → Type where
  | off : Tagged false
  | on (value : Nat) : Tagged true

-- Exercise reconstruction directly: the SMT datatype encoding currently erases indices,
-- which is a separate translation limitation and cannot establish this goal as `unsat`.
theorem indexedDatatypeExhaustive (tagged : Tagged true) :
    ∃ value, tagged = .on value := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    unless ← tryReconstruct goal #[] (← finisherTactics) do
      throwError "generic reconstruction did not split an indexed datatype"

@[crush_reconstruct]
theorem stageReconstructionRule (stage : Stage) : Advances stage (.next stage) :=
  advancesNext stage

axiom Ready : Stage → Prop
axiom Active : Stage → Prop
axiom Complete : Stage → Prop

@[crush_reconstruct]
axiom activeOfReady {stage : Stage} : Ready stage → Active stage

@[crush_reconstruct]
axiom completeOfActive {stage : Stage} : Active stage → Complete stage

run_meta do
  unless (← reconstructionLemmas).contains ``stageReconstructionRule do
    throwError "@[crush_reconstruct] did not register the downstream theorem"
  let finishers ← finisherTactics
  Lean.Meta.withLocalDeclD `stage (Lean.mkConst ``Stage) fun stage =>
    Lean.Meta.withLocalDeclD `ready (Lean.mkApp (Lean.mkConst ``Ready) stage) fun ready => do
      let completeTarget := Lean.mkApp (Lean.mkConst ``Complete) stage
      let candidates ← reconstructionLemmasFor completeTarget
      unless candidates.contains ``completeOfActive do
        throwError "the reconstruction index omitted a matching downstream rule"
      if candidates.contains ``natCubeDown || candidates.contains ``natSquareDown then
        throwError "the reconstruction index returned unrelated Nat rules"
      let goal ← Lean.Meta.mkFreshExprMVar (Lean.mkApp (Lean.mkConst ``Complete) stage)
      let reconstructed ← IO.mkRef false
      discard <| Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Tactic.run goal.mvarId! do
        reconstructed.set (← tryReconstruct goal.mvarId! #[ready] finishers)
      unless ← reconstructed.get do
        throwError "registered reconstruction rules did not close a downstream rule chain"
      let proof ← Lean.instantiateMVars (Lean.mkMVar goal.mvarId!)
      if proof.hasSorry || proof.hasMVar then
        throwError "registered reconstruction rule chain produced an incomplete proof"

end GenericDatatype
