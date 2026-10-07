import Crush

open Lean Meta Elab Tactic Crush

-- Exercise only the manual finisher: without any general finishers, a successful
-- result witnesses that its reference to the selected premise was resolved.
run_meta do
  withLocalDeclD `P (mkSort Level.zero) fun p => do
    withLocalDeclD `namedPremise p fun h => do
      let target := mkApp2 (mkConst ``And) p p
      let goal ← mkFreshExprMVar target
      let name := mkIdent `namedPremise
      let finisher ← `(tactic| exact And.intro $name $name)
      discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
        unless ← tryReconstruct goal.mvarId! #[h] #[] (some finisher) do
          throwError "manual finisher could not refer to its named premise"

-- The visible declaration keeps its name even if the solver returns an older,
-- shadowed declaration later in the unsat core.
run_meta do
  withLocalDeclD `P (mkSort Level.zero) fun p => do
    withLocalDeclD `Q (mkSort Level.zero) fun q => do
      withLocalDeclD `sharedName p fun old => do
        withLocalDeclD `sharedName q fun visible => do
          let target := mkApp2 (mkConst ``And) p q
          let goal ← mkFreshExprMVar target
          let name := mkIdent `sharedName
          let finisher ← `(tactic| exact And.intro (by assumption) $name)
          discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
            unless ← tryReconstruct goal.mvarId! #[visible, old] #[] (some finisher) do
              throwError "a shadowed premise hid the visible premise's name"

-- Preserving names must not expose hypotheses omitted from the selected core.
run_meta do
  withLocalDeclD `P (mkSort Level.zero) fun p => do
    withLocalDeclD `excludedPremise p fun _ => do
      let goal ← mkFreshExprMVar p
      let name := mkIdent `excludedPremise
      let finisher ← `(tactic| exact $name)
      discard <| Term.TermElabM.run' <| Tactic.run goal.mvarId! do
        if ← tryReconstruct goal.mvarId! #[] #[] (some finisher) then
          throwError "manual finisher accessed a hypothesis outside the selected core"
        if ← goal.mvarId!.isAssigned then
          throwError "failed named finisher left the original goal assigned"

-- End-to-end syntax uses the same isolated, named core context.
set_option crush.trust "reconstruct" in
example (p q : Prop) (namedPremise : p ∧ q) : q ∧ p := by
  crush using (exact And.intro namedPremise.right namedPremise.left)
