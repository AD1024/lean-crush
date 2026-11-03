import Crush

/-!
Manual finishers must resolve selected premises by their visible names, including
when an older declaration has been shadowed. Their isolated context must exclude
unselected hypotheses. Direct API checks disable fallback finishers so success
requires the named reference to resolve.
-/

open Lean Meta Elab Tactic Crush

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

-- Return the visible premise before its shadowed predecessor in the core.
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

-- An ambient premise omitted from the core stays inaccessible.
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

-- Exercise the tactic syntax as well as the direct API.
set_option crush.trust "reconstruct" in
example (p q : Prop) (namedPremise : p ∧ q) : q ∧ p := by
  crush using (exact And.intro namedPremise.right namedPremise.left)
