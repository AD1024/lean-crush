import Crush

/-!
Proof irrelevance may erase proof-valued subterms and justify proof equality.
Hypothetical proofs must never become unconditional inhabitants of padded SMT
carriers, and direct translation of a proof as an ordinary value must be refused.
-/

set_option linter.unusedVariables false
set_option crush.timeout 2

example : True := by
  have h : ∀ h : False, h = h := fun _ => rfl
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : ¬ ∃ h : False, h = h := fun ⟨h, _⟩ => h
  fail_if_success have : False := by crush
  fail_if_success have : ∃ h : False, h = h := by crush
  trivial

-- False elimination inside proof equality must remain erased.
example : True := by
  have h : ∀ h : False, (False.elim h : True) = True.intro := fun _ => rfl
  fail_if_success have : False := by crush
  trivial

example : ∃ h : True, h = True.intro := by crush
example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := by crush
example (p : Prop) (h₁ h₂ : p → p) : h₁ = h₂ := by crush
example (p : Prop) (f : p → Int) (h₁ h₂ : p) : f h₁ = f h₂ := by crush

-- Exercise direct proof-value translation outside structural proof irrelevance.
open Lean Meta Crush in
run_meta do
  let accepted ← try
    discard <| TranslateM.run {} (emitTerm (mkConst ``True.intro))
    pure true
  catch _ => pure false
  if accepted then throwError "translation accepted a proof as an ordinary SMT value"
