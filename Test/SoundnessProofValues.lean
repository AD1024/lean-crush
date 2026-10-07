import Crush

set_option linter.unusedVariables false
set_option crush.timeout 2

-- A hypothetical proof must not create an unconditional inhabitant of False's
-- padded SMT carrier while the proposition containing it is translated.
example : True := by
  have h : ∀ h : False, h = h := fun _ => rfl
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : ¬ ∃ h : False, h = h := fun ⟨h, _⟩ => h
  fail_if_success have : False := by crush
  fail_if_success have : ∃ h : False, h = h := by crush
  trivial

-- Proof-producing subterms also disappear through proof irrelevance, without
-- translating a False eliminator as an ordinary data-valued application.
example : True := by
  have h : ∀ h : False, (False.elim h : True) = True.intro := fun _ => rfl
  fail_if_success have : False := by crush
  trivial

example : ∃ h : True, h = True.intro := by crush
example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := by crush
example (p : Prop) (h₁ h₂ : p → p) : h₁ = h₂ := by crush
example (p : Prop) (f : p → Int) (h₁ h₂ : p) : f h₁ = f h₂ := by crush

-- Outside a proof-irrelevance-aware structural operation, actual proofs have no
-- SMT value representation and must be refused instead of asserting validity.
open Lean Meta Crush in
run_meta do
  let accepted ← try
    discard <| TranslateM.run {} (emitTerm (mkConst ``True.intro))
    pure true
  catch _ => pure false
  if accepted then throwError "translation accepted a proof as an ordinary SMT value"
