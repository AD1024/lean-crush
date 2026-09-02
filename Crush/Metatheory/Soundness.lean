import Crush.Metatheory.Defunctionalization.Theory

/-!
# Soundness of higher-order defunctionalization

This module exposes the semantic consequence of the model-extension theorem:
unsatisfiability of the complete generated first-order theory reflects to the
higher-order source. It is deliberately independent of Lean-expression
reification, custom datatype semantics, SMT command semantics, and solver
certificates.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature}

/-- Unsatisfiability of the translated first-order theory reflects to its
higher-order source sentence. -/
theorem target_unsat_implies_source_unsat (formula : Sentence signature)
    (targetUnsat : FO.FamilyTheoryUnsatisfiable (translatedTheory formula)) :
    Unsatisfiable formula := by
  intro model sourceValid
  exact targetUnsat (canonicalModel model)
    (model_extension model formula sourceValid)

/-- Unsatisfiability of the combined translated first-order theory reflects to
the complete higher-order source theory. -/
theorem target_theories_unsat_implies_source_unsat
    (theory : Theory signature)
    (targetUnsat : FO.FamilyTheoryUnsatisfiable (translatedTheories theory)) :
    TheoryUnsatisfiable theory := by
  intro model sourceValid
  exact targetUnsat (canonicalModel model)
    (model_extension_theory model theory sourceValid)

end Crush.Metatheory.Defunctionalization
