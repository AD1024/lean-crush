import Crush.Metatheory.VCG.Trust
import Crush.Metatheory.SMT.Soundness

/-!
# Proved and trusted whole-translation results

The proved constructor retains the exact representation theorem needed to move
from concrete SMT commands back to the intrinsic flattened theory.  Trusted
results retain their operational output and reasons, but deliberately expose no
semantic representation witness.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened

/-- Semantic classification of a completed Lean-to-SMT translation. -/
inductive TranslationStatus {signature : Signature}
    (encoding : SMT.Encoding (Symbol signature)) where
  | proved (source : Sentence signature) (commands : Array Crush.SMT.Command)
      (representation :
        SMT.TheoryRepresentation encoding (translatedTheory source) commands)
  | trusted (commands : Array Crush.SMT.Command)
      (reasons : Array TrustReason) (nonempty : ¬reasons.isEmpty)

namespace TranslationStatus

/-- Concrete commands retained by either translation branch. -/
def commands {signature : Signature} {encoding : SMT.Encoding (Symbol signature)} :
    TranslationStatus encoding → Array Crush.SMT.Command
  | .proved _ commands _ => commands
  | .trusted commands _ _ => commands

/-- A status proves the translation of this particular intrinsic source. -/
def Proves {signature : Signature} {encoding : SMT.Encoding (Symbol signature)}
    (status : TranslationStatus encoding) (source : Sentence signature) : Prop :=
  ∃ (commands : Array Crush.SMT.Command)
      (representation :
        SMT.TheoryRepresentation encoding (translatedTheory source) commands),
    status = .proved source commands representation

/-- Unsatisfiability of the exact commands in a proved status reflects to its
intrinsic source sentence.  No corresponding theorem is available for the
trusted constructor. -/
theorem unsat_source {signature : Signature}
    {encoding : SMT.Encoding (Symbol signature)}
    (status : TranslationStatus encoding) {source : Sentence signature}
    (proved : status.Proves source)
    (unsat : Crush.SMT.CommandsUnsatisfiable status.commands) :
    Unsatisfiable source := by
  rcases proved with ⟨commands, representation, rfl⟩
  exact target_unsat_implies_source_unsat source
    (SMT.commands_unsat_implies_theory_unsat encoding representation unsat)

end TranslationStatus

end Crush.Metatheory.VCG
