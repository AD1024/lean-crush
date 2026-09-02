import Crush.Metatheory.Reification.Witness
import Crush.Metatheory.SMT.Guarded
import Crush.Metatheory.SMT.Soundness

/-!
# Verified command generation

After Lean expressions have been reified as a finite higher-order theory, this
module translates that entire theory to first-order form and constructs its SMT
commands. The accompanying theorem states that the generated commands impose
exactly the translated first-order formulas. This pure function is the
proof-facing specification used when checking the complete emitted command sequence.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened
open SMT.Datatype
open scoped Crush.Metatheory Crush.SMT

/-- Exact concrete commands for a finite reified higher-order theory translated
against one common signature. -/
def theoryCommands {signature : Signature}
    (encoding : SMT.Encoding (Symbol signature))
    (source : Theory signature) : Array Crush.SMT.Command :=
  SMT.encodeTheories encoding source

/-- The finite-theory VCG represents the combined flattened target theory. -/
theorem theoryCommands_represents {signature : Signature}
    (encoding : SMT.Encoding (Symbol signature))
    (source : Theory signature) :
    SMT.TheoryRepr encoding (translatedTheories source)
      (theoryCommands encoding source) :=
  SMT.encode_theories encoding source

/-- Exact guarded commands for a finite reified higher-order theory. -/
def guardedTheoryCommands {signature : Signature}
    (guarding : SMT.GuardedEncoding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Theory signature) :
    Array Crush.SMT.Command :=
  guarding.theory derived (SMT.translatedDecls source)
    (translatedTheories source)

/-- Guarded finite-theory generation retains exact declarations and assertions
in source traversal order. -/
theorem guardedTheoryCommands_represents {signature : Signature}
    (guarding : SMT.GuardedEncoding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Theory signature) :
    SMT.GuardedTheoryRepr guarding derived (translatedTheories source)
      (guardedTheoryCommands guarding derived source) :=
  ⟨SMT.translatedDecls source, Crush.SMT.SameCommandSet.refl _⟩

/-- Absence of a model in the internal relational semantics reflects through
the pure finite-theory encoder. The translator-facing theorem in
`CommandEquiv` additionally requires the modeled SMT theory semantics. -/
theorem theoryCommands_unsat_implies_source_unsat {signature : Signature}
    (encoding : SMT.Encoding (Symbol signature))
    (source : Theory signature)
    (data : Reification.DatatypeSignaturePrefix signature)
    (native : EnvRepr encoding data.toModelEnv)
    (unsat : Crush.SMT.RawCommandsUnsat
      (theoryCommands encoding source)) :
    Datatype.Env.TheoryUnsatisfiable data.toModelEnv source := by
  exact SMT.commands_unsat_implies_source_theory_unsat encoding native source
    (theoryCommands_represents encoding source) unsat

end Crush.Metatheory.VCG
