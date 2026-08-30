import Crush.Metatheory.VCG.Soundness

/-!
# Live production agreement

This module is the refinement boundary for a completed direct production run.
The unrestricted `emitTerm` implementation is not proved correct merely by
entering this module. Instead, `ProductionAgreement` can be constructed only
when the final command snapshot, after erasing semantically transparent
top-level assertion attributes, is exactly the guarded intrinsic encoding of
the exact reified fact retained by `CertifiedDataEnv`.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened Reification

/-- Erase a top-level assertion annotation. Production adds `:named` at this
position for unsat-core provenance; the attribute does not change the formula's
raw semantics. Nested annotations are part of the represented term and remain
untouched. -/
def stripAssertionAnnotation : Crush.SMT.Command → Crush.SMT.Command
  | .assert (.annot body _) => .assert body
  | command => command

/-- Top-level assertion attributes are semantically transparent. -/
@[simp] theorem satisfiesCommand_stripAssertionAnnotation
    (model : Crush.SMT.Model) (command : Crush.SMT.Command) :
    model.SatisfiesCommand (stripAssertionAnnotation command) ↔
      model.SatisfiesCommand command := by
  cases command with
  | assert formula =>
      cases formula with
      | annot body attributes =>
          constructor
          · rintro ⟨_, evaluated⟩
            exact ⟨trivial, .annot evaluated⟩
          · rintro ⟨_, evaluated⟩
            cases evaluated with
            | annot bodyEval => exact ⟨trivial, bodyEval⟩
      | lit | bvar | app | letE | forallE | existsE | lam => rfl
  | setLogic | setOption | declSort | defSort | declFun | defFun |
      defFunsRec | declDatatypes | checkSat | getModel | getProof |
      getUnsatCore | echo | exit => rfl

/-- Stripping production provenance from every assertion preserves the class
of satisfying raw models. -/
theorem satisfiesCommands_stripAssertionAnnotations
    (model : Crush.SMT.Model) (commands : Array Crush.SMT.Command) :
    model.SatisfiesCommands (commands.map stripAssertionAnnotation) ↔
      model.SatisfiesCommands commands := by
  constructor
  · intro valid command member
    have mappedMember : stripAssertionAnnotation command ∈
        (commands.map stripAssertionAnnotation).toList := by
      simp only [Array.toList_map, List.mem_map]
      exact ⟨command, member, rfl⟩
    exact (satisfiesCommand_stripAssertionAnnotation model command).mp
      (valid _ mappedMember)
  · intro valid command member
    simp only [Array.toList_map, List.mem_map] at member
    rcases member with ⟨original, originalMember, rfl⟩
    exact (satisfiesCommand_stripAssertionAnnotation model original).mpr
      (valid original originalMember)

/-- Semantic unsatisfiability is unchanged by stripping top-level assertion
attributes. -/
theorem commandsUnsatisfiable_stripAssertionAnnotations
    (commands : Array Crush.SMT.Command) :
    Crush.SMT.CommandsUnsatisfiable
        (commands.map stripAssertionAnnotation) ↔
      Crush.SMT.CommandsUnsatisfiable commands := by
  constructor
  · intro unsat model valid
    exact unsat model
      ((satisfiesCommands_stripAssertionAnnotations model commands).mpr valid)
  · intro unsat model valid
    exact unsat model
      ((satisfiesCommands_stripAssertionAnnotations model commands).mp valid)

/-- Whole-array refinement evidence for one live production certificate and its
exact retained intrinsic sentence. Native declarations, recursive guard
definitions, all ordinary declarations, and every assertion must occur in the
guarded encoder's exact order. The only ignored syntax is the root provenance
annotation proved semantically transparent above. -/
structure ProductionAgreement (certificate : CertifiedDataEnv)
    (guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail)))
    (represented : certificate.Represents guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented)
    (reified : ReifiedSentenceFor certificate.source certificate.env
      certificate.bridge) where
  retained : certificate.reified = some reified
  representation : SMT.GuardedTheoryRepresentation guarding
    certificate.guardCommands (translatedTheory reified.source)
    (certificate.emitted.map stripAssertionAnnotation)

namespace ProductionAgreement

/-- Unsatisfiability of the exact live production snapshot reflects to the
retained intrinsic sentence, provided the production encoding has one uniform
guard interpretation for all datatype-lawful source models. -/
theorem unsat_source {certificate : CertifiedDataEnv}
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    {represented : certificate.Represents guarding.encoding}
    {guarded : certificate.GuardRepresentation guarding represented}
    {reified : ReifiedSentenceFor certificate.source certificate.env
      certificate.bridge}
    (agreement : ProductionAgreement certificate guarding represented guarded
      reified)
    (interpretation : certificate.GuardInterpretation guarding represented guarded)
    (unsat : Crush.SMT.CommandsUnsatisfiable certificate.emitted) :
    Datatype.Env.Unsatisfiable certificate.data.toModelEnv reified.source := by
  apply represented.unsat guarded interpretation reified.source
    agreement.representation
  exact (commandsUnsatisfiable_stripAssertionAnnotations
    certificate.emitted).mpr unsat

end ProductionAgreement

end Crush.Metatheory.VCG
