import Crush.Metatheory.VCG.Soundness

/-!
# Live production agreement

This module is the refinement boundary for a completed single-fact direct
production run.
The unrestricted `emitTerm` implementation is not proved correct merely by
entering this module. Instead, `SingleFactAgreement` can be constructed only
when the final command snapshot, after erasing semantically transparent
top-level assertion attributes, is exactly the guarded intrinsic encoding of
the exact reified fact retained by `CertifiedDataEnv`.

The ordinary tactic query may contain several facts. Its final array cannot be
certified by this fact-local object; a future whole-run certificate must retain
one common intrinsic signature and the complete reified source theory.
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

/-- The logic-selection command is administrative in the raw model semantics. -/
theorem satisfiesCommands_setLogic (model : Crush.SMT.Model) (logic : String)
    (commands : Array Crush.SMT.Command) :
    model.SatisfiesCommands (#[.setLogic logic] ++ commands) ↔
      model.SatisfiesCommands commands := by
  rw [Crush.SMT.Model.satisfiesCommands_append]
  exact and_iff_right (by
    intro command member
    simp at member
    subst command
    trivial)

/-- Semantic unsatisfiability is unchanged when the production script adds its
leading logic-selection command. -/
theorem commandsUnsatisfiable_setLogic (logic : String)
    (commands : Array Crush.SMT.Command) :
    Crush.SMT.CommandsUnsatisfiable (#[.setLogic logic] ++ commands) ↔
      Crush.SMT.CommandsUnsatisfiable commands := by
  constructor
  · intro unsat model valid
    exact unsat model ((satisfiesCommands_setLogic model logic commands).mpr valid)
  · intro unsat model valid
    exact unsat model ((satisfiesCommands_setLogic model logic commands).mp valid)

/-- Whole-array refinement evidence for one live production certificate and its
exact retained intrinsic sentence. Native declarations, recursive guard
definitions, all ordinary declarations, and every assertion must occur in the
guarded encoder's exact order. The only ignored syntax is the root provenance
annotation proved semantically transparent above. -/
structure SingleFactAgreement (certificate : CertifiedDataEnv)
    (guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail)))
    (represented : certificate.Representation guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented)
    (reified : ReifiedSentenceFor certificate.source certificate.env
      certificate.bridge) where
  retained : certificate.reified = some reified
  representation : SMT.GuardedTheoryRepresentation guarding
    certificate.guardCommands (translatedTheory reified.source)
    (certificate.emitted.map stripAssertionAnnotation)

namespace SingleFactAgreement

/-- The exact retained sentence together with checked whole-array production
agreement. This packages the existential result of `build?` as data while the
agreement itself remains proof-irrelevant. -/
structure Checked (certificate : CertifiedDataEnv)
    (guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail)))
    (represented : certificate.Representation guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented) where
  reified : ReifiedSentenceFor certificate.source certificate.env
    certificate.bridge
  agreement : SingleFactAgreement certificate guarding represented guarded
    reified

/-- Check the completed production array against the exact guarded intrinsic
array and return proof-carrying agreement only on structural equality. The
reified fact is obtained from the environment-indexed certificate itself, so a
caller cannot substitute a different intrinsic sentence. -/
def build? {certificate : CertifiedDataEnv}
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    {represented : certificate.Representation guarding.encoding}
    {guarded : certificate.GuardRepresentation guarding represented} :
    Option (Checked certificate guarding represented guarded) := by
  cases retained : certificate.reified with
  | none => exact none
  | some reified =>
      let expected := guardedCommands guarding certificate.guardCommands
        reified.source
      if equal : certificate.emitted.map stripAssertionAnnotation = expected then
        exact some {
          reified
          agreement := {
            retained
            representation := by
              rw [equal]
              exact guardedCommands_represents guarding certificate.guardCommands
                reified.source }}
      else
        exact none

/-- Unsatisfiability of the exact live production snapshot reflects to the
retained intrinsic sentence, provided the production encoding has one uniform
guard interpretation for all datatype-lawful source models. -/
theorem unsat_source {certificate : CertifiedDataEnv}
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    {represented : certificate.Representation guarding.encoding}
    {guarded : certificate.GuardRepresentation guarding represented}
    {reified : ReifiedSentenceFor certificate.source certificate.env
      certificate.bridge}
    (agreement : SingleFactAgreement certificate guarding represented guarded
      reified)
    (interpretation : certificate.GuardInterpretation guarding represented guarded)
    (unsat : Crush.SMT.CommandsUnsatisfiable certificate.emitted) :
    Datatype.Env.Unsatisfiable certificate.data.toModelEnv reified.source := by
  apply represented.unsat guarded interpretation reified.source
    agreement.representation
  exact (commandsUnsatisfiable_stripAssertionAnnotations
    certificate.emitted).mpr unsat

/-- Reflection from the exact script returned by `buildScript`, including its
leading logic-selection command. -/
theorem unsat_source_script {certificate : CertifiedDataEnv}
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    {represented : certificate.Representation guarding.encoding}
    {guarded : certificate.GuardRepresentation guarding represented}
    {reified : ReifiedSentenceFor certificate.source certificate.env
      certificate.bridge}
    (agreement : SingleFactAgreement certificate guarding represented guarded
      reified)
    (interpretation : certificate.GuardInterpretation guarding represented guarded)
    (logic : String)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (#[.setLogic logic] ++ certificate.emitted)) :
    Datatype.Env.Unsatisfiable certificate.data.toModelEnv reified.source :=
  agreement.unsat_source interpretation
    ((commandsUnsatisfiable_setLogic logic certificate.emitted).mp unsat)

end SingleFactAgreement

end Crush.Metatheory.VCG
