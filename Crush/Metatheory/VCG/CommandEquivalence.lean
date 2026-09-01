import Crush.Metatheory.VCG.Datatype
import Crush.Metatheory.VCG.Generate
import Crush.SMT.TermEq

/-!
# Relating emitted SMT commands to the formal encoding

After the Crush translator has processed every selected fact,
`TranslateState.commands` contains its complete SMT command sequence. This module
checks that, after removing only the proved-semantically-irrelevant top-level
assertion names, those commands impose exactly the same model requirements as
the guarded encoding of the complete reified higher-order theory.

`CommandEquivalence.build?` constructs the existing
`SMT.GuardedTheoryRepresentation` proposition only when both command sets
contain exactly the same commands. `FactCommandRepresentation` specializes
this comparison to one reified fact. The theorem applies to the extensible
Crush translator only when the
shared encoding, datatype representations, guard interpretation, complete
reification, and this final command-set comparison have all been constructed.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened Reification

/-- Erase a top-level assertion annotation. The Crush translator adds `:named` at this
position so an unsat core can identify the source fact; the attribute does not
change the formula's untyped semantics. Nested annotations are part of the
represented term and remain untouched. -/
def stripAssertionAnnotation : Crush.SMT.Command → Crush.SMT.Command
  | .assert (.annot body _) => .assert body
  | command => command

/-- Removing a top-level assertion name does not change whether the command is
part of the modeled fragment. -/
@[simp] theorem supported_stripAssertionAnnotation
    (command : Crush.SMT.Command) :
    (stripAssertionAnnotation command).Supported ↔ command.Supported := by
  cases command with
  | assert formula => cases formula <;> rfl
  | setLogic | setOption | declSort | declFun | defFun | defFunsRec |
      declDatatypes | checkSat | getModel | getProof | getUnsatCore | echo | exit => rfl

/-- Top-level assertion attributes are semantically transparent. -/
@[simp] theorem satisfiesCommand_stripAssertionAnnotation
    (model : Crush.SMT.Model) (command : Crush.SMT.Command) :
    model.SatisfiesCommand (stripAssertionAnnotation command) ↔
      model.SatisfiesCommand command := by
  cases command with
  | assert formula =>
      cases formula with
      | annot body attributes =>
          change Crush.SMT.Holds model [] body ↔
            Crush.SMT.Holds model [] (.annot body attributes)
          exact Crush.SMT.Eval.annot_iff.symm
      | lit | bvar | app | letE | forallE | existsE | lam => rfl
  | setLogic | setOption | declSort | declFun | defFun |
      defFunsRec | declDatatypes | checkSat | getModel | getProof |
      getUnsatCore | echo | exit => rfl

/-- Top-level assertion annotations do not affect which interpreted SMT
theories a command uses. Attribute payloads are semantically transparent in
the modeled fragment. -/
@[simp] theorem requiresIntegerSemantics_stripAssertionAnnotation
    (command : Crush.SMT.Command) :
    (stripAssertionAnnotation command).requiresIntegerSemantics =
      command.requiresIntegerSemantics := by
  cases command with
  | assert formula =>
      cases formula <;>
        simp [stripAssertionAnnotation,
          Crush.SMT.Command.requiresIntegerSemantics,
          Crush.SMT.Term.requiresIntegerSemantics]
  | setLogic | setOption | declSort | declFun | defFun |
      defFunsRec | declDatatypes | checkSat | getModel | getProof |
      getUnsatCore | echo | exit => rfl

/-- Normalizing top-level assertion annotations preserves the interpreted
theories required by the complete command array. -/
theorem commandsRequireIntegerSemantics_stripAssertionAnnotations
    (commands : Array Crush.SMT.Command) :
    Crush.SMT.CommandsRequireIntegerSemantics
        (commands.map stripAssertionAnnotation) =
      Crush.SMT.CommandsRequireIntegerSemantics commands := by
  simp [Crush.SMT.CommandsRequireIntegerSemantics]

/-- Removing top-level assertion names preserves the class of satisfying SMT
models. -/
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

/-- Removing top-level assertion names also preserves membership in the modeled
command fragment. -/
theorem commandsSupported_stripAssertionAnnotations
    (commands : Array Crush.SMT.Command) :
    Crush.SMT.CommandsSupported
        (commands.map stripAssertionAnnotation) ↔
      Crush.SMT.CommandsSupported commands := by
  constructor
  · intro supported command member
    have mappedMember : stripAssertionAnnotation command ∈
        (commands.map stripAssertionAnnotation).toList := by
      simp only [Array.toList_map, List.mem_map]
      exact ⟨command, member, rfl⟩
    exact (supported_stripAssertionAnnotation command).mp
      (supported _ mappedMember)
  · intro supported command member
    simp only [Array.toList_map, List.mem_map] at member
    rcases member with ⟨original, originalMember, rfl⟩
    exact (supported_stripAssertionAnnotation original).mpr
      (supported original originalMember)

/-- Semantic unsatisfiability is unchanged by stripping top-level assertion
attributes. -/
theorem commandsUnsatisfiable_stripAssertionAnnotations
    (commands : Array Crush.SMT.Command)
    (normalizedWellTyped : Crush.SMT.CommandsWellTyped
      (commands.map stripAssertionAnnotation))
    (originalWellTyped : Crush.SMT.CommandsWellTyped commands) :
    Crush.SMT.CommandsUnsatisfiable
        (commands.map stripAssertionAnnotation) ↔
      Crush.SMT.CommandsUnsatisfiable commands := by
  constructor
  · intro unsat
    refine ⟨(commandsSupported_stripAssertionAnnotations commands).mp
      unsat.supported, originalWellTyped, ?_⟩
    · intro model standard valid
      exact unsat.noModel model
        (standard.of_requirements_eq
          (commandsRequireIntegerSemantics_stripAssertionAnnotations commands).symm)
        ((satisfiesCommands_stripAssertionAnnotations model commands).mpr valid)
  · intro unsat
    refine ⟨(commandsSupported_stripAssertionAnnotations commands).mpr
      unsat.supported, normalizedWellTyped, ?_⟩
    · intro model standard valid
      exact unsat.noModel model
        (standard.of_requirements_eq
          (commandsRequireIntegerSemantics_stripAssertionAnnotations commands))
        ((satisfiesCommands_stripAssertionAnnotations model commands).mp valid)

/-- The logic-selection command imposes no requirement on an SMT model. -/
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

/-- A leading logic-selection command does not add an interpreted-theory
requirement. -/
theorem commandsRequireIntegerSemantics_setLogic (logic : String)
    (commands : Array Crush.SMT.Command) :
    Crush.SMT.CommandsRequireIntegerSemantics
        (#[.setLogic logic] ++ commands) =
      Crush.SMT.CommandsRequireIntegerSemantics commands := by
  simp [Crush.SMT.CommandsRequireIntegerSemantics,
    Crush.SMT.Command.requiresIntegerSemantics]

/-- Semantic unsatisfiability is unchanged when the emitted script adds its
leading logic-selection command. -/
theorem commandsUnsatisfiable_setLogic (logic : String)
    (commands : Array Crush.SMT.Command)
    (commandsWellTyped : Crush.SMT.CommandsWellTyped commands)
    (scriptWellTyped : Crush.SMT.CommandsWellTyped
      (#[.setLogic logic] ++ commands)) :
    Crush.SMT.CommandsUnsatisfiable (#[.setLogic logic] ++ commands) ↔
      Crush.SMT.CommandsUnsatisfiable commands := by
  constructor
  · intro unsat
    have supportedParts :=
      (Crush.SMT.commandsSupported_append #[.setLogic logic] commands).mp
        unsat.supported
    refine ⟨supportedParts.2, commandsWellTyped, ?_⟩
    intro model standard valid
    exact unsat.noModel model
      (standard.of_requirements_eq
        (commandsRequireIntegerSemantics_setLogic logic commands).symm)
      ((satisfiesCommands_setLogic model logic commands).mpr valid)
  · intro unsat
    have logicSupported : Crush.SMT.CommandsSupported #[.setLogic logic] := by
      intro command member
      simp at member
      subst command
      trivial
    refine ⟨(Crush.SMT.commandsSupported_append _ _).mpr
      ⟨logicSupported, unsat.supported⟩, scriptWellTyped, ?_⟩
    intro model standard valid
    exact unsat.noModel model
      (standard.of_requirements_eq
        (commandsRequireIntegerSemantics_setLogic logic commands))
      ((satisfiesCommands_setLogic model logic commands).mp valid)

/-- Decide whether two arrays impose the same model requirements. The command
semantics depends on membership, so order and duplicate occurrences do not
change the result. -/
def sameCommandSet? (left right : Array Crush.SMT.Command) : Bool :=
  (left.toList.all fun command => decide (command ∈ right.toList)) &&
    (right.toList.all fun command => decide (command ∈ left.toList))

@[simp] theorem sameCommandSet?_eq_true
    (left right : Array Crush.SMT.Command) :
    sameCommandSet? left right = true ↔ Crush.SMT.SameCommandSet left right := by
  simp only [sameCommandSet?, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Crush.SMT.SameCommandSet]

/-! ## Whole-theory command equivalence -/

/-- Exact command-set agreement together with declaration-aware sort checking
of both the emitted commands and their annotation-normalized form. The latter
is the array related to the mathematical encoder; retaining both checks avoids
having to trust a generic theorem about the executable checker. -/
structure ValidatedCommandEquivalence {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {expressions : List Lean.Expr}
    (reified : ReifiedSentencesFor translation.datatypes translation.constants
      expressions) where
  theory : SMT.GuardedTheoryRepresentation guarding translation.guardDefinitionCommands
    (translatedTheories reified.sources)
    (translation.emittedCommands.map stripAssertionAnnotation)
  emittedWellTyped : Crush.SMT.CommandsWellTyped translation.emittedCommands
  normalizedWellTyped : Crush.SMT.CommandsWellTyped
    (translation.emittedCommands.map stripAssertionAnnotation)

namespace CommandEquivalence

/-- Compare the emitted commands with the guarded encoding of all facts
reified under the same environment. -/
def build? {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {expressions : List Lean.Expr}
    (reified : ReifiedSentencesFor translation.datatypes translation.constants
      expressions) :
    Option (PLift (ValidatedCommandEquivalence (guarding := guarding) reified)) := by
  let encodedCommands := guardedTheoryCommands guarding translation.guardDefinitionCommands
    reified.sources
  let emittedCommands := translation.emittedCommands.map stripAssertionAnnotation
  if emittedTyped : Crush.SMT.metatheoryScriptWellTyped translation.emittedCommands then
    if normalizedTyped : Crush.SMT.metatheoryScriptWellTyped emittedCommands then
      if same : sameCommandSet? emittedCommands encodedCommands = true then
        exact some ⟨{
          theory := ⟨SMT.translatedDeclarations reified.sources,
            (sameCommandSet?_eq_true emittedCommands encodedCommands).mp same⟩
          emittedWellTyped := emittedTyped
          normalizedWellTyped := normalizedTyped }⟩
      else
        exact none
    else
      exact none
  else
    exact none

/-- Unsatisfiability of the emitted commands reflects to the complete reified
higher-order source theory. -/
theorem unsat_source {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    {expressions : List Lean.Expr}
    {reified : ReifiedSentencesFor translation.datatypes translation.constants
      expressions}
    (representation : ValidatedCommandEquivalence (guarding := guarding) reified)
    (interpretation : translation.GuardDefinitionSemantics guarding represented guarded)
    (unsat : Crush.SMT.CommandsUnsatisfiable translation.emittedCommands) :
    Datatype.Env.TheoryUnsatisfiable translation.datatypeSignaturePrefix.toModelEnv
      reified.sources := by
  apply represented.theory_unsat guarded interpretation reified.sources
    representation.theory
    (commandsRequireIntegerSemantics_stripAssertionAnnotations
      translation.emittedCommands).symm
  exact (commandsUnsatisfiable_stripAssertionAnnotations
    translation.emittedCommands representation.normalizedWellTyped
      representation.emittedWellTyped).mpr unsat

/-- Whole-theory reflection from the script returned by `buildScript`,
including its leading logic-selection command. -/
theorem unsat_source_script {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    {expressions : List Lean.Expr}
    {reified : ReifiedSentencesFor translation.datatypes translation.constants
      expressions}
    (representation : ValidatedCommandEquivalence (guarding := guarding) reified)
    (interpretation : translation.GuardDefinitionSemantics guarding represented guarded)
    (logic : String)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (#[.setLogic logic] ++ translation.emittedCommands)) :
    Datatype.Env.TheoryUnsatisfiable translation.datatypeSignaturePrefix.toModelEnv
      reified.sources :=
  unsat_source represented guarded representation interpretation
    ((commandsUnsatisfiable_setLogic logic translation.emittedCommands
      representation.emittedWellTyped unsat.wellTyped).mp unsat)

end CommandEquivalence

/-- The single-fact specialization of whole-theory command equivalence. SMT
datatype declarations, recursive guard definitions, ordinary declarations,
and assertions must all occur in the guarded encoder's command set. Command
order and duplicate elimination do not affect the membership-based semantics;
the only removed syntax is the top-level assertion name handled above. -/
structure FactCommandRepresentation (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (reified : ReifiedSentenceFor translation.expression translation.datatypes
      translation.constants) where
  retained : translation.reifiedSentence = some reified
  theory : ValidatedCommandEquivalence (guarding := guarding)
    (ReifiedSentencesFor.cons reified .nil)

/-- A reified sentence existentially packaged with its command representation. -/
structure SomeFactCommandRepresentation (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented) where
  reified : ReifiedSentenceFor translation.expression translation.datatypes
    translation.constants
  representation : FactCommandRepresentation translation guarding represented guarded
    reified

namespace FactCommandRepresentation

/-- Compare the emitted command sequence with the guarded formal encoding and
return the retained fact plus a proof of mutual inclusion. The type of
`FactTranslationRecord.reifiedSentence` ties the sentence to this fact's expression,
datatype environment, and constants, so a caller cannot substitute another
sentence. -/
def build? {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.Representation guarding.encoding}
    {guarded : translation.GuardDefinitionEncoding guarding represented} :
    Option (SomeFactCommandRepresentation translation guarding represented guarded) := by
  cases retained : translation.reifiedSentence with
  | none => exact none
  | some reified =>
      let witness : ReifiedSentencesFor translation.datatypes translation.constants
          [translation.expression] := .cons reified .nil
      match CommandEquivalence.build? (guarding := guarding) witness
      with
      | none => exact none
      | some checked =>
          exact some {
            reified
            representation := { retained, theory := checked.down }}

/-- Unsatisfiability of the emitted commands reflects to the reified sentence,
provided the same guard interpretation works for every
source model satisfying the free-datatype model condition. -/
theorem unsat_source {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.Representation guarding.encoding}
    {guarded : translation.GuardDefinitionEncoding guarding represented}
    {reified : ReifiedSentenceFor translation.expression translation.datatypes
      translation.constants}
    (representation : FactCommandRepresentation translation guarding represented guarded
      reified)
    (interpretation : translation.GuardDefinitionSemantics guarding represented guarded)
    (unsat : Crush.SMT.CommandsUnsatisfiable translation.emittedCommands) :
    Datatype.Env.Unsatisfiable translation.datatypeSignaturePrefix.toModelEnv reified.source := by
  intro source freeDataModel sourceValid
  apply CommandEquivalence.unsat_source represented guarded representation.theory
    interpretation unsat source freeDataModel
  intro formula membership
  simp only [ReifiedSentencesFor.sources, List.mem_singleton] at membership
  subst formula
  exact sourceValid

/-- Reflection from the exact script returned by `buildScript`, including its
leading logic-selection command. -/
theorem unsat_source_script {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.Representation guarding.encoding}
    {guarded : translation.GuardDefinitionEncoding guarding represented}
    {reified : ReifiedSentenceFor translation.expression translation.datatypes
      translation.constants}
    (representation : FactCommandRepresentation translation guarding represented guarded
      reified)
    (interpretation : translation.GuardDefinitionSemantics guarding represented guarded)
    (logic : String)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (#[.setLogic logic] ++ translation.emittedCommands)) :
    Datatype.Env.Unsatisfiable translation.datatypeSignaturePrefix.toModelEnv reified.source := by
  intro source freeDataModel sourceValid
  apply CommandEquivalence.unsat_source_script represented guarded
    representation.theory interpretation logic unsat source freeDataModel
  intro formula membership
  simp only [ReifiedSentencesFor.sources, List.mem_singleton] at membership
  subst formula
  exact sourceValid

end FactCommandRepresentation

end Crush.Metatheory.VCG
