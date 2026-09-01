import Crush.Metatheory.VCG.Datatype
import Crush.Metatheory.VCG.Generate
import Crush.SMT.TermEq

/-!
# Certifying emitted SMT command equivalence

After the Crush translator has processed every selected fact,
`TranslateState.commands` contains its complete SMT command sequence. This module
checks that, after removing only the proved-semantically-irrelevant top-level
assertion names, those commands impose exactly the same model requirements as
the guarded encoding of the complete reified higher-order theory.

`CommandEquiv.build?` constructs a `CommandEquivCert` only when both command
sets contain exactly the same commands and both compared arrays pass the
modeled-fragment checker. Its `theory` field reuses the existing
`SMT.GuardedTheoryRepr`; `FactCommandRepr` specializes this comparison to one
reified fact. The theorem applies to the extensible
Crush translator only when the
shared encoding, datatype representations, guard interpretation, complete
reification, and this final command-set comparison have all been constructed.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened Reification
open Crush.SMT (CommandsInFragment CommandsWellTyped CommandsWellTypedIn
  Eval Holds SameCommandSet commandsInFragment_append modeledScriptWellTyped)
open Crush.SMT.Model (satisfiesCommands_append)

/-- Erase a top-level assertion annotation. The Crush translator adds `:named` at this
position so an unsat core can identify the source fact; the attribute does not
change the formula's untyped semantics. Nested annotations are part of the
represented term and remain untouched. -/
def stripAssertionAnnotation : Command → Command
  | .assert (.annot body _) => .assert body
  | command => command

/-- Removing a top-level assertion name does not change whether the command is
part of the modeled fragment. -/
@[simp] theorem inFragment_stripAssertionAnnotation
    (command : Command) :
    (stripAssertionAnnotation command).InFragment ↔ command.InFragment := by
  cases command with
  | assert formula => cases formula <;> rfl
  | setLogic | setOption | declSort | declFun | defFun | defFunsRec |
      declDatatypes | checkSat | getModel | getProof | getUnsatCore | echo | exit => rfl

/-- Top-level assertion attributes are semantically transparent. -/
@[simp] theorem satisfiesCommand_stripAssertionAnnotation
    (model : SMTModel) (command : Command) :
    model.SatisfiesCommand (stripAssertionAnnotation command) ↔
      model.SatisfiesCommand command := by
  cases command with
  | assert formula =>
      cases formula with
      | annot body attributes =>
          change Holds model [] body ↔
            Holds model [] (.annot body attributes)
          exact Eval.annot_iff.symm
      | lit | bvar | app | letE | forallE | existsE | lam => rfl
  | setLogic | setOption | declSort | declFun | defFun |
      defFunsRec | declDatatypes | checkSat | getModel | getProof |
      getUnsatCore | echo | exit => rfl

/-- Top-level assertion annotations do not affect which registered theory a
command uses. Attribute payloads are semantically transparent. -/
@[simp] theorem usesCommand_stripAssertionAnnotation
    (sigEnv : Crush.SMT.Theory.SigEnv)
    (theory : Fin sigEnv.modeled.length) (command : Command) :
    sigEnv.usesCommand theory (stripAssertionAnnotation command) =
      sigEnv.usesCommand theory command := by
  cases command with
  | assert formula =>
      cases formula with
      | annot body attributes =>
          change sigEnv.usesTerm theory body =
            sigEnv.usesTerm theory (.annot body attributes)
          rw [Crush.SMT.Theory.SigEnv.usesTerm.eq_8]
      | lit | bvar | app | letE | forallE | existsE | lam => rfl
  | setLogic | setOption | declSort | declFun | defFun |
      defFunsRec | declDatatypes | checkSat | getModel | getProof |
      getUnsatCore | echo | exit => rfl

/-- Normalizing top-level assertion annotations preserves every registered
theory requirement of the complete command array. -/
theorem usesCommands_stripAssertionAnnotations
    (sigEnv : Crush.SMT.Theory.SigEnv) (commands : Array Command) :
    sigEnv.usesCommands (commands.map stripAssertionAnnotation) =
      sigEnv.usesCommands commands := by
  funext theory
  simp [Crush.SMT.Theory.SigEnv.usesCommands]

/-- Normalizing top-level assertion annotations preserves the complete
dependency-closed theory combination. -/
theorem comb_stripAssertionAnnotations
    (env : SMT.Theory.Env) (commands : Array Command) :
    SMT.Theory.Comb.ofCommands env
        (commands.map stripAssertionAnnotation) =
      SMT.Theory.Comb.ofCommands env commands := by
  apply SMT.Theory.Comb.ext
  intro theory
  change env.closure.close
      (env.sigEnv.usesCommands (commands.map stripAssertionAnnotation)) theory =
    env.closure.close (env.sigEnv.usesCommands commands) theory
  rw [usesCommands_stripAssertionAnnotations]

/-- Removing top-level assertion names preserves the class of satisfying SMT
models. -/
theorem satisfiesCommands_stripAssertionAnnotations
    (model : SMTModel) (commands : Array Command) :
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
theorem commandsInFragment_stripAssertionAnnotations
    (commands : Array Command) :
    CommandsInFragment
        (commands.map stripAssertionAnnotation) ↔
      CommandsInFragment commands := by
  constructor
  · intro inFragment command member
    have mappedMember : stripAssertionAnnotation command ∈
        (commands.map stripAssertionAnnotation).toList := by
      simp only [Array.toList_map, List.mem_map]
      exact ⟨command, member, rfl⟩
    exact (inFragment_stripAssertionAnnotation command).mp
      (inFragment _ mappedMember)
  · intro inFragment command member
    simp only [Array.toList_map, List.mem_map] at member
    rcases member with ⟨original, originalMember, rfl⟩
    exact (inFragment_stripAssertionAnnotation original).mpr
      (inFragment original originalMember)

/-- Semantic unsatisfiability is unchanged by stripping top-level assertion
attributes. -/
theorem commandsUnsat_stripAssertionAnnotations
    (env : SMT.Theory.Env)
    (commands : Array Command)
    (normalizedWellTyped : CommandsWellTypedIn env.sigEnv
      (commands.map stripAssertionAnnotation))
    (originalWellTyped : CommandsWellTypedIn env.sigEnv commands) :
    SMT.Theory.Comb.CommandsUnsat env
        (commands.map stripAssertionAnnotation) ↔
      SMT.Theory.Comb.CommandsUnsat env commands := by
  constructor
  · intro unsat
    refine ⟨(commandsInFragment_stripAssertionAnnotations commands).mp
      unsat.inFragment, originalWellTyped, ?_⟩
    · intro model models valid
      exact unsat.noModel model
        (models.congr (comb_stripAssertionAnnotations env commands).symm)
        ((satisfiesCommands_stripAssertionAnnotations model commands).mpr valid)
  · intro unsat
    refine ⟨(commandsInFragment_stripAssertionAnnotations commands).mpr
      unsat.inFragment, normalizedWellTyped, ?_⟩
    · intro model models valid
      exact unsat.noModel model
        (models.congr (comb_stripAssertionAnnotations env commands))
        ((satisfiesCommands_stripAssertionAnnotations model commands).mp valid)

/-- The logic-selection command imposes no requirement on an SMT model. -/
theorem satisfiesCommands_setLogic (model : SMTModel) (logic : String)
    (commands : Array Command) :
    model.SatisfiesCommands (#[.setLogic logic] ++ commands) ↔
      model.SatisfiesCommands commands := by
  rw [satisfiesCommands_append]
  exact and_iff_right (by
    intro command member
    simp at member
    subst command
    trivial)

/-- A leading logic-selection command does not add any registered theory
requirement. -/
theorem usesCommands_setLogic (sigEnv : Crush.SMT.Theory.SigEnv)
    (logic : String) (commands : Array Command) :
    sigEnv.usesCommands (#[.setLogic logic] ++ commands) =
      sigEnv.usesCommands commands := by
  funext theory
  simp [Crush.SMT.Theory.SigEnv.usesCommands,
    Crush.SMT.Theory.SigEnv.usesCommand]

/-- A leading logic-selection command preserves the complete dependency-closed
theory combination. -/
theorem comb_setLogic (env : SMT.Theory.Env) (logic : String)
    (commands : Array Command) :
    SMT.Theory.Comb.ofCommands env (#[.setLogic logic] ++ commands) =
      SMT.Theory.Comb.ofCommands env commands := by
  apply SMT.Theory.Comb.ext
  intro theory
  change env.closure.close
      (env.sigEnv.usesCommands (#[.setLogic logic] ++ commands)) theory =
    env.closure.close (env.sigEnv.usesCommands commands) theory
  rw [usesCommands_setLogic]

/-- Semantic unsatisfiability is unchanged when the emitted script adds its
leading logic-selection command. -/
theorem commandsUnsat_setLogic (env : SMT.Theory.Env) (logic : String)
    (commands : Array Command)
    (commandsWellTyped : CommandsWellTypedIn env.sigEnv commands)
    (scriptWellTyped : CommandsWellTypedIn env.sigEnv
      (#[.setLogic logic] ++ commands)) :
    SMT.Theory.Comb.CommandsUnsat env
        (#[.setLogic logic] ++ commands) ↔
      SMT.Theory.Comb.CommandsUnsat env commands := by
  constructor
  · intro unsat
    have supportedParts :=
      (commandsInFragment_append #[.setLogic logic] commands).mp
        unsat.inFragment
    refine ⟨supportedParts.2, commandsWellTyped, ?_⟩
    intro model models valid
    exact unsat.noModel model
      (models.congr (comb_setLogic env logic commands).symm)
      ((satisfiesCommands_setLogic model logic commands).mpr valid)
  · intro unsat
    have logicInFragment : CommandsInFragment #[.setLogic logic] := by
      intro command member
      simp at member
      subst command
      trivial
    refine ⟨(commandsInFragment_append _ _).mpr
      ⟨logicInFragment, unsat.inFragment⟩, scriptWellTyped, ?_⟩
    intro model models valid
    exact unsat.noModel model
      (models.congr (comb_setLogic env logic commands))
      ((satisfiesCommands_setLogic model logic commands).mp valid)

/-- Decide whether two arrays impose the same model requirements. The command
semantics depends on membership, so order and duplicate occurrences do not
change the result. -/
def sameCommandSet? (left right : Array Command) : Bool :=
  (left.toList.all fun command => decide (command ∈ right.toList)) &&
    (right.toList.all fun command => decide (command ∈ left.toList))

@[simp] theorem sameCommandSet?_eq_true
    (left right : Array Command) :
    sameCommandSet? left right = true ↔ SameCommandSet left right := by
  simp only [sameCommandSet?, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, SameCommandSet]

/-! ## Whole-theory command equivalence -/

/-- Exact command-set agreement together with declaration-aware sort checking
of both the emitted commands and their annotation-normalized form. The latter
is the array related to the mathematical encoder; retaining both checks avoids
having to trust a generic theorem about the executable checker. -/
structure CommandEquivCert {translation : FactTranslation}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {expressions : List Lean.Expr}
    (reified : ReifiedSentencesFor translation.datatypes translation.constants
      expressions) where
  theory : SMT.GuardedTheoryRepr guarding translation.guardDefCommands
    (translatedTheories reified.sources)
    (translation.emittedCommands.map stripAssertionAnnotation)
  emittedWellTyped : CommandsWellTyped translation.emittedCommands
  normalizedWellTyped : CommandsWellTyped
    (translation.emittedCommands.map stripAssertionAnnotation)

namespace CommandEquiv

/-- Compare the emitted commands with the guarded encoding of all facts
reified under the same environment. -/
def build? {translation : FactTranslation}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {expressions : List Lean.Expr}
    (reified : ReifiedSentencesFor translation.datatypes translation.constants
      expressions) :
    Option (PLift (CommandEquivCert (guarding := guarding) reified)) := by
  let encodedCommands := guardedTheoryCommands guarding translation.guardDefCommands
    reified.sources
  let emittedCommands := translation.emittedCommands.map stripAssertionAnnotation
  if emittedTyped : modeledScriptWellTyped translation.emittedCommands then
    if normalizedTyped : modeledScriptWellTyped emittedCommands then
      if same : sameCommandSet? emittedCommands encodedCommands = true then
        exact some ⟨{
          theory := ⟨SMT.translatedDecls reified.sources,
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
theorem unsat_source {translation : FactTranslation}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.DatatypeRepr guarding.encoding)
    (guarded : translation.GuardDefEncoding guarding represented)
    {expressions : List Lean.Expr}
    {reified : ReifiedSentencesFor translation.datatypes translation.constants
      expressions}
    (cert : CommandEquivCert (guarding := guarding) reified)
    (interp : translation.GuardDefInterp guarding represented guarded)
    (unsat : SMT.CommandsUnsat translation.emittedCommands) :
    Datatype.Env.TheoryUnsatisfiable translation.datatypeSignaturePrefix.toModelEnv
      reified.sources := by
  apply represented.theory_unsat guarded interp reified.sources
    cert.theory
    (comb_stripAssertionAnnotations SMT.Int.env
      translation.emittedCommands).symm
  exact (commandsUnsat_stripAssertionAnnotations SMT.Int.env
    translation.emittedCommands cert.normalizedWellTyped
    cert.emittedWellTyped).mpr unsat

/-- Whole-theory reflection from the script returned by `buildScript`,
including its leading logic-selection command. -/
theorem unsat_source_script {translation : FactTranslation}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.DatatypeRepr guarding.encoding)
    (guarded : translation.GuardDefEncoding guarding represented)
    {expressions : List Lean.Expr}
    {reified : ReifiedSentencesFor translation.datatypes translation.constants
      expressions}
    (cert : CommandEquivCert (guarding := guarding) reified)
    (interp : translation.GuardDefInterp guarding represented guarded)
    (logic : String)
    (unsat : SMT.CommandsUnsat
      (#[.setLogic logic] ++ translation.emittedCommands)) :
    Datatype.Env.TheoryUnsatisfiable translation.datatypeSignaturePrefix.toModelEnv
      reified.sources :=
  unsat_source represented guarded cert interp (by
    exact (commandsUnsat_setLogic SMT.Int.env logic
      translation.emittedCommands cert.emittedWellTyped
      unsat.wellTyped).mp unsat)

end CommandEquiv

/-- The single-fact specialization of whole-theory command equivalence. SMT
datatype declarations, recursive guard definitions, ordinary declarations,
and assertions must all occur in the guarded encoder's command set. Command
order and duplicate elimination do not affect the membership-based semantics;
the only removed syntax is the top-level assertion name handled above. -/
structure FactCommandRepr (translation : FactTranslation)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.DatatypeRepr guarding.encoding)
    (guarded : translation.GuardDefEncoding guarding represented)
    (reified : ReifiedSentenceFor translation.expression translation.datatypes
      translation.constants) where
  retained : translation.reifiedSentence = some reified
  theory : CommandEquivCert (guarding := guarding)
    (ReifiedSentencesFor.cons reified .nil)

/-- A reified sentence existentially packaged with its command representation. -/
structure SomeFactCommandRepr (translation : FactTranslation)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.DatatypeRepr guarding.encoding)
    (guarded : translation.GuardDefEncoding guarding represented) where
  reified : ReifiedSentenceFor translation.expression translation.datatypes
    translation.constants
  repr : FactCommandRepr translation guarding represented guarded
    reified

namespace FactCommandRepr

/-- Compare the emitted command sequence with the guarded formal encoding and
return the retained fact plus a proof of mutual inclusion. The type of
`FactTranslation.reifiedSentence` ties the sentence to this fact's expression,
datatype environment, and constants, so a caller cannot substitute another
sentence. -/
def build? {translation : FactTranslation}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.DatatypeRepr guarding.encoding}
    {guarded : translation.GuardDefEncoding guarding represented} :
    Option (SomeFactCommandRepr translation guarding represented guarded) := by
  cases retained : translation.reifiedSentence with
  | none => exact none
  | some reified =>
      let witness : ReifiedSentencesFor translation.datatypes translation.constants
          [translation.expression] := .cons reified .nil
      match CommandEquiv.build? (guarding := guarding) witness
      with
      | none => exact none
      | some checked =>
          exact some {
            reified
            repr := { retained, theory := checked.down }}

/-- Unsatisfiability of the emitted commands reflects to the reified sentence,
provided the same guard interpretation works for every
source model satisfying the free-datatype model condition. -/
theorem unsat_source {translation : FactTranslation}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.DatatypeRepr guarding.encoding}
    {guarded : translation.GuardDefEncoding guarding represented}
    {reified : ReifiedSentenceFor translation.expression translation.datatypes
      translation.constants}
    (factRepr : FactCommandRepr translation guarding represented guarded
      reified)
    (interp : translation.GuardDefInterp guarding represented guarded)
    (unsat : SMT.CommandsUnsat translation.emittedCommands) :
    Datatype.Env.Unsatisfiable translation.datatypeSignaturePrefix.toModelEnv reified.source := by
  intro source freeDataModel sourceValid
  apply CommandEquiv.unsat_source represented guarded factRepr.theory
    interp unsat source freeDataModel
  intro formula membership
  simp only [ReifiedSentencesFor.sources, List.mem_singleton] at membership
  subst formula
  exact sourceValid

/-- Reflection from the exact script returned by `buildScript`, including its
leading logic-selection command. -/
theorem unsat_source_script {translation : FactTranslation}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.DatatypeRepr guarding.encoding}
    {guarded : translation.GuardDefEncoding guarding represented}
    {reified : ReifiedSentenceFor translation.expression translation.datatypes
      translation.constants}
    (factRepr : FactCommandRepr translation guarding represented guarded
      reified)
    (interp : translation.GuardDefInterp guarding represented guarded)
    (logic : String)
    (unsat : SMT.CommandsUnsat
      (#[.setLogic logic] ++ translation.emittedCommands)) :
    Datatype.Env.Unsatisfiable translation.datatypeSignaturePrefix.toModelEnv reified.source := by
  intro source freeDataModel sourceValid
  apply CommandEquiv.unsat_source_script represented guarded
    factRepr.theory interp logic unsat source freeDataModel
  intro formula membership
  simp only [ReifiedSentencesFor.sources, List.mem_singleton] at membership
  subst formula
  exact sourceValid

end FactCommandRepr

end Crush.Metatheory.VCG
