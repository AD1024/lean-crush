import Crush.Metatheory.VCG.Datatype
import Crush.Metatheory.VCG.Generate
import Crush.SMT.TermEq

/-!
# Relating final production commands to the intrinsic theory

After the production translator has processed every selected fact,
`TranslateState.commands` contains its final SMT command array. This module
checks that, after removing only the proved-semantically-irrelevant top-level
assertion names, those commands impose exactly the same model requirements as
the guarded intrinsic encoding of the complete reified higher-order theory.

`ProductionTheoryAgreement` states this whole-theory correspondence, and
`build?` returns its proof only when both command sets contain exactly the same
commands. `ProductionFactAgreement` is the specialization to one retained fact.
The theorem applies to the extensible production translator only when the
shared encoding, datatype representations, guard interpretation, complete
reification, and this final command-set comparison have all been constructed.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened Reification

/-- Erase a top-level assertion annotation. Production adds `:named` at this
position so an unsat core can identify the source fact; the attribute does not
change the formula's untyped semantics. Nested annotations are part of the
represented term and remain untouched. -/
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

/-! ## Whole-theory production agreement -/

/-- Proof that the final production commands encode every fact reified under
one shared datatype environment and ordinary signature. -/
structure ProductionTheoryAgreement (production : ProductionFact)
    (guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature)))
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented)
    {expressions : List Lean.Expr}
    (reified : ReifiedSentencesFor production.datatypes production.constants
      expressions) where
  representation : SMT.GuardedTheoryRepresentation guarding
    production.guardCommands (translatedTheories reified.sources)
    (production.allCommands.map stripAssertionAnnotation)

namespace ProductionTheoryAgreement

/-- Compare the final production array with the guarded encoding of all facts
reified under the same environment. -/
def build? {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    {guarded : production.GuardRepresentation guarding represented}
    {expressions : List Lean.Expr}
    (reified : ReifiedSentencesFor production.datatypes production.constants
      expressions) :
    Option (PLift
      (ProductionTheoryAgreement production guarding represented guarded reified)) := by
  let expected := guardedTheoryCommands guarding production.guardCommands
    reified.sources
  let actual := production.allCommands.map stripAssertionAnnotation
  if same : sameCommandSet? actual expected = true then
    exact some ⟨{
      representation := ⟨SMT.translatedDeclarations reified.sources,
        (sameCommandSet?_eq_true actual expected).mp same⟩ }⟩
  else
    exact none

/-- Unsatisfiability of the final production commands reflects to the complete
retained intrinsic source theory. -/
theorem unsat_source {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    {guarded : production.GuardRepresentation guarding represented}
    {expressions : List Lean.Expr}
    {reified : ReifiedSentencesFor production.datatypes production.constants
      expressions}
    (agreement : ProductionTheoryAgreement production guarding represented guarded reified)
    (interpretation : production.GuardInterpretation guarding represented guarded)
    (unsat : Crush.SMT.CommandsUnsatisfiable production.allCommands) :
    Datatype.Env.TheoryUnsatisfiable production.datatypeBridge.toModelEnv
      reified.sources := by
  apply represented.theory_unsat guarded interpretation reified.sources
    agreement.representation
  exact (commandsUnsatisfiable_stripAssertionAnnotations
    production.allCommands).mpr unsat

/-- Whole-theory reflection from the script returned by `buildScript`,
including its leading logic-selection command. -/
theorem unsat_source_script {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    {guarded : production.GuardRepresentation guarding represented}
    {expressions : List Lean.Expr}
    {reified : ReifiedSentencesFor production.datatypes production.constants
      expressions}
    (agreement : ProductionTheoryAgreement production guarding represented guarded reified)
    (interpretation : production.GuardInterpretation guarding represented guarded)
    (logic : String)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (#[.setLogic logic] ++ production.allCommands)) :
    Datatype.Env.TheoryUnsatisfiable production.datatypeBridge.toModelEnv
      reified.sources :=
  agreement.unsat_source interpretation
    ((commandsUnsatisfiable_setLogic logic production.allCommands).mp unsat)

end ProductionTheoryAgreement

/-- The single-fact specialization of `ProductionTheoryAgreement`. Native
datatype declarations, recursive guard definitions, ordinary declarations,
and assertions must all occur in the guarded encoder's command set. Command
order and duplicate elimination do not affect the membership-based semantics;
the only removed syntax is the top-level assertion name handled above. -/
structure ProductionFactAgreement (production : ProductionFact)
    (guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature)))
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented)
    (reified : ReifiedSentenceFor production.expression production.datatypes
      production.constants) where
  retained : production.sentence = some reified
  theory : ProductionTheoryAgreement production guarding represented guarded
    (.cons reified .nil)

namespace ProductionFactAgreement

/-- The retained intrinsic sentence together with the checked final-command
comparison. -/
structure Checked (production : ProductionFact)
    (guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature)))
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented) where
  reified : ReifiedSentenceFor production.expression production.datatypes
    production.constants
  agreement : ProductionFactAgreement production guarding represented guarded
    reified

/-- Compare the final production array with the guarded intrinsic commands and
return the retained fact plus a proof of mutual inclusion. The type of
`ProductionFact.sentence` ties the sentence to this fact's expression,
datatype environment, and constants, so a caller cannot substitute another
sentence. -/
def build? {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    {guarded : production.GuardRepresentation guarding represented} :
    Option (Checked production guarding represented guarded) := by
  cases retained : production.sentence with
  | none => exact none
  | some reified =>
      let witness : ReifiedSentencesFor production.datatypes production.constants
          [production.expression] := .cons reified .nil
      match ProductionTheoryAgreement.build? (guarding := guarding)
          (represented := represented) (guarded := guarded) witness
      with
      | none => exact none
      | some checked =>
          exact some {
            reified
            agreement := { retained, theory := checked.down }}

/-- Unsatisfiability of the final production commands reflects to the retained
intrinsic sentence, provided the same guard interpretation works for every
source model satisfying the datatype laws. -/
theorem unsat_source {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    {guarded : production.GuardRepresentation guarding represented}
    {reified : ReifiedSentenceFor production.expression production.datatypes
      production.constants}
    (agreement : ProductionFactAgreement production guarding represented guarded
      reified)
    (interpretation : production.GuardInterpretation guarding represented guarded)
    (unsat : Crush.SMT.CommandsUnsatisfiable production.allCommands) :
    Datatype.Env.Unsatisfiable production.datatypeBridge.toModelEnv reified.source := by
  intro source lawful sourceValid
  apply agreement.theory.unsat_source interpretation unsat source lawful
  intro formula membership
  simp only [ReifiedSentencesFor.sources, List.mem_singleton] at membership
  subst formula
  exact sourceValid

/-- Reflection from the exact script returned by `buildScript`, including its
leading logic-selection command. -/
theorem unsat_source_script {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    {guarded : production.GuardRepresentation guarding represented}
    {reified : ReifiedSentenceFor production.expression production.datatypes
      production.constants}
    (agreement : ProductionFactAgreement production guarding represented guarded
      reified)
    (interpretation : production.GuardInterpretation guarding represented guarded)
    (logic : String)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (#[.setLogic logic] ++ production.allCommands)) :
    Datatype.Env.Unsatisfiable production.datatypeBridge.toModelEnv reified.source :=
  agreement.unsat_source interpretation
    ((commandsUnsatisfiable_setLogic logic production.allCommands).mp unsat)

end ProductionFactAgreement

end Crush.Metatheory.VCG
