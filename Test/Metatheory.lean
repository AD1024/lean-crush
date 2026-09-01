import Crush.Metatheory.HO.Syntax
import Crush.Metatheory.FO.Core
import Crush.Metatheory.HO.Semantics
import Crush.Metatheory.FO.Semantics
import Crush.Metatheory.Defunctionalization.Collect
import Crush.Metatheory.Defunctionalization.Annotate
import Crush.Metatheory.Defunctionalization.Eta
import Crush.Metatheory.Defunctionalization.EtaCorrectness
import Crush.Metatheory.Defunctionalization.Translate
import Crush.Metatheory.Defunctionalization.Core
import Crush.Metatheory.FO.FamilySemantics
import Crush.Metatheory.FO.Renaming
import Crush.Metatheory.Defunctionalization.LogicalRelation
import Crush.Metatheory.Notation
import Crush.Metatheory.Defunctionalization.Fundamental
import Crush.Metatheory.Defunctionalization.ModelExtension
import Crush.Metatheory.Defunctionalization.FlattenedApplication
import Crush.Metatheory.Defunctionalization.TermTranslation
import Crush.Metatheory.Defunctionalization.Flattened.Spine
import Crush.Metatheory.Defunctionalization.Flattened.Lambda
import Crush.Metatheory.Defunctionalization.Flattened.Translate
import Crush.Metatheory.Defunctionalization.Flattened.Currying
import Crush.Metatheory.Defunctionalization.Flattened.Denotation
import Crush.Metatheory.Defunctionalization.Flattened.Theory
import Crush.Metatheory.Defunctionalization.Flattened.ClosureCorrectness
import Crush.Metatheory.Guarded.Encoding
import Crush.Metatheory.Hooks
import Crush.Metatheory.SMT.Soundness
import Crush.Metatheory.SMT.Guarded
import Crush.Metatheory.SMT.GuardedSoundness
import Crush.Metatheory.VCG.Generate

open scoped Crush.Metatheory
open scoped Crush.SMT

/-!
Compile-time examples for the intrinsically typed metatheory language. The types of
these definitions exercise opaque sorts, constants, functions, lambdas, application,
equality, Boolean formulas, and quantification without relying on the translator's
translator.
-/

namespace Crush.Metatheory.Tests

private def entity : Ty := .base ⟨"Entity"⟩

/-- `f : Entity → Entity`, `a : Entity`, and `p : Entity → Bool`. -/
private abbrev exampleSignature : Signature :=
  [.arrow entity entity, entity, .arrow entity .bool]

private def f : Const exampleSignature (.arrow entity entity) := .here
private def a : Const exampleSignature entity := .there .here
private def p : Const exampleSignature (.arrow entity .bool) := .there (.there .here)

/-- The identity function over an opaque base sort. -/
def identity : ClosedTerm exampleSignature (.arrow entity entity) :=
  .lam (.var .here)

/-- The closed formula `f a = f a`. -/
def applicationEquality : Sentence exampleSignature :=
  .eq (.app (.const f) (.const a)) (.app (.const f) (.const a))

/-- The closed formula `∀ x, p x → ∃ y, f y = x`. -/
def quantifiedFormula : Sentence exampleSignature :=
  .forallE <| .imp
    (.app (.const p) (.var .here))
    (.existsE <| .eq
      (.app (.const f) (.var .here))
      (.var (.there .here)))

/-- A quantified higher-order variable: `∀ g : Entity → Entity, g a = g a`. -/
def higherOrderQuantifier : Sentence exampleSignature :=
  let g : Var [.arrow entity entity] (.arrow entity entity) := .here
  .forallE <| .eq
    (.app (.var g) (.const a))
    (.app (.var g) (.const a))

/-- Boolean literals and all primitive connectives remain formula-valued. -/
def booleanFormula : Sentence exampleSignature :=
  .iff
    (.and .trueE (.not .falseE))
    (.or (.app (.const p) (.const a)) (.not (.app (.const p) (.const a))))

/-! ## Surface syntax -/

def syntaxIdentity : ClosedTerm exampleSignature (.arrow entity entity) :=
  (ho| λ x : Entity. x)

def syntaxApplicationEquality : Sentence exampleSignature :=
  (ho| #f #a = #f #a)

def syntaxQuantifiedFormula : Sentence exampleSignature :=
  (ho| ∀ x : Entity, #p x → ∃ y : Entity, #f y = x)

def syntaxHigherOrderQuantifier : Sentence exampleSignature :=
  (ho| ∀ g : Entity → Entity, g #a = g #a)

def syntaxBooleanFormula : Sentence exampleSignature :=
  (ho| (⊤ ∧ ¬⊥) ↔ (#p #a ∨ ¬(#p #a)))

/-- Type and term antiquotation compose with the intrinsically typed elaborator. -/
def syntaxAntiquotation (body : Term exampleSignature [entity] entity) :
    ClosedTerm exampleSignature (.arrow entity entity) :=
  (ho| λ x : (~entity). ~body)

/-! ## Higher-order semantics -/

/-- Lambda and application have their ordinary semantics. -/
example (model : Model exampleSignature) (value : model.Base ⟨"Entity"⟩) :
    ⟦identity⟧[model, Valuation.empty model.Base] value = value := rfl

/-- Source equality is interpreted as actual semantic equality. -/
example (model : Model exampleSignature) :
    model ⊨ applicationEquality := rfl

end Crush.Metatheory.Tests

namespace Crush.Metatheory.FO.Tests

private def entity : Ty := .base ⟨"Entity"⟩

/-- The Crush translator flattens `Entity → Entity → Bool` into a ternary target
application symbol: a function value followed by both source arguments. -/
private def predicateApp : SymbolDecl :=
  appDecl entity (.arrow entity .bool)

private def capturedClosure : SymbolDecl :=
  closureDecl [entity] entity (.arrow entity .bool)

private abbrev exampleSignature : Signature :=
  [predicateApp, capturedClosure]

private def appSymbol : Symbol exampleSignature predicateApp := .here
private def closureSymbol : Symbol exampleSignature capturedClosure := .there .here

/-- `app (clo capture) x y`, intrinsically checked against the flattened app
declaration and the closure's capture list. -/
def flattenedClosureApplication :
    Term exampleSignature [.base ⟨"Entity"⟩, .base ⟨"Entity"⟩, .base ⟨"Entity"⟩] .bool :=
  let capture : Term exampleSignature _ (.base ⟨"Entity"⟩) := .var .here
  let x : Term exampleSignature _ (.base ⟨"Entity"⟩) := .var (.there .here)
  let y : Term exampleSignature _ (.base ⟨"Entity"⟩) := .var (.there (.there .here))
  let closure := Term.symbol closureSymbol (.cons capture .nil)
  .symbol appSymbol (.cons closure (.cons x (.cons y .nil)))

example : predicateApp.args =
    [.fn entity (.arrow entity .bool), .base ⟨"Entity"⟩, .base ⟨"Entity"⟩] := rfl

example : predicateApp.result = .bool := rfl

/-! ## Abstract-family binder infrastructure -/

private inductive BinderSymbol : SymbolDecl → Type

/-- Weakening preserves a variable's sort and shifts it beneath the fresh
binder, which is the operation used while assembling closure equations. -/
example :
    (FamilyTerm.var (symbols := BinderSymbol)
      (.here : Var [.base ⟨"Entity"⟩] (.base ⟨"Entity"⟩))).weaken
        (domain := .bool) =
      FamilyTerm.var (.there .here) := rfl

/-- Argument concatenation retains left-to-right application order. -/
private def firstBinderArgument :
    FamilyArgs BinderSymbol [.base ⟨"Entity"⟩] [.base ⟨"Entity"⟩] :=
  .cons (.var .here) .nil

example :
    firstBinderArgument.append firstBinderArgument =
      .cons (.var .here) (.cons (.var .here) .nil) := rfl

/-! ## First-order semantics -/

private def reflexiveSentence : Sentence [] :=
  .forallE (domain := .base ⟨"Entity"⟩) <| .eq (.var .here) (.var .here)

/-- Quantification and equality use the model's arbitrary target carriers. -/
example (model : Model []) : model.Satisfies reflexiveSentence :=
  by
    simp [Model.Satisfies, reflexiveSentence, Term.denote]

/-- Theory satisfaction applies formula satisfaction pointwise. -/
example (model : Model []) : model ⊨ᵀ [reflexiveSentence] := by
  intro formula membership
  simp only [List.mem_singleton] at membership
  subst formula
  simp [Model.Satisfies, reflexiveSentence, Term.denote]

end Crush.Metatheory.FO.Tests

namespace Crush.Metatheory.Defunctionalization.Tests

open Flattened

private def entity : Ty := .base ⟨"Entity"⟩

/-- `fun x => fun y => x`: the inner closure captures exactly `x`, while the
outer closure is closed. -/
private def nestedCapture :
    ClosedTerm [] (.arrow entity (.arrow entity entity)) :=
  .lam (.lam (.var (.there .here)))

example : (closures nestedCapture).length = 2 := rfl

example : (closures nestedCapture).head?.map Closure.captures = some [] := rfl

example : (closures nestedCapture)[1]?.map Closure.captures = some [0] := rfl

example : FV(nestedCapture) = [] := rfl

/-- Type and context brackets expose the type-erasure map used by the pass. -/
example : ⌊Ty.arrow entity entity⌋ = FO.FOSort.fn entity entity := rfl

example : ⌊[Ty.bool, entity]⌋^⋆ = [FO.FOSort.bool, FO.FOSort.base ⟨"Entity"⟩] := rfl

/-- The outer and residual arrow types each receive one collected arrow key. -/
example : (collect nestedCapture).arrows.length = 2 := rfl

/-- Empty source signature, two application symbols, and two closure constructors. -/
example : ((collect nestedCapture).targetSignature []).length = 4 := by
  rw [Plan.targetSignature_length]
  rfl

example : (annotate nestedCapture).closureIds = [0, 1] := rfl

example : (annotate nestedCapture).erase = nestedCapture := by simp

/-- A partial application with residual arrow type becomes a closure-shaped
lambda instead of an under-applied flattened `app`. -/
private abbrev partialSignature : Signature :=
  [.arrow entity (.arrow entity entity)]

private def binaryFn : Const partialSignature (.arrow entity (.arrow entity entity)) :=
  .here

private def partialApplication :
    Term partialSignature [entity] (.arrow entity entity) :=
  .app (.const binaryFn) (.var .here)

example : IsLambda (etaLong partialApplication) := etaLong_isLambda _

example :
    etaLong partialApplication =
      .lam (.app
        (.app
          (.lam (.lam
            (.app (.app (.const binaryFn) (.var (.there .here))) (.var .here))))
          (.var (.there .here)))
        (.var .here)) := rfl

example : (prepare partialApplication).annotated.erase =
    (prepare partialApplication).normalized := by simp

/-- Preparation collects the residual partial-application closure in addition
to the eta closures for the named binary function. -/
example : (prepare partialApplication).plan.closures.length = 3 := rfl

/-- Eta materialization of the residual function is semantically exact, not
merely a syntactic invariant. -/
example (model : Model partialSignature)
    (valuation : Valuation model.Base [entity]) :
    Term.denote model (etaLong partialApplication) valuation =
      Term.denote model partialApplication valuation :=
  etaLong_denote model partialApplication valuation

private def completeBinaryArgs :
    SourceArgs partialSignature [entity] [entity, entity] :=
  .cons (.var .here) (.cons (.var .here) .nil)

/-- The complete source application telescope is reconstructed as the expected
left-associated application chain. -/
example :
    completeBinaryArgs.applyTerm
        (.arrow entity (.arrow entity entity)) (.const binaryFn) =
      .app (.app (.const binaryFn) (.var .here)) (.var .here) := rfl

example :
    FO.appDecl entity (.arrow entity entity) =
      { args := [.fn entity (.arrow entity entity), .base ⟨"Entity"⟩,
          .base ⟨"Entity"⟩]
        result := .base ⟨"Entity"⟩ } :=
  flattened_binary_declaration_base entity entity ⟨"Entity"⟩

/-- The unary reference translation is total even before finite symbol
allocation. -/
private def translatedPartial := 𝒟⟦partialApplication⟧

/-- The indexed infix is the bundled source/target logical relation. -/
example {signature : Signature} {source : Model signature}
    {target : FO.FamilyModel (CoreSymbol signature)}
    (models : ModelRelation source target) (ty : Ty)
    (sourceValue : ty.Denote source.Base)
    (targetValue : ⌊ty⌋.Denote target.carriers) :
    (sourceValue ≈[models, ty] targetValue) ↔
      ValueRel source target models.baseRel ty sourceValue targetValue :=
  Iff.rfl

example : (defunctionalize nestedCapture).equations.length = 2 := rfl

/-! ## Flattened translation result substrate -/

/-- The primary flattened symbol family classifies application by semantic role. -/
private def flattenedAppSymbol :
    Flattened.Symbol [] (FO.appDecl entity entity) :=
  .application { domain := entity, codomain := entity }

/-- A result with no generated formulas has an empty combined theory. -/
private def variableTranslation :
    Flattened.TermTranslation [] [entity] entity where
  term := .var .here

example : variableTranslation.theory = [] := rfl

/-- Obligation classes are retained independently and combined in stable order. -/
private def guardedTranslation :
    Flattened.TermTranslation [] [entity] .bool where
  term := .boolLit true
  equations := [.boolLit true]
  extensionality := [.boolLit false]

example : guardedTranslation.theory = [.boolLit true, .boolLit false] := rfl

/-- Complete application-spine collection retains both arguments in source order. -/
private def collectedBinarySpine :=
  Flattened.ApplicationSpine.collect
    (completeBinaryArgs.applyTerm
      (.arrow entity (.arrow entity entity)) (.const binaryFn))

#eval show IO Unit from do
  unless collectedBinarySpine.arguments.types == [entity, entity] do
    throw <| IO.userError "complete application spine lost an argument"

example : collectedBinarySpine.toTerm =
    .app (.app (.const binaryFn) (.var .here)) (.var .here) := by
  apply Flattened.ApplicationSpine.toTerm_collect

/-- A partial spine records only its applied prefix and retains the residual
function result in its index. -/
private def collectedPartialSpine :=
  Flattened.ApplicationSpine.collect partialApplication

#eval show IO Unit from do
  unless collectedPartialSpine.arguments.types == [entity] do
    throw <| IO.userError "partial application spine has the wrong arguments"

/-- Recursive argument translation composes generated output in source order,
ready for the flattened application node to consume. -/
private def repeatedArguments :
    Flattened.AppliedArguments partialSignature [entity]
      (.arrow entity (.arrow entity entity)) entity :=
  .snoc (.snoc (.nil _) (.var .here)) (.var .here)

example
    (translateTerm : {ty : Ty} → Term partialSignature [entity] ty →
      Flattened.TermTranslation partialSignature [entity] ty)
    (equation : (translateTerm (.var .here :
      Term partialSignature [entity] entity)).equations = [.boolLit true]) :
    (repeatedArguments.translate translateTerm).generated.equations.length = 2 := by
  simp only [repeatedArguments, Flattened.AppliedArguments.translate]
  change ((translateTerm (.var .here)).equations ++
    (translateTerm (.var .here)).equations).length = 2
  rw [equation]
  rfl

/-- The target-side telescope can emit an n-ary application only after its
indices establish that all arguments leading to a ground result are present. -/
private def identityClosure : Closure partialSignature :=
  let body : Term partialSignature (entity :: [entity]) entity := .var .here
  Closure.ofBody body

private def targetIdentityArguments :
    Flattened.TargetArguments partialSignature [entity]
      (.arrow entity entity) entity :=
  .snoc (.nil _) (.var .here)

private def targetIdentityApplication :
    Flattened.TargetTerm partialSignature [entity] entity :=
  targetIdentityArguments.completeApplication
    (.symbol (Flattened.Symbol.closure identityClosure) .nil)
    (.base ⟨"Entity"⟩)

example : targetIdentityArguments.types = [entity] := by decide

/-- Opening a curried source value exposes its complete flattened telescope. -/
example :
    (Flattened.LambdaBody.ofTerm
      (.arrow entity (.arrow entity entity))
      (.const binaryFn :
        Term partialSignature [] (.arrow entity (.arrow entity entity)))).binders =
      [entity, entity] := by decide

/-- A closure equation can now be assembled under the exact binder context. -/
private def openedIdentityBody :=
  (Flattened.LambdaBody.ofTerm (.arrow entity entity)
    (.lam (.var .here) :
      Term partialSignature [entity] (.arrow entity entity))).openTarget
    (.symbol (Flattened.Symbol.closure identityClosure) .nil)
    (.nil _)

private def identityClosureEquation :
    Flattened.TargetSentence partialSignature :=
  openedIdentityBody.equation (.var .here)

example : openedIdentityBody.context = [entity, entity] := by decide

example (model : Model partialSignature)
    (valuation : Valuation model.Base [entity]) :
    Term.denote model
        (.lam (Flattened.LambdaBody.etaBody partialApplication)) valuation =
      Term.denote model partialApplication valuation :=
  Flattened.LambdaBody.denote_etaBody model partialApplication valuation

/-! ## Total flattened translation -/

private def translatedApplicationEquality :=
  𝓕⟦Crush.Metatheory.Tests.applicationEquality⟧

/- A completely applied source constant remains one flattened source-symbol
application and introduces no closure equation. -/
#eval show IO Unit from do
  unless translatedApplicationEquality.equations.length == 0 do
    throw <| IO.userError "complete application introduced a closure equation"

/-- Translating a residual function value materializes exactly one eta closure
and its fully flattened defining equation. -/
private def translatedPartialApplication :=
  𝓕⟦partialApplication⟧

#eval show IO Unit from do
  unless translatedPartialApplication.equations.length == 1 do
    throw <| IO.userError "partial application did not introduce one closure equation"

/-- A curried lambda chain is represented by one flattened closure rather than
one intermediate closure per binder. -/
private def translatedNestedCapture :=
  𝓕⟦nestedCapture⟧

#eval show IO Unit from do
  unless translatedNestedCapture.equations.length == 1 do
    throw <| IO.userError "curried lambda did not introduce one closure equation"

/-- Exact captures survive into the structural identity of the generated
closure symbol. -/
private def capturingLambda :
    Term partialSignature [entity] (.arrow entity entity) :=
  .lam (.var (.there .here))

private def firstClosureCaptureCount :
    List (Flattened.DeclaredSymbol partialSignature) → Nat
  | [] => 0
  | declaration :: declarations =>
      declaration.closureCaptureCount?.getD
        (firstClosureCaptureCount declarations)

private def translatedCaptureCount : Nat :=
  firstClosureCaptureCount (𝓕⟦capturingLambda⟧.declarations)

#eval show IO Unit from do
  unless translatedCaptureCount == 1 do
    throw <| IO.userError "closure did not retain its exact capture count"

/-- Function equality requests the extensionality formula for its arrow sort. -/
private def functionReflexivity : Sentence partialSignature :=
  .eq (.const binaryFn) (.const binaryFn)

#eval show IO Unit from do
  unless 𝓕⟦functionReflexivity⟧.extensionality.length == 1 do
    throw <| IO.userError "function equality did not request extensionality"

/-- Quantifiers and every Boolean constructor recurse through the same total
translation and preserve their generated output. -/
private def translatedQuantifiedFormula :=
  𝓕⟦Crush.Metatheory.Tests.quantifiedFormula⟧

private def translatedBooleanFormula :=
  𝓕⟦Crush.Metatheory.Tests.booleanFormula⟧

example : translatedQuantifiedFormula.term = translatedQuantifiedFormula.term := rfl
example : translatedBooleanFormula.term = translatedBooleanFormula.term := rfl

/-- The public theorem states denotation preservation for the actual total
flattened translation. -/
example (model : Model partialSignature)
    (valuation : Valuation model.Base [entity]) :
    ⟦𝓕⟦partialApplication⟧.term⟧[
        Flattened.canonicalModel model, Flattened.targetVal model valuation] =
      toCanonical model (.arrow entity entity)
        ⟦partialApplication⟧[model, valuation] :=
  Flattened.translate_denote model partialApplication valuation

/-- The flattened emitted-symbol shape and unary reference translation have the
same canonical denotation. -/
example (model : Model partialSignature)
    (valuation : Valuation model.Base [entity]) :
    ⟦𝓕⟦partialApplication⟧.term⟧[
        Flattened.canonicalModel model, Flattened.targetVal model valuation] =
      ⟦𝒟⟦partialApplication⟧⟧[
        canonicalModel model, Flattened.targetVal model valuation] :=
  Flattened.flattened_refines_unary model partialApplication valuation

/-- All equations and extensionality axioms emitted by flattened translation
hold simultaneously in its canonical model. -/
example (model : Model partialSignature) :
    Flattened.canonicalModel model ⊨ᵀ
      𝓕⟦partialApplication⟧.theory :=
  Flattened.generatedFormulas_valid model partialApplication

example (model : Model partialSignature) (formula : Sentence partialSignature)
    (sourceValid : model ⊨ formula) :
    Flattened.canonicalModel model ⊨ᵀ Flattened.translatedTheory formula :=
  Flattened.model_extension model formula sourceValid

example (formula : Sentence partialSignature)
    (targetUnsat : FO.FamilyTheoryUnsatisfiable
      (Flattened.translatedTheory formula)) :
    Unsatisfiable formula :=
  Flattened.target_unsat_implies_source_unsat formula targetUnsat

example (model : Model partialSignature) (theory : Theory partialSignature)
    (sourceValid : model.SatisfiesTheory theory) :
    Flattened.canonicalModel model ⊨ᵀ Flattened.translatedTheories theory :=
  Flattened.model_extension_theory model theory sourceValid

example (theory : Theory partialSignature)
    (targetUnsat : FO.FamilyTheoryUnsatisfiable
      (Flattened.translatedTheories theory)) :
    TheoryUnsatisfiable theory :=
  Flattened.target_theories_unsat_implies_source_unsat theory targetUnsat

/-- The complete semantic soundness theorem is exposed at the same abstract
symbol-family level as the total unary reference translation. -/
example (formula : Sentence partialSignature)
    (targetUnsat : FO.FamilyTheoryUnsatisfiable
      (defunctionalizationTheory formula)) :
    Unsatisfiable formula :=
  target_unsat_implies_source_unsat formula targetUnsat

end Crush.Metatheory.Defunctionalization.Tests

namespace Crush.Metatheory.Guarded.Tests

/-- `guardSort true Nat` is semantically the implication guard used here. -/
example : (∀ value : Nat, value = value) ↔
    ∀ value : Int, 0 ≤ value → value = value := by
  apply nat_forall_iff_int_guarded
  intro value
  simp

/-- `guardSort false Nat` is the corresponding conjunction guard. -/
example : (∃ value : Nat, value = 3) ↔
    ∃ value : Int, 0 ≤ value ∧ value = 3 := by
  apply nat_exists_iff_int_guarded
  intro value
  constructor
  · intro equality
    subst value
    rfl
  · intro equality
    exact Int.ofNat_inj.mp equality

example (fn : Nat → Nat) (argument : Int) :
    (0 : Int) ≤ (natInt.liftFunction fn argument : Int) :=
  nat_liftFunction_result_nonnegative fn argument

example (left right : Nat → Nat)
    (pointwise : ∀ argument : Int, 0 ≤ argument →
      natInt.liftFunction left argument = natInt.liftFunction right argument) :
    left = right :=
  nat_function_eq_of_nonnegative_pointwise left right pointwise

/-- `emitResultWF` is valid for symbols with arbitrary argument carriers. -/
example (fn : String → Nat) (argument : String) :
    natInt.guard (natInt.liftResult fn argument) :=
  natInt.liftResult_guard fn argument

end Crush.Metatheory.Guarded.Tests

namespace Crush.SMT.Tests

/-- A small total Boolean model used to exercise the relational SMT semantics. -/
private def boolModel : Model where
  Value := Bool
  inSort := fun _ _ => True
  sortNonempty := fun _ => ⟨false, trivial⟩
  bool := id
  boolTyped := fun _ => trivial
  boolInjective := by
    intro left right equality
    exact equality
  literal
    | .bool value => value
    | _ => false
  literalTyped := fun _ => trivial
  apply := fun _ _ _ => False

example : boolModel ⊨ₛ .lit (.bool true) :=
  Eval.boolLit true

example : boolModel ⊨ₛ .symbApp "not" #[.lit (.bool false)] :=
  Eval.not (Eval.boolLit false)

private def boolRefl : Term :=
  .forallE #[("value", boolSort)]
    (.symbApp "=" #[.bvar 0, .bvar 0])

example : boolModel ⊨ₛ boolRefl := by
  apply Eval.forallTrue
  intro values typed
  cases typed with
  | cons valueTyped tail =>
    cases tail
    exact Eval.eqTrue (Eval.bvar rfl) (Eval.bvar rfl) rfl

example : boolModel ⊨ₛᶜ #[.setLogic "ALL", .checkSat] := by
  have logicValid : boolModel ⊨ₛᶜ #[.setLogic "ALL"] := by
    simpa using Model.satisfiesCommands_push boolModel
      (commands := #[]) (command := .setLogic "ALL")
      (Model.satisfiesCommands_empty boolModel) (by trivial)
  simpa using Model.satisfiesCommands_push boolModel
    (commands := #[.setLogic "ALL"]) (command := .checkSat)
    logicValid (by trivial)

private def trueDefinition : FunDef := {
  name := "f"
  args := #[]
  resSort := boolSort
  body := .lit (.bool true) }

example : Command.Supported (.defFun trueDefinition) := by
  trivial

/-- Regression: a nonrecursive function definition has an ordinary satisfying
model; it is not declared unsatisfiable by absence of a command semantics. -/
private def definedBoolModel : Model :=
  { boolModel with
    apply := fun symbol arguments output =>
      symbol = .symb "f" ∧ arguments = [] ∧ output = true }

private theorem definedBoolModel_applyUnique : ApplyUnique definedBoolModel := by
  intro symbol arguments left right leftApplied rightApplied
  exact leftApplied.2.2.trans rightApplied.2.2.symm

example : definedBoolModel.SatisfiesCommand (.defFun trueDefinition) := by
  change trueDefinition.Holds definedBoolModel
  constructor
  · intro values typed
    have valuesEq := ValuesTyped.eq_nil typed
    subst values
    refine ⟨true, trivial, ⟨rfl, rfl, rfl⟩, ?_⟩
    intro other applied
    exact applied.2.2
  · intro values typed output
    change ValuesTyped definedBoolModel [] values at typed
    have valuesEq := ValuesTyped.eq_nil typed
    subst values
    change definedBoolModel.apply (.symb "f") [] output ↔
      Eval definedBoolModel [] (.lit (.bool true)) output
    rw [Eval.iff_eq definedBoolModel_applyUnique (Eval.boolLit true)]
    simp [definedBoolModel, boolModel]

#eval show IO Unit from do
  if metatheoryScriptWellTyped #[.defFunsRec #[]] then
    throw <| IO.userError "empty recursive-definition group was accepted"

#eval show IO Unit from do
  unless metatheoryScriptWellTyped #[.assert (.lit (.bool false))] do
    throw <| IO.userError "well-sorted false assertion was rejected"

example (wellTyped : CommandsWellTyped #[.assert (.lit (.bool false))]) :
    CommandsUnsatisfiable #[.assert (.lit (.bool false))] := by
  refine ⟨?_, ?_, ?_⟩
  · intro command member
    simp at member
    subst command
    trivial
  · exact wellTyped
  · intro model standard valid
    have evaluated := valid (.assert (.lit (.bool false))) (by simp)
    change Eval model [] (.lit (.bool false)) (model.bool true) at evaluated
    have impossible : true = false :=
      model.boolInjective (Eval.boolLit_iff.mp evaluated)
    contradiction

/-- The standard-model side condition is inhabited, so an empty script is not
unsatisfiable by an empty-domain-of-models accident. -/
example : ¬CommandsUnsatisfiable #[] := by
  intro unsat
  rcases standardModel_exists with ⟨model, standard⟩
  exact unsat.noModel model standard model.satisfiesCommands_empty

/- Standard integer semantics prevents distinct numerals from collapsing in
the relational model. -/
#eval show IO Unit from do
  unless metatheoryScriptWellTyped #[.assert (smt| (= 0 1))] do
    throw <| IO.userError "well-sorted integer equality was rejected"

example (wellTyped : CommandsWellTyped #[.assert (smt| (= 0 1))]) :
    CommandsUnsatisfiable #[.assert (smt| (= 0 1))] := by
  refine ⟨?_, ?_, ?_⟩
  · intro command member
    simp at member
    subst command
    trivial
  · exact wellTyped
  · intro model standard valid
    have evaluated := valid (.assert (smt| (= 0 1))) (by simp)
    change Eval model [] (smt| (= 0 1)) (model.bool true) at evaluated
    rcases standard.integer with ⟨integers⟩
    have different : model.literal (.num 0) ≠ model.literal (.num 1) := by
      intro equal
      apply (show (0 : Int) ≠ 1 by decide)
      apply integers.int_injective
      exact (integers.numeral 0).symm.trans (equal.trans (integers.numeral 1))
    have expected : Eval model [] (smt| (= 0 1)) (model.bool false) :=
      Eval.eqFalse
        (Eval.literal (.num 0) (by intro boolean impossible; cases impossible))
        (Eval.literal (.num 1) (by intro boolean impossible; cases impossible))
        different
    have impossible := evaluated.unique standard.applyUnique expected
    exact Bool.noConfusion (model.boolInjective impossible)

/- Sort names are checked against the preceding declaration environment. -/
#eval show IO Unit from do
  if metatheoryScriptWellTyped
      #[.declFun "x" #[] (.app (.symb "Undeclared") #[])] then
    throw <| IO.userError "undeclared sort was accepted"

/- The modeled fragment uses literal syntax for Boolean constants; otherwise
the generic symbol graph could assign `true` or `false` an arbitrary value. -/
#eval show IO Unit from do
  if metatheoryScriptWellTyped #[.assert (.app (.symb "true") #[])] then
    throw <| IO.userError "unmodeled Boolean constant syntax was accepted"

/- Regression: syntax coverage alone must not let contradictory sort uses in
an invalid SMT script establish semantic unsatisfiability. -/
#eval show IO Unit from do
  if metatheoryScriptWellTyped
      #[.assert (.lit (.num 0)), .assert (smt| (not 0))] then
    throw <| IO.userError "incompatibly sorted assertions were accepted"

#eval show IO Unit from do
  if metatheoryScriptWellTyped #[.assert (.lam #[] (.lit (.bool true)))] then
    throw <| IO.userError "lambda syntax was accepted by the first-order checker"

#eval show IO Unit from do
  if metatheoryScriptWellTyped #[.assert (.bvar 0)] then
    throw <| IO.userError "unbound variable was accepted"

end Crush.SMT.Tests

namespace Crush.Metatheory.SMT.Tests

private def tySort : Ty → Crush.SMT.SSort
  | .bool => .app (.symb "TyBool") #[]
  | .base sort => .app (.indexed "TyBase" #[.inl sort.name]) #[]
  | .arrow domain codomain =>
      .app (.symb "TyArrow") #[tySort domain, tySort codomain]

private theorem tySort_injective : Function.Injective tySort := by
  intro left right equality
  induction left generalizing right with
  | bool => cases right <;> simp_all [tySort]
  | base leftSort =>
      cases right with
      | bool | arrow => simp_all [tySort]
      | base rightSort =>
          simp only [tySort] at equality
          cases leftSort
          cases rightSort
          simp_all
  | arrow leftDomain leftCodomain domainIH codomainIH =>
      cases right with
      | bool | base => simp_all [tySort]
      | arrow rightDomain rightCodomain =>
          have parts : tySort leftDomain = tySort rightDomain ∧
              tySort leftCodomain = tySort rightCodomain := by
            simpa [tySort] using equality
          rw [domainIH parts.1, codomainIH parts.2]

private def foSort : FO.FOSort → Crush.SMT.SSort
  | .bool => Crush.SMT.boolSort
  | .base sort => .app (.indexed "Base" #[.inl sort.name]) #[]
  | .fn domain codomain =>
      .app (.symb "Fn") #[tySort domain, tySort codomain]

private theorem foSort_injective : Function.Injective foSort := by
  intro left right equality
  cases left with
  | bool => cases right <;> simp_all [foSort, Crush.SMT.boolSort]
  | base leftSort =>
      cases right with
      | bool | fn => simp_all [foSort, Crush.SMT.boolSort]
      | base rightSort =>
          simp only [foSort] at equality
          cases leftSort
          cases rightSort
          simp_all
  | fn leftDomain leftCodomain =>
      cases right with
      | bool | base => simp_all [foSort, Crush.SMT.boolSort]
      | fn rightDomain rightCodomain =>
          have parts : tySort leftDomain = tySort rightDomain ∧
              tySort leftCodomain = tySort rightCodomain := by
            simpa [foSort] using equality
          rw [tySort_injective parts.1, tySort_injective parts.2]

private inductive NoSymbol : FO.SymbolDecl → Type

private def encoding : Encoding NoSymbol where
  sort := foSort
  sort_injective := foSort_injective
  bool_eq := rfl
  name := fun symbol => nomatch symbol
  ident := fun symbol => nomatch symbol
  ident_decl_injective := fun left => nomatch left
  ident_injective := fun left => nomatch left
  ident_fresh := fun symbol => nomatch symbol
  nativeSort := fun _ => false
  nativeSymbol := fun symbol => nomatch symbol
  nativeCommands := #[]
  ordinary_ident := fun symbol => nomatch symbol

private def reflexiveFormula : FO.FamilySentence NoSymbol :=
  .eq (.boolLit true) (.boolLit true)

/-- SMT quotation and the pure encoder produce the same concrete formula. -/
example : term encoding reflexiveFormula = (smt| (= true true)) := rfl

private def guarded : GuardedEncoding NoSymbol where
  encoding
  guard := fun _ value => some (smt| (wf $value))

private def quantifiedReflexive (universal : Bool) :
    FO.FamilySentence NoSymbol :=
  let body : FO.FamilyTerm NoSymbol [.base ⟨"Entity"⟩] .bool :=
    .eq (.var .here) (.var .here)
  if universal then .forallE body else .existsE body

/-- Enlarged universal carriers use implication from the exact guard syntax. -/
example : guarded.term (quantifiedReflexive true) =
    let value : STerm := .bvar 0
    let condition := (smt| (wf $value))
    let body := (smt| (= $value $value))
    let expected : STerm := .forallE
      #[("x", encoding.sort (.base ⟨"Entity"⟩))]
      (smt| (=> $condition $body))
    expected := rfl

/-- Enlarged existential carriers use conjunction with the exact guard syntax. -/
example : guarded.term (quantifiedReflexive false) =
    let value : STerm := .bvar 0
    let condition := (smt| (wf $value))
    let body := (smt| (= $value $value))
    let expected : STerm := .existsE
      #[("x", encoding.sort (.base ⟨"Entity"⟩))]
      (smt| (and $condition $body))
    expected := rfl

/-- Disabling guards recovers the ordinary encoder exactly. -/
example : (GuardedEncoding.none encoding).term reflexiveFormula =
    term encoding reflexiveFormula := by
  exact GuardedEncoding.none_term encoding reflexiveFormula

example : TheoryRepresentation encoding [reflexiveFormula]
    (theory encoding [] [reflexiveFormula]) :=
  ⟨[], Crush.SMT.SameCommandSet.refl _⟩

private def carriers : FO.Carriers where
  Base := fun _ => Unit
  Fn := fun _ _ => Unit
  baseNonempty := fun _ => ⟨()⟩
  fnNonempty := fun _ _ => ⟨()⟩

private def target : FO.FamilyModel NoSymbol where
  carriers := carriers
  symbol := fun symbol => nomatch symbol

private def unaryGuards : UnaryGuards encoding target (fun _ _ => True) where
  ident
    | .bool => some (.symb "wf")
    | _ => none
  ident_injective := by
    intro left right identifier leftEq rightEq
    cases left <;> cases right <;> simp_all
  notBuiltin := by
    intro sort identifier equal
    cases sort with
    | bool =>
        simp only [Option.some.injEq] at equal
        subst identifier
        exact .symb "wf" (by decide) (by decide) (by decide) (by decide) (by decide)
    | base | fn => simp at equal
  sourceFresh := by
    intro sort identifier equal decl symbol
    nomatch symbol

/-- The shared recursive-definition theorem covers the exact emitted
`wfDef` syntax; components need only prove their body denotation. -/
example :
    (SMT.Datatype.wfDef "wf" "x" (encoding.sort .bool) #[]).Holds
      (modelWith encoding target unaryGuards.extra) := by
  apply unaryGuards.wfDef_holds (sort := .bool) (binder := "x") rfl #[]
  intro value
  exact Crush.SMT.Eval.boolLit true

/-- The generic guarded evaluator includes the exact empty-guard legacy path. -/
example : Crush.SMT.Eval (modelWith encoding target (.nil encoding target)) []
    ((GuardedEncoding.none encoding).term reflexiveFormula)
    (.typed .bool
      (reflexiveFormula.guardDenote target (fun _ _ => True)
        (FO.Valuation.empty target.carriers))) := by
  exact guardTerm_eval (GuardedEncoding.none encoding) target (.nil encoding target)
    _ (GuardedEncoding.none_semantics encoding target _) reflexiveFormula _ []
      (Env.empty target)

/-- A fresh unary `wf` predicate discharges the same theorem with an actual
guarded universal binder. -/
example : Crush.SMT.Eval
    (modelWith encoding target unaryGuards.extra) []
    (unaryGuards.guarding.term (quantifiedReflexive true))
    (.typed .bool
      ((quantifiedReflexive true).guardDenote target (fun _ _ => True)
        (FO.Valuation.empty target.carriers))) := by
  exact guardTerm_eval unaryGuards.guarding target unaryGuards.extra _
    (unaryGuards.semantics (by intros; trivial))
      (quantifiedReflexive true) _ [] (Env.empty target)

/-- A valid typed theory induces a model of its exact concrete commands. -/
example : ∃ smtModel : Crush.SMT.Model,
    smtModel ⊨ₛᶜ theory encoding [] [reflexiveFormula] := by
  apply lift encoding ⟨[], Crush.SMT.SameCommandSet.refl _⟩ target
  intro candidate membership
  simp only [List.mem_singleton] at membership
  subst candidate
  simp [FO.FamilyModel.Satisfies, reflexiveFormula]
  exact Crush.SMT.Model.satisfiesCommands_empty _

end Crush.Metatheory.SMT.Tests

namespace Crush.Metatheory.HookTests

private def hookCarriers : FO.Carriers where
  Base := fun _ => Unit
  Fn := fun _ _ => Unit
  baseNonempty := fun _ => ⟨()⟩
  fnNonempty := fun _ _ => ⟨()⟩

private def hookRelation : HookValueRelation (fun _ => Unit) hookCarriers :=
  fun _ _ _ => True

/-- A certified unary hook consumes a related argument and returns the residual
result certificate; this is the contract certified translation handlers must carry. -/
private def negationCertificate :
    TermHookCertificate hookRelation (.arrow .bool .bool) where
  sourceValue := Not
  targetValue := Not
  preserves := by
    unfold FlattenedHookRel
    intros
    trivial

example : FlattenedHookRel hookRelation .bool
    (negationCertificate.apply True True trivial).sourceValue
    (negationCertificate.apply True True trivial).targetValue :=
  (negationCertificate.apply True True trivial).preserves

/-- Registry-grade contracts cannot pick an always-true relation: they quantify
over every source model and use the canonical model-extension relation. -/
private def canonicalNegationCertificate :
    CanonicalTermHookCertificate [] (.arrow .bool .bool) where
  sourceValue := fun _ => Not
  targetValue := fun _ => Not
  preserves := by
    intro source sourceArgument targetArgument related
    exact not_congr related

example (source : Model []) (proposition : Prop) :
    CanonicalHookValueRelation source .bool
      (canonicalNegationCertificate.sourceValue source proposition)
      (canonicalNegationCertificate.targetValue source proposition) :=
  canonicalNegationCertificate.preserves source proposition proposition Iff.rfl

end Crush.Metatheory.HookTests
