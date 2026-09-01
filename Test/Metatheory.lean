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
import Crush.Metatheory.Defunctionalization.ModelExt
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
import Crush.Metatheory.VCG.CommandEquiv

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

private def trueDef : FunDef := {
  name := "f"
  args := #[]
  resSort := boolSort
  body := .lit (.bool true) }

example : Command.InFragment (.defFun trueDef) := by
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

example : definedBoolModel.SatisfiesCommand (.defFun trueDef) := by
  change trueDef.Holds definedBoolModel
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
  if modeledScriptWellTyped #[.defFunsRec #[]] then
    throw <| IO.userError "empty recursive-definition group was accepted"

example : CommandsWellTyped #[.assert (.lit (.bool false))] := by
  unfold CommandsWellTyped
  exact modeledScriptWellTyped_assertFalse

example :
    CommandsUnsat #[.assert (.lit (.bool false))] := by
  refine ⟨?_, ?_, ?_⟩
  · intro command member
    simp at member
    subst command
    trivial
  · unfold CommandsWellTyped
    exact modeledScriptWellTyped_assertFalse
  · intro model standard valid
    have evaluated := valid (.assert (.lit (.bool false))) (by simp)
    change Eval model [] (.lit (.bool false)) (model.bool true) at evaluated
    have impossible : true = false :=
      model.boolInjective (Eval.boolLit_iff.mp evaluated)
    contradiction

/-- The standard-model side condition is inhabited, so an empty script is not
unsatisfiable by an empty-domain-of-models accident. -/
example : ¬CommandsUnsat #[] := by
  intro unsat
  rcases standardModel_exists with ⟨model, standard⟩
  exact unsat.noModel model (standard.forCommands #[])
    model.satisfiesCommands_empty

/- Standard integer semantics prevents distinct numerals from collapsing in
the relational model. -/
example : CommandsWellTyped #[.assert (smt| (= 0 1))] := by
  unfold CommandsWellTyped
  exact modeledScriptWellTyped_distinctNumerals

example :
    CommandsUnsat #[.assert (smt| (= 0 1))] := by
  refine ⟨?_, ?_, ?_⟩
  · intro command member
    simp at member
    subst command
    trivial
  · unfold CommandsWellTyped
    exact modeledScriptWellTyped_distinctNumerals
  · intro model standard valid
    have evaluated := valid (.assert (smt| (= 0 1))) (by simp)
    change Eval model [] (smt| (= 0 1)) (model.bool true) at evaluated
    rcases standard.integer (by rfl) with ⟨integers⟩
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
  if modeledScriptWellTyped
      #[.declFun "x" #[] (.app (.symb "Undeclared") #[])] then
    throw <| IO.userError "undeclared sort was accepted"

/- The modeled fragment uses literal syntax for Boolean constants; otherwise
the generic symbol graph could assign `true` or `false` an arbitrary value. -/
#eval show IO Unit from do
  if modeledScriptWellTyped #[.assert (.app (.symb "true") #[])] then
    throw <| IO.userError "unmodeled Boolean constant syntax was accepted"

/- Regression: syntax coverage alone must not let contradictory sort uses in
an invalid SMT script establish semantic unsatisfiability. -/
#eval show IO Unit from do
  if modeledScriptWellTyped
      #[.assert (.lit (.num 0)), .assert (smt| (not 0))] then
    throw <| IO.userError "incompatibly sorted assertions were accepted"

#eval show IO Unit from do
  if modeledScriptWellTyped #[.assert (.lam #[] (.lit (.bool true)))] then
    throw <| IO.userError "lambda syntax was accepted by the first-order checker"

#eval show IO Unit from do
  if modeledScriptWellTyped #[.assert (.bvar 0)] then
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

example : TheoryRepr encoding [reflexiveFormula]
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

/-! ## Executable command-equivalence instance with ordinary symbols -/

open Defunctionalization

/-- A small injective tree serialization used only to give every possible
flattened symbol a collision-free identifier. The two source constants below
remain ordinary named SMT constants; generated application and closure symbols
occupy separate indexed namespaces. -/
private abbrev Token := String ⊕ Nat

private inductive Code where
  | text : String → Code
  | number : Nat → Code
  | node : Nat → List Code → Code

namespace Code

mutual
  private def tokens : Code → List Token
    | .text value => [.inr 0, .inl value]
    | .number value => [.inr 1, .inr value]
    | .node tag children =>
        [.inr 2, .inr tag, .inr children.length] ++ childrenTokens children

  private def childrenTokens : List Code → List Token
    | [] => []
    | child :: children =>
        .inr (tokens child).length :: tokens child ++ childrenTokens children
end

private theorem append_parts {a b restA restB : List Token}
    (lengthEq : a.length = b.length) (whole : a ++ restA = b ++ restB) :
    a = b ∧ restA = restB := by
  have heads := congrArg (List.take a.length) whole
  have tails := congrArg (List.drop a.length) whole
  have lengthLe : a.length ≤ b.length := Nat.le_of_eq lengthEq
  rw [List.take_append_of_le_length (Nat.le_refl _),
    List.take_append_of_le_length lengthLe] at heads
  rw [List.drop_append_of_le_length (Nat.le_refl _),
    List.drop_append_of_le_length lengthLe] at tails
  have takeRight : List.take a.length b = b := by
    rw [lengthEq]
    exact List.take_length
  have dropRight : List.drop a.length b = [] := by
    rw [lengthEq]
    exact List.drop_length
  simp only [List.take_length, takeRight, List.drop_length, dropRight,
    List.nil_append] at heads tails
  exact ⟨heads, tails⟩

mutual
  private theorem tokens_injective : ∀ {left right : Code},
      tokens left = tokens right → left = right
    | .text left, .text right, equal => by
        simp only [tokens, List.cons.injEq] at equal
        simp_all
    | .number left, .number right, equal => by
        simp only [tokens, List.cons.injEq] at equal
        simp_all
    | .node leftTag leftChildren, .node rightTag rightChildren, equal => by
        simp only [tokens] at equal
        have tagEq : leftTag = rightTag := by simp_all
        have lengthEq : leftChildren.length = rightChildren.length := by simp_all
        have childrenEq : childrenTokens leftChildren = childrenTokens rightChildren := by
          simpa [tagEq, lengthEq] using equal
        rw [tagEq, childrenTokens_injective childrenEq]
    | .text _, .number _, equal | .text _, .node _ _, equal |
      .number _, .text _, equal | .number _, .node _ _, equal |
      .node _ _, .text _, equal | .node _ _, .number _, equal => by
        simp [tokens] at equal

  private theorem childrenTokens_injective : ∀ {left right : List Code},
      childrenTokens left = childrenTokens right → left = right
    | [], [], _ => rfl
    | [], _ :: _, equal | _ :: _, [], equal => by
        simp [childrenTokens] at equal
    | left :: lefts, right :: rights, equal => by
        simp only [childrenTokens] at equal
        injection equal with lengthEq framedEq
        have tokenLengthEq : (tokens left).length = (tokens right).length := by
          exact Sum.inr.inj lengthEq
        have parts := append_parts tokenLengthEq framedEq
        have headEq := tokens_injective parts.1
        have tailEq := childrenTokens_injective parts.2
        rw [headEq, tailEq]
end

end Code

private def tyCode : Ty → Code
  | .bool => .node 0 []
  | .base sort => .node 1 [.text sort.name]
  | .arrow domain codomain => .node 2 [tyCode domain, tyCode codomain]

private theorem tyCode_injective : Function.Injective tyCode := by
  intro left
  induction left with
  | bool => intro right equal; cases right <;> simp_all [tyCode]
  | base leftSort =>
      intro right equal
      cases right with
      | bool | arrow => simp_all [tyCode]
      | base rightSort =>
          cases leftSort
          cases rightSort
          simp_all [tyCode]
  | arrow leftDomain leftCodomain domainIH codomainIH =>
      intro right equal
      cases right with
      | bool | base => simp_all [tyCode]
      | arrow rightDomain rightCodomain =>
          injection equal with _ childrenEq
          injection childrenEq with domainEq tailEq
          injection tailEq with codomainEq
          rw [domainIH domainEq, codomainIH codomainEq]

private def contextCode (context : List Ty) : Code :=
  .node 20 (context.map tyCode)

private theorem contextCode_injective : Function.Injective contextCode := by
  intro left
  induction left with
  | nil => intro right equal; cases right <;> simp_all [contextCode]
  | cons left lefts ih =>
      intro right equal
      cases right with
      | nil => simp_all [contextCode]
      | cons right rights =>
          simp only [contextCode, List.map_cons, Code.node.injEq,
            List.cons.injEq] at equal
          have tailCode : contextCode lefts = contextCode rights := by
            exact congrArg (Code.node 20) equal.2.2
          rw [tyCode_injective equal.2.1, ih tailCode]

@[simp] private theorem tyCode_eq {left right : Ty} :
    tyCode left = tyCode right ↔ left = right := tyCode_injective.eq_iff

@[simp] private theorem contextCode_eq {left right : List Ty} :
    contextCode left = contextCode right ↔ left = right := contextCode_injective.eq_iff

private theorem refToNat_injective {types : List Ty} {ty : Ty} :
    Function.Injective (refToNat (types := types) (ty := ty)) := by
  intro left
  induction left with
  | here => intro right equal; cases right with
    | here => rfl
    | there right => simp [refToNat] at equal
  | there left ih => intro right equal; cases right with
    | here => simp [refToNat] at equal
    | there right =>
        have innerEqual : refToNat left = refToNat right :=
          Nat.add_right_cancel equal
        rw [ih innerEqual]

private def termCode {signature : Signature} {context : Context} {ty : Ty}
    (term : Term signature context ty) : Code :=
  let indices := [contextCode context, tyCode ty]
  match term with
  | .var ref => .node 30 (indices ++ [.number (refToNat ref)])
  | .const ref => .node 31 (indices ++ [.number (refToNat ref)])
  | .boolLit value => .node 32 (indices ++ [.number value.toNat])
  | .not body => .node 33 (indices ++ [termCode body])
  | .and left right => .node 34 (indices ++ [termCode left, termCode right])
  | .or left right => .node 35 (indices ++ [termCode left, termCode right])
  | .imp left right => .node 36 (indices ++ [termCode left, termCode right])
  | .iff left right => .node 37 (indices ++ [termCode left, termCode right])
  | .eq left right => .node 38 (indices ++ [termCode left, termCode right])
  | .lam body => .node 39 (indices ++ [termCode body])
  | .app fn argument => .node 40 (indices ++ [termCode fn, termCode argument])
  | .forallE body => .node 41 (indices ++ [termCode body])
  | .existsE body => .node 42 (indices ++ [termCode body])

private theorem termCode_indices {signature : Signature}
    {leftContext rightContext : Context} {leftTy rightTy : Ty}
    (left : Term signature leftContext leftTy)
    (right : Term signature rightContext rightTy)
    (equal : termCode left = termCode right) :
    leftContext = rightContext ∧ leftTy = rightTy := by
  cases left <;> cases right <;> simp_all [termCode]

private theorem termCode_heq {signature : Signature} {context : Context} {ty : Ty}
    (left : Term signature context ty) :
    ∀ {rightContext rightTy} (right : Term signature rightContext rightTy),
      termCode left = termCode right → HEq left right := by
  induction left <;> intro rightContext rightTy right equal <;> cases right <;>
    simp_all [termCode]
  case var.var left right =>
    rcases equal with ⟨contextEq, typeEq, indexEq⟩
    subst rightContext
    subst rightTy
    exact heq_of_eq (congrArg Term.var (refToNat_injective indexEq))
  case const.const left right =>
    rcases equal with ⟨contextEq, typeEq, indexEq⟩
    subst rightContext
    subst rightTy
    exact heq_of_eq (congrArg Term.const (refToNat_injective indexEq))
  case boolLit.boolLit left right =>
    rcases equal with ⟨contextEq, valueEq⟩
    subst rightContext
    cases left <;> cases right <;> simp_all
  case not.not left right ih =>
    rcases equal with ⟨contextEq, bodyEq⟩
    subst rightContext
    have bodyHEq := ih right rfl
    cases bodyHEq
    rfl
  case and.and leftA leftB rightA rightB ihA ihB =>
    rcases equal with ⟨contextEq, leftEq, rightEq⟩
    subst rightContext
    have leftHEq := ihA rightA rfl
    cases leftHEq
    have rightHEq := ihB rightB rfl
    cases rightHEq
    rfl
  case or.or leftA leftB rightA rightB ihA ihB =>
    rcases equal with ⟨contextEq, leftEq, rightEq⟩
    subst rightContext
    have leftHEq := ihA rightA rfl
    cases leftHEq
    have rightHEq := ihB rightB rfl
    cases rightHEq
    rfl
  case imp.imp leftA leftB rightA rightB ihA ihB =>
    rcases equal with ⟨contextEq, leftEq, rightEq⟩
    subst rightContext
    have leftHEq := ihA rightA rfl
    cases leftHEq
    have rightHEq := ihB rightB rfl
    cases rightHEq
    rfl
  case iff.iff leftA leftB rightA rightB ihA ihB =>
    rcases equal with ⟨contextEq, leftEq, rightEq⟩
    subst rightContext
    have leftHEq := ihA rightA rfl
    cases leftHEq
    have rightHEq := ihB rightB rfl
    cases rightHEq
    rfl
  case eq.eq leftA leftB rightA rightB ihA ihB =>
    rcases equal with ⟨contextEq, leftEq, rightEq⟩
    subst rightContext
    have typeEq := (termCode_indices _ _ leftEq).2
    subst leftB
    have leftTermEq := eq_of_heq (ihA rightA rfl)
    have rightTermEq := eq_of_heq (ihB rightB rfl)
    rw [leftTermEq, rightTermEq]
  case lam.lam left right ih =>
    rcases equal with ⟨contextEq, ⟨domainEq, codomainEq⟩, bodyEq⟩
    subst rightContext
    subst domainEq
    subst codomainEq
    have bodyHEq := ih right rfl
    cases bodyHEq
    rfl
  case app.app leftFn leftArg rightFn rightArg fnIH argIH =>
    rcases equal with ⟨contextEq, resultEq, fnEq, argEq⟩
    subst rightContext
    subst resultEq
    have domainEq := (termCode_indices _ _ argEq).2
    subst leftArg
    have fnTermEq := eq_of_heq (fnIH rightArg rfl)
    have argTermEq := eq_of_heq (argIH rightFn rfl)
    rw [fnTermEq, argTermEq]
  case forallE.forallE left right ih =>
    rcases equal with ⟨contextEq, bodyEq⟩
    subst rightContext
    have bodyContextEq := (termCode_indices _ _ bodyEq).1
    injection bodyContextEq with domainEq
    subst left
    have bodyTermEq := eq_of_heq (ih right rfl)
    rw [bodyTermEq]
  case existsE.existsE left right ih =>
    rcases equal with ⟨contextEq, bodyEq⟩
    subst rightContext
    have bodyContextEq := (termCode_indices _ _ bodyEq).1
    injection bodyContextEq with domainEq
    subst left
    have bodyTermEq := eq_of_heq (ih right rfl)
    rw [bodyTermEq]

private theorem termCode_injective {signature : Signature} {context : Context} {ty : Ty} :
    Function.Injective (termCode (signature := signature) (context := context) (ty := ty)) := by
  intro left right equal
  exact eq_of_heq (termCode_heq left right equal)

private def arrowCode (arrow : Arrow) : Code :=
  .node 50 [tyCode arrow.domain, tyCode arrow.codomain]

private theorem arrowCode_injective : Function.Injective arrowCode := by
  intro left right equal
  cases left
  cases right
  simp only [arrowCode, Code.node.injEq, List.cons.injEq] at equal
  simp_all

private def closureCode {signature : Signature} (closure : Closure signature) : Code :=
  .node 51 [contextCode closure.context, tyCode closure.domain,
    tyCode closure.codomain, termCode closure.body]

private theorem closureCode_injective {signature : Signature} :
    Function.Injective (closureCode (signature := signature)) := by
  intro left right equal
  cases left
  cases right
  simp only [closureCode, Code.node.injEq, List.cons.injEq] at equal
  rcases equal with ⟨_, contextEq, domainEq, codomainEq, bodyEq⟩
  have contextEq := contextCode_injective contextEq
  have domainEq := tyCode_injective domainEq
  have codomainEq := tyCode_injective codomainEq
  subst contextEq
  subst domainEq
  subst codomainEq
  rw [termCode_injective bodyEq.1]

private abbrev TwoConstantSignature : Signature := [.bool, .bool]

private def symbolCode {decl : FO.SymbolDecl} :
    Flattened.Symbol TwoConstantSignature decl → Code
  | .sourceConstant constant => .node 60 [.number (refToNat constant)]
  | .application arrow => .node 61 [arrowCode arrow]
  | .closure closure => .node 62 [closureCode closure]

private theorem symbolCode_heq {leftDecl rightDecl : FO.SymbolDecl}
    (left : Flattened.Symbol TwoConstantSignature leftDecl)
    (right : Flattened.Symbol TwoConstantSignature rightDecl)
    (equal : symbolCode left = symbolCode right) : HEq left right := by
  cases left with
  | sourceConstant left =>
      cases right with
      | sourceConstant right =>
          simp only [symbolCode, Code.node.injEq, List.cons.injEq] at equal
          have indexEq : refToNat left = refToNat right :=
            Code.number.inj equal.2.1
          cases left with
          | here => cases right with
            | here => rfl
            | there right => simp [refToNat] at indexEq
          | there left => cases right with
            | here => simp [refToNat] at indexEq
            | there right =>
                cases left with
                | here => cases right with
                  | here => rfl
                  | there right => nomatch right
                | there left => nomatch left
      | application | closure => simp [symbolCode] at equal
  | application left =>
      cases right with
      | sourceConstant | closure => simp [symbolCode] at equal
      | application right =>
          simp only [symbolCode, Code.node.injEq, List.cons.injEq] at equal
          have arrowEq := arrowCode_injective equal.2.1
          subst right
          rfl
  | closure left =>
      cases right with
      | sourceConstant | application => simp [symbolCode] at equal
      | closure right =>
          simp only [symbolCode, Code.node.injEq, List.cons.injEq] at equal
          have closureEq := closureCode_injective equal.2.1
          subst right
          rfl

private theorem symbolCode_decl_injective {leftDecl rightDecl : FO.SymbolDecl}
    (left : Flattened.Symbol TwoConstantSignature leftDecl)
    (right : Flattened.Symbol TwoConstantSignature rightDecl)
    (equal : symbolCode left = symbolCode right) : leftDecl = rightDecl := by
  cases left with
  | sourceConstant left =>
      cases right with
      | sourceConstant right =>
          simp only [symbolCode, Code.node.injEq, List.cons.injEq] at equal
          have indexEq : refToNat left = refToNat right :=
            Code.number.inj equal.2.1
          cases left with
          | here => cases right with
            | here => rfl
            | there right => simp [refToNat] at indexEq
          | there left => cases right with
            | here => simp [refToNat] at indexEq
            | there right =>
                cases left with
                | here => cases right with
                  | here => rfl
                  | there right => nomatch right
                | there left => nomatch left
      | application | closure => simp [symbolCode] at equal
  | application left =>
      cases right with
      | sourceConstant | closure => simp [symbolCode] at equal
      | application right =>
          simp only [symbolCode, Code.node.injEq, List.cons.injEq] at equal
          rw [arrowCode_injective equal.2.1]
  | closure left =>
      cases right with
      | sourceConstant | application => simp [symbolCode] at equal
      | closure right =>
          simp only [symbolCode, Code.node.injEq, List.cons.injEq] at equal
          rw [closureCode_injective equal.2.1]

private theorem symbolCode_injective {decl : FO.SymbolDecl} :
    Function.Injective (symbolCode (decl := decl)) := by
  intro left right equal
  exact eq_of_heq (symbolCode_heq left right equal)

private def sourceName {ty : Ty} : Const TwoConstantSignature ty → String
  | .here => "left"
  | .there .here => "right"

private def symbolName {decl : FO.SymbolDecl} :
    Flattened.Symbol TwoConstantSignature decl → String
  | .sourceConstant constant => sourceName constant
  | .application _ => "unused_application"
  | .closure _ => "unused_closure"

private def symbolIdent {decl : FO.SymbolDecl} :
    Flattened.Symbol TwoConstantSignature decl → Crush.SMT.Ident
  | .sourceConstant constant => .symb (sourceName constant)
  | .application arrow => .indexed "test_application" (Code.tokens (arrowCode arrow)).toArray
  | .closure closure => .indexed "test_closure" (Code.tokens (closureCode closure)).toArray

private theorem symbolIdent_implies_code {leftDecl rightDecl : FO.SymbolDecl}
    (left : Flattened.Symbol TwoConstantSignature leftDecl)
    (right : Flattened.Symbol TwoConstantSignature rightDecl)
    (equal : symbolIdent left = symbolIdent right) : symbolCode left = symbolCode right := by
  cases left with
  | sourceConstant left =>
      cases right with
      | sourceConstant right =>
          cases left with
          | here => cases right with
            | here => rfl
            | there right =>
                cases right with
                | here => simp [symbolIdent, sourceName] at equal
                | there right => nomatch right
          | there left =>
              cases left with
              | here => cases right with
                | here => simp [symbolIdent, sourceName] at equal
                | there right => cases right with
                  | here => rfl
                  | there right => nomatch right
              | there left => nomatch left
      | application | closure => simp [symbolIdent] at equal
  | application left =>
      cases right with
      | sourceConstant | closure => simp [symbolIdent] at equal
      | application right =>
          simp only [symbolIdent, Crush.SMT.Ident.indexed.injEq] at equal
          have tokensEq : Code.tokens (arrowCode left) = Code.tokens (arrowCode right) :=
            congrArg Array.toList equal.2
          have codeEq := Code.tokens_injective tokensEq
          simp [symbolCode, codeEq]
  | closure left =>
      cases right with
      | sourceConstant | application => simp [symbolIdent] at equal
      | closure right =>
          simp only [symbolIdent, Crush.SMT.Ident.indexed.injEq] at equal
          have tokensEq : Code.tokens (closureCode left) = Code.tokens (closureCode right) :=
            congrArg Array.toList equal.2
          have codeEq := Code.tokens_injective tokensEq
          simp [symbolCode, codeEq]

private def symbolNative {decl : FO.SymbolDecl} :
    Flattened.Symbol TwoConstantSignature decl → Bool
  | .sourceConstant _ => false
  | .application _ | .closure _ => true

/-- A total encoding of the flattened symbol family over two source constants.
`left` and `right` are ordinary SMT constants. Symbols that cannot occur in the
chosen first-order theory still receive distinct indexed identifiers, which is
why the injectivity obligations below are substantive rather than `nomatch`
proofs. -/
private def twoConstantEncoding :
    Crush.Metatheory.SMT.Encoding (Flattened.Symbol TwoConstantSignature) where
  sort := foSort
  sort_injective := foSort_injective
  bool_eq := rfl
  name := symbolName
  ident := symbolIdent
  ident_decl_injective := by
    intro leftDecl rightDecl left right equal
    exact symbolCode_decl_injective left right
      (symbolIdent_implies_code left right equal)
  ident_injective := by
    intro decl left right equal
    exact symbolCode_injective (symbolIdent_implies_code left right equal)
  ident_fresh := by
    intro decl symbol
    cases symbol with
    | sourceConstant constant =>
        cases constant with
        | here => exact by decide
        | there constant => cases constant with
          | here => exact by decide
          | there constant => nomatch constant
    | application arrow =>
        exact ⟨Crush.SMT.NotBuiltin.indexed _ _, by simp [symbolIdent]⟩
    | closure closure =>
        exact ⟨Crush.SMT.NotBuiltin.indexed _ _, by simp [symbolIdent]⟩
  nativeSort := fun _ => false
  nativeSymbol := symbolNative
  nativeCommands := #[]
  ordinary_ident := by
    intro decl symbol ordinary
    cases symbol with
    | sourceConstant constant => rfl
    | application arrow | closure arrow => simp [symbolNative] at ordinary

private def leftConstant : Const TwoConstantSignature .bool := .here
private def rightConstant : Const TwoConstantSignature .bool := .there .here

/-- `∀ x : Bool, x = left ∨ x = right`, so the checked theory uses both
ordinary constants and an actual binder. -/
private def twoConstantFormula : Sentence TwoConstantSignature :=
  .forallE <| .or
    (.eq (.var .here) (.const leftConstant))
    (.eq (.var .here) (.const rightConstant))

private def twoConstantTheory : Theory TwoConstantSignature := [twoConstantFormula]

private def twoConstantGuarding :=
  Crush.Metatheory.SMT.GuardedEncoding.none twoConstantEncoding

private def generatedTwoConstantCommands : Array Crush.SMT.Command :=
  Crush.Metatheory.VCG.guardedTheoryCommands twoConstantGuarding #[] twoConstantTheory

private def twoConstantCommands : Array Crush.SMT.Command := #[
  .declFun "left" #[] Crush.SMT.boolSort,
  .declFun "right" #[] Crush.SMT.boolSort,
  .assert (.forallE #[("x", Crush.SMT.boolSort)]
    (.app (.symb "or") #[
      .app (.symb "=") #[.bvar 0, .app (.symb "left") #[]],
      .app (.symb "=") #[.bvar 0, .app (.symb "right") #[]]]))]

private def emptyDatatypeEnv : Crush.Metatheory.Reification.DatatypeEnv where
  blocks := #[]

private def twoConstantLeftProposition : Prop := True
private def twoConstantRightProposition : Prop := False

private def leftExpression : Lean.Expr := .const ``twoConstantLeftProposition []
private def rightExpression : Lean.Expr := .const ``twoConstantRightProposition []
private def propositionType : Lean.Expr := .sort .zero

private def reifiedConstants :
    Crush.Metatheory.Reification.ReifiedSignature TwoConstantSignature :=
  .cons leftExpression (.bool propositionType)
    (.cons rightExpression (.bool propositionType) .nil)

/-- A Lean expression with the same constructor tree as `twoConstantFormula`.
The separate Lean-to-HO denotation theorem remains outside this test's scope. -/
private def sourceExpression : Lean.Expr :=
  let type := Lean.Expr.sort .zero
  let leftEquality := Lean.mkApp3 (.const ``Eq []) type (.bvar 0) leftExpression
  let rightEquality := Lean.mkApp3 (.const ``Eq []) type (.bvar 0) rightExpression
  .forallE `x type (Lean.mkApp2 (.const ``Or []) leftEquality rightEquality) .default

private def reifiedFormula :
    Crush.Metatheory.Reification.ReifiedSentenceFor sourceExpression emptyDatatypeEnv
      reifiedConstants where
  typeExpr := propositionType
  source := twoConstantFormula
  witness := {
    sourceShape := .forallE .unsupported
      (.or (.eq .variable .constant) (.eq .variable .constant))
    shapeCorrespondence := by rfl }

private def translationRecord : Crush.Metatheory.VCG.FactTranslation where
  expression := sourceExpression
  datatypes := emptyDatatypeEnv
  ordinarySignature := TwoConstantSignature
  constants := reifiedConstants
  reifiedSentence := some reifiedFormula
  emittedCommands := twoConstantCommands
  datatypeDeclLocations := .nil
  guardDefLocations := .nil

private def reifiedTheory :
    Crush.Metatheory.Reification.ReifiedSentencesFor emptyDatatypeEnv reifiedConstants
      [sourceExpression] :=
  .cons reifiedFormula .nil

/-- The executable link between the exact concrete command array and the
mathematical guarded encoder. -/
private def checkedCommandEquiv :=
  Crush.Metatheory.VCG.CommandEquiv.build?
    (translation := translationRecord) (guarding := twoConstantGuarding) reifiedTheory

/-- The empty datatype prefix is represented by the same nontrivial symbol
encoding used by the command-equivalence check. -/
private def twoConstantRepr :
    translationRecord.DatatypeRepr twoConstantEncoding where
  decls :=
    Crush.Metatheory.VCG.DatatypeDeclLocations.Repr.nil
      twoConstantEncoding
  datatypeDecls_eq := rfl

/-- With no custom datatypes, there are no recursive datatype-guard commands
or guard identifiers to allocate. -/
private def twoConstantGuardDefEncoding :
    translationRecord.GuardDefEncoding twoConstantGuarding
      twoConstantRepr where
  defs := .nil
  commands_eq := rfl
  ident := fun _ => none
  ident_injective := by simp
  notReserved := by simp
  sourceFresh := by simp
  linked := trivial

/-- Every source model induces a standard model for this exact Boolean-only
script. No integer carrier is requested because the retained commands contain
no integer syntax. -/
private noncomputable def twoConstantGuardDefInterp :
    translationRecord.GuardDefInterp twoConstantGuarding
      twoConstantRepr twoConstantGuardDefEncoding where
  realize := by
    intro source freeDataModel
    let prior := Crush.Metatheory.Datatype.Lifted.refl
      (Defunctionalization.Flattened.canonicalModel source)
    let lifted := twoConstantRepr.datatypeRepr.liftedFrom
      source freeDataModel prior
    let base := Crush.Metatheory.SMT.ExtraGraph.nil twoConstantEncoding
      lifted.target
    let guards := twoConstantGuardDefEncoding.toUnaryGuards
      lifted.target (fun sort => (lifted.relation sort).guard)
    have liftedEq : lifted = prior := by
      exact Crush.Metatheory.SMT.Datatype.EnvRepr.liftedFrom_nil
        twoConstantRepr.datatypeRepr source freeDataModel prior
    let TotalGuard := fun current : Crush.Metatheory.Datatype.Lifted
        (Defunctionalization.Flattened.canonicalModel source) =>
      ∀ sort (value : sort.Denote current.target.carriers),
        (current.relation sort).guard value
    have priorTotal : TotalGuard prior := by
      intro sort value
      exact Crush.Metatheory.Datatype.Lifted.refl_guard
        (Defunctionalization.Flattened.canonicalModel source) sort value
    have liftedTotal : TotalGuard lifted := liftedEq.symm ▸ priorTotal
    have baseUnique : Crush.SMT.ApplyUnique
        (Crush.Metatheory.SMT.modelWith twoConstantEncoding lifted.target base) := by
      exact Crush.Metatheory.SMT.modelWith_nil_applyUnique
        twoConstantEncoding lifted.target
    have fresh : guards.Fresh base := by
      intro sort identifier present values output
      change (none : Option Crush.SMT.Ident) = some identifier at present
      contradiction
    have guardSemantics : twoConstantGuarding.TermSemantics lifted.target
        (guards.over base) (fun sort => (lifted.relation sort).guard) := by
      apply (Crush.Metatheory.SMT.GuardedEncoding.none_termSemantics
        twoConstantEncoding lifted.target (guards.over base)).congr
      intro sort value
      constructor
      · intro
        exact liftedTotal sort value
      · intro
        trivial
    refine {
      prior
      base
      baseUnique
      fresh
      semantics := guardSemantics
      standard := ?_ }
    refine {
      bool_exhaustive := Crush.Metatheory.SMT.modelWith_bool_exhaustive
        twoConstantEncoding lifted.target (guards.over base)
      integer := ?_
      apply_unique := guards.applyUnique_over base baseUnique fresh }
    intro required
    simp [translationRecord, twoConstantCommands,
      Crush.SMT.CommandsUseInt,
      Crush.SMT.Command.usesInt,
      Crush.SMT.Term.usesInt] at required

/-- The concrete Lean expression and the HO formula have the same reified
constructor tree. This checks only syntactic reification, not denotation. -/
private theorem twoConstantShapesMatch :
    Crush.Metatheory.Reification.shapesMatch
      (Crush.Metatheory.Reification.exprShape sourceExpression)
      (Crush.Metatheory.Reification.termShape twoConstantFormula) = true := by
  rfl

/-- The declaration-aware checker accepts the exact nonempty environment used
by the command-equivalence regression, with a kernel-checked certificate. -/
private theorem twoConstantCommands_wellTyped :
    Crush.SMT.modeledScriptWellTyped twoConstantCommands = true := by
  unfold twoConstantCommands
  prove_modeled_script_well_typed

private theorem generatedTwoConstantCommands_eq :
    generatedTwoConstantCommands = twoConstantCommands := by
  unfold generatedTwoConstantCommands twoConstantCommands
  unfold Crush.Metatheory.VCG.guardedTheoryCommands
  unfold Crush.Metatheory.SMT.GuardedEncoding.theory
  simp [twoConstantGuarding, twoConstantEncoding,
    Crush.Metatheory.SMT.GuardedEncoding.theoryBody,
    Crush.Metatheory.SMT.GuardedEncoding.assertions,
    Crush.Metatheory.SMT.GuardedEncoding.none,
    Crush.Metatheory.SMT.translatedDecls,
    Crush.Metatheory.SMT.ofDeclared,
    Crush.Metatheory.SMT.ordinarySorts,
    Crush.Metatheory.SMT.ordinaryDecls,
    Crush.Metatheory.SMT.usedSorts,
    Crush.Metatheory.SMT.termSorts,
    Crush.Metatheory.SMT.argumentSorts,
    Crush.Metatheory.SMT.sortDecl?,
    Crush.Metatheory.SMT.declaration,
    Crush.Metatheory.SMT.varIndex,
    Crush.SMT.Term.symbApp,
    Defunctionalization.Flattened.translatedTheories,
    Defunctionalization.Flattened.translatedTheory,
    Defunctionalization.Flattened.translatedSentence,
    Defunctionalization.Flattened.translate,
    Defunctionalization.Flattened.translateWith,
    Defunctionalization.Flattened.TermTranslation.ofGenerated,
    Defunctionalization.Flattened.TermTranslation.combine,
    Defunctionalization.Flattened.TermTranslation.generated,
    Defunctionalization.Flattened.TermTranslation.theory,
    Defunctionalization.Flattened.AuxiliaryTheory.empty,
    Defunctionalization.Flattened.AuxiliaryTheory.declare,
    Defunctionalization.Flattened.AuxiliaryTheory.theory,
    Defunctionalization.Flattened.DeclaredSymbol.of,
    Defunctionalization.targetVar, Renaming.lift,
    twoConstantTheory, twoConstantFormula, leftConstant, rightConstant,
    FO.FOSort.ofTy,
    symbolNative, symbolName, symbolIdent, sourceName, foSort]

private theorem checkedCommandEquiv_succeeds :
    checkedCommandEquiv.isSome = true := by
  have generated : Crush.Metatheory.VCG.guardedTheoryCommands
      twoConstantGuarding #[] twoConstantTheory = twoConstantCommands := by
    simpa [generatedTwoConstantCommands] using generatedTwoConstantCommands_eq
  have stripped : twoConstantCommands.map
      Crush.Metatheory.VCG.stripAssertionAnnotation = twoConstantCommands := by
    apply Array.toList_inj.mp
    simp [twoConstantCommands,
      Crush.Metatheory.VCG.stripAssertionAnnotation]
  unfold checkedCommandEquiv
  simp [Crush.Metatheory.VCG.CommandEquiv.build?,
    translationRecord, reifiedTheory, stripped,
    twoConstantCommands_wellTyped]
  change Crush.SMT.SameCommandSet twoConstantCommands
    (Crush.Metatheory.VCG.guardedTheoryCommands
      twoConstantGuarding #[] twoConstantTheory)
  rw [generated]
  exact Crush.SMT.SameCommandSet.refl _

/-- Extract the kernel-checked evidence returned by the executable comparison.
The preceding theorem proves that this option is present. -/
private theorem validatedTwoConstantCommands :
    Crush.Metatheory.VCG.CommandEquivCert
      (translation := translationRecord)
      (guarding := twoConstantGuarding) reifiedTheory :=
  (checkedCommandEquiv.get (by
    simpa using checkedCommandEquiv_succeeds)).down

/-- A concrete source model used to show that the complete target-model
construction is inhabited for the nontrivial symbol encoding. -/
private def twoConstantSourceModel :
    Crush.Metatheory.Model TwoConstantSignature where
  Base := fun _ => Unit
  baseNonempty := fun _ => ⟨()⟩
  const := fun constant =>
    match constant with
    | .here => True
    | .there .here => False

private theorem twoConstantSourceModel_valid :
    twoConstantSourceModel.SatisfiesTheory twoConstantTheory := by
  intro formula member
  simp only [twoConstantTheory, List.mem_singleton] at member
  subst formula
  change ∀ proposition : Prop, proposition = True ∨ proposition = False
  intro proposition
  by_cases valid : proposition
  · left
    exact propext ⟨fun _ => trivial, fun _ => valid⟩
  · right
    exact propext ⟨valid, False.elim⟩

/-- The complete datatype/guard/SMT model construction produces a standard
model satisfying the exact command array. Thus the final soundness link is not
inhabited only through an impossible integer-side premise. -/
private theorem twoConstantCommands_haveStandardModel :
    ∃ model : Crush.SMT.Model,
      model.StandardFor twoConstantCommands ∧
        model.SatisfiesCommands twoConstantCommands := by
  have encoding : Crush.Metatheory.SMT.GuardedTheoryRepr
      twoConstantGuarding #[]
        (Defunctionalization.Flattened.translatedTheories twoConstantTheory)
        twoConstantCommands := by
    refine ⟨Crush.Metatheory.SMT.translatedDecls twoConstantTheory, ?_⟩
    change Crush.SMT.SameCommandSet twoConstantCommands
      generatedTwoConstantCommands
    rw [generatedTwoConstantCommands_eq]
    exact Crush.SMT.SameCommandSet.refl _
  exact Crush.Metatheory.VCG.FactTranslation.DatatypeRepr.sound
    (translation := translationRecord) (guarding := twoConstantGuarding)
    twoConstantRepr twoConstantGuardDefEncoding
    twoConstantSourceModel .nil
    (twoConstantGuardDefInterp.realize twoConstantSourceModel .nil)
    encoding rfl
    (Defunctionalization.Flattened.model_extension_theory
      twoConstantSourceModel twoConstantTheory twoConstantSourceModel_valid)

private theorem twoConstantCommands_notUnsatisfiable :
    ¬Crush.SMT.CommandsUnsat twoConstantCommands := by
  intro unsat
  obtain ⟨model, standard, valid⟩ := twoConstantCommands_haveStandardModel
  exact unsat.noModel model standard valid

/-- The exact evidence returned by `CommandEquiv.build?` composes with
the final reflection theorem. For this satisfiable running example the premise
is false, as proved above; the theorem checks the complete API connection from
the retained command array back to its reified higher-order theory. -/
private theorem twoConstantCommands_reflectUnsatisfiability
    (unsat : Crush.SMT.CommandsUnsat twoConstantCommands) :
    Crush.Metatheory.Datatype.Env.TheoryUnsatisfiable []
      twoConstantTheory := by
  exact Crush.Metatheory.VCG.CommandEquiv.unsat_source
    twoConstantRepr twoConstantGuardDefEncoding
    validatedTwoConstantCommands twoConstantGuardDefInterp unsat


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
