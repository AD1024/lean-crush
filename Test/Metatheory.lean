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
import Crush.Metatheory.Defunctionalization.LogicalRelation
import Crush.Metatheory.Notation
import Crush.Metatheory.Defunctionalization.Fundamental
import Crush.Metatheory.Defunctionalization.ModelExtension
import Crush.Metatheory.Defunctionalization.FlattenedApplication
import Crush.Metatheory.Defunctionalization.ProductionClosure
import Crush.Metatheory.Guarded.Encoding
import Crush.Metatheory.Hooks

open scoped Crush.Metatheory

/-!
Compile-time examples for the intrinsically typed metatheory language. The types of
these definitions exercise opaque sorts, constants, functions, lambdas, application,
equality, Boolean formulas, and quantification without relying on the production
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
  (core| λ x : Entity. x)

def syntaxApplicationEquality : Sentence exampleSignature :=
  (core| #f #a = #f #a)

def syntaxQuantifiedFormula : Sentence exampleSignature :=
  (core| ∀ x : Entity, #p x → ∃ y : Entity, #f y = x)

def syntaxHigherOrderQuantifier : Sentence exampleSignature :=
  (core| ∀ g : Entity → Entity, g #a = g #a)

def syntaxBooleanFormula : Sentence exampleSignature :=
  (core| (⊤ ∧ ¬⊥) ↔ (#p #a ∨ ¬(#p #a)))

/-- Type and term antiquotation compose with the intrinsically typed elaborator. -/
def syntaxAntiquotation (body : Term exampleSignature [entity] entity) :
    ClosedTerm exampleSignature (.arrow entity entity) :=
  (core| λ x : (~entity). ~body)

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

/-- The live pass flattens `Entity → Entity → Bool` into a ternary target
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

/-- The classic core transformation is total even before finite symbol
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

example : (defunctionalize nestedCapture).axioms.length = 2 := rfl

/-- The complete semantic soundness theorem is exposed at the same abstract
symbol-family level as the total classic pass. -/
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

/-- Recursive datatype guards preserve the `Nat` field invariant. -/
example : natInt.option.guard (none : Option Int) := optionNat_guard_none

example : ¬natInt.option.guard (some (-1 : Int)) := by
  simp [Encoding.option, natInt]

example (value : Option Nat) :
    natInt.option.guard (natInt.option.encode value) :=
  optionNat_guard_encode value

/-- `emitResultWF` is valid for symbols with arbitrary argument carriers. -/
example (fn : String → Nat) (argument : String) :
    natInt.guard (natInt.liftResult fn argument) :=
  natInt.liftResult_guard fn argument

end Crush.Metatheory.Guarded.Tests

namespace Crush.Metatheory.HookTests

private def hookCarriers : FO.Carriers where
  Base := fun _ => Unit
  Fn := fun _ _ => Unit
  baseNonempty := fun _ => ⟨()⟩
  fnNonempty := fun _ _ => ⟨()⟩

private def hookRelation : HookValueRelation (fun _ => Unit) hookCarriers :=
  fun _ _ _ => True

/-- A certified unary hook consumes a related argument and returns the residual
result certificate; this is the contract live certified handlers must carry. -/
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
