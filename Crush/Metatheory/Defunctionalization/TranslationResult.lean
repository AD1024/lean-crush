import Crush.Metatheory.Defunctionalization.Flattened.Symbol

/-!
# Result of flattened intrinsic translation

The translated FO term is bundled with every class of generated declaration or
formula.  Keeping the lists separate preserves provenance during recursion;
`theory` supplies the single ordered theory used by semantic theorems.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

/-- An existentially packaged flattened symbol together with its declaration.
Unlike a bare `FO.SymbolDecl`, this retains the structural identity of a source
constant, application symbol, or closure occurrence. -/
structure DeclaredSymbol (signature : Signature) where
  declaration : FO.SymbolDecl
  symbol : Symbol signature declaration

namespace DeclaredSymbol

def of {signature : Signature} {declaration : FO.SymbolDecl}
    (symbol : Symbol signature declaration) : DeclaredSymbol signature :=
  ⟨declaration, symbol⟩

/-- Exact capture count when this occurrence declares a closure. -/
def closureCaptureCount? {signature : Signature}
    (declared : DeclaredSymbol signature) : Option Nat :=
  match declared with
  | ⟨_, Symbol.closure closure⟩ => some closure.captureRefs.length
  | _ => none

end DeclaredSymbol

/-- Generated declarations and formulas, separated from the translated term so
heterogeneous collections of recursive results can accumulate them uniformly. -/
structure GeneratedObligations (signature : Signature) where
  declarations : List (DeclaredSymbol signature) := []
  equations : TargetTheory signature := []
  extensionality : TargetTheory signature := []

namespace GeneratedObligations

variable {signature : Signature}

/-- Empty generated output. -/
def empty : GeneratedObligations signature := {}

/-- Record one structural symbol use.  This deliberately remains an occurrence
trace: the later finite allocator proves which repeated structural identities
share one concrete declaration. -/
def declare (generated : GeneratedObligations signature)
    (declaration : DeclaredSymbol signature) : GeneratedObligations signature :=
  { generated with
    declarations := generated.declarations ++ [declaration] }

/-- Compose generated output in source traversal order. -/
def append (left right : GeneratedObligations signature) :
    GeneratedObligations signature :=
  { declarations := left.declarations ++ right.declarations
    equations := left.equations ++ right.equations
    extensionality := left.extensionality ++ right.extensionality }

/-- Complete generated auxiliary theory in stable provenance order. -/
def theory (generated : GeneratedObligations signature) :
    TargetTheory signature :=
  generated.equations ++ generated.extensionality

end GeneratedObligations

/-- A translated intrinsic term together with all obligations generated while
translating it and its recursive subterms. -/
structure TranslationResult (signature : Signature) (context : Context) (ty : Ty) where
  term : TargetTerm signature context ty
  declarations : List (DeclaredSymbol signature) := []
  equations : TargetTheory signature := []
  extensionality : TargetTheory signature := []

namespace TranslationResult

variable {signature : Signature} {context : Context}
variable {ty newTy leftTy rightTy resultTy : Ty}

/-- Attach accumulated generated output to a translated term. -/
def ofGenerated
    (term : TargetTerm signature context ty)
    (generated : GeneratedObligations signature := {}) :
    TranslationResult signature context ty :=
  { term
    declarations := generated.declarations
    equations := generated.equations
    extensionality := generated.extensionality }

/-- Forget the result term while retaining every generated obligation. -/
def obligations (result : TranslationResult signature context ty) :
  GeneratedObligations signature where
  declarations := result.declarations
  equations := result.equations
  extensionality := result.extensionality

/-- Complete generated auxiliary theory in stable provenance order. -/
def theory (result : TranslationResult signature context ty) :
    TargetTheory signature :=
  result.obligations.theory

@[simp] theorem mem_theory (result : TranslationResult signature context ty)
    (formula : TargetSentence signature) :
    formula ∈ result.theory ↔
      formula ∈ result.equations ∨ formula ∈ result.extensionality := by
  simp [theory, obligations, GeneratedObligations.theory]

/-- Replace only the translated term while retaining every generated
declaration and obligation. -/
def replaceTerm (result : TranslationResult signature context ty)
    (term : TargetTerm signature context newTy) :
    TranslationResult signature context newTy :=
  { result with term }

/-- Combine two recursive results in source traversal order and supply the term
built from their translated subterms. -/
def combine (left : TranslationResult signature context leftTy)
    (right : TranslationResult signature context rightTy)
    (term : TargetTerm signature context resultTy) :
    TranslationResult signature context resultTy where
  term
  declarations := left.declarations ++ right.declarations
  equations := left.equations ++ right.equations
  extensionality := left.extensionality ++ right.extensionality

/-- Retain a recursive result while appending obligations generated at the
current syntax node. -/
def appendGenerated (result : TranslationResult signature context ty)
    (declarations : List (DeclaredSymbol signature) := [])
    (equations extensionality :
      TargetTheory signature := []) :
    TranslationResult signature context ty :=
  { result with
    declarations := result.declarations ++ declarations
    equations := result.equations ++ equations
    extensionality := result.extensionality ++ extensionality }

/-- Replace all generated output at once. -/
def withObligations (result : TranslationResult signature context ty)
    (generated : GeneratedObligations signature) :
    TranslationResult signature context ty :=
  { result with
    declarations := generated.declarations
    equations := generated.equations
    extensionality := generated.extensionality }

end TranslationResult

end Crush.Metatheory.Defunctionalization.Flattened
