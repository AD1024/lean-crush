import Crush.Metatheory.Defunctionalization.Flattened.Symbol

/-!
# Result of flattened higher-order translation

The translated FO term is bundled with every class of generated declaration or
formula. Keeping the lists separate records what produced each formula and
keeps source traversal order; `theory` supplies the single ordered theory used
by semantic theorems.
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
structure AuxiliaryTheory (signature : Signature) where
  declarations : List (DeclaredSymbol signature) := []
  equations : TargetTheory signature := []
  extensionality : TargetTheory signature := []

namespace AuxiliaryTheory

variable {signature : Signature}

/-- Empty generated output. -/
def empty : AuxiliaryTheory signature := {}

/-- Record one structural symbol use. Repeated uses remain in this list; the
later finite allocator proves which uses share one concrete declaration. -/
def declare (generated : AuxiliaryTheory signature)
    (declaration : DeclaredSymbol signature) : AuxiliaryTheory signature :=
  { generated with
    declarations := generated.declarations ++ [declaration] }

/-- Compose generated output in source traversal order. -/
def append (left right : AuxiliaryTheory signature) :
    AuxiliaryTheory signature :=
  { declarations := left.declarations ++ right.declarations
    equations := left.equations ++ right.equations
    extensionality := left.extensionality ++ right.extensionality }

/-- Generated equations followed by generated extensionality formulas. -/
def theory (generated : AuxiliaryTheory signature) :
    TargetTheory signature :=
  generated.equations ++ generated.extensionality

end AuxiliaryTheory

/-- A translated typed term together with the declarations, closure
equations, and function-extensionality formulas generated for it and its
subterms. -/
structure TermTranslation (signature : Signature) (context : Context) (ty : Ty) where
  term : TargetTerm signature context ty
  declarations : List (DeclaredSymbol signature) := []
  equations : TargetTheory signature := []
  extensionality : TargetTheory signature := []

namespace TermTranslation

variable {signature : Signature} {context : Context}
variable {ty newTy leftTy rightTy resultTy : Ty}

/-- Attach accumulated generated output to a translated term. -/
def ofGenerated
    (term : TargetTerm signature context ty)
    (generated : AuxiliaryTheory signature := {}) :
    TermTranslation signature context ty :=
  { term
    declarations := generated.declarations
    equations := generated.equations
    extensionality := generated.extensionality }

/-- Forget the translated term and collect the rest of the generated output. -/
def generated (result : TermTranslation signature context ty) :
  AuxiliaryTheory signature where
  declarations := result.declarations
  equations := result.equations
  extensionality := result.extensionality

/-- Generated equations followed by generated extensionality formulas. -/
def theory (result : TermTranslation signature context ty) :
    TargetTheory signature :=
  result.generated.theory

@[simp] theorem mem_theory (result : TermTranslation signature context ty)
    (formula : TargetSentence signature) :
    formula ∈ result.theory ↔
      formula ∈ result.equations ∨ formula ∈ result.extensionality := by
  simp [theory, generated, AuxiliaryTheory.theory]

/-- Replace only the translated term while retaining all other generated output. -/
def replaceTerm (result : TermTranslation signature context ty)
    (term : TargetTerm signature context newTy) :
    TermTranslation signature context newTy :=
  { result with term }

/-- Combine two recursive results in source traversal order and supply the term
built from their translated subterms. -/
def combine (left : TermTranslation signature context leftTy)
    (right : TermTranslation signature context rightTy)
    (term : TargetTerm signature context resultTy) :
    TermTranslation signature context resultTy where
  term
  declarations := left.declarations ++ right.declarations
  equations := left.equations ++ right.equations
  extensionality := left.extensionality ++ right.extensionality

/-- Retain a recursive result while appending output from the current syntax node. -/
def appendOutput (result : TermTranslation signature context ty)
    (declarations : List (DeclaredSymbol signature) := [])
    (equations extensionality :
      TargetTheory signature := []) :
    TermTranslation signature context ty :=
  { result with
    declarations := result.declarations ++ declarations
    equations := result.equations ++ equations
    extensionality := result.extensionality ++ extensionality }

/-- Replace all generated output at once. -/
def withAuxiliaryTheory (result : TermTranslation signature context ty)
    (generated : AuxiliaryTheory signature) :
    TermTranslation signature context ty :=
  { result with
    declarations := generated.declarations
    equations := generated.equations
    extensionality := generated.extensionality }

end TermTranslation

end Crush.Metatheory.Defunctionalization.Flattened
