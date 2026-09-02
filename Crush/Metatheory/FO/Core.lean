import Crush.Metatheory.HO.Core

/-!
# Intrinsically typed first-order target language

This is the proof-facing target of Crush's defunctionalization pass.  Unlike the
higher-order source language, target terms contain neither arrows, lambdas, nor a
distinguished application constructor.  Function values inhabit an opaque `.fn`
sort and application and closure construction are ordinary first-order symbols.

The representation deliberately follows the emitted SMT encoding in
`Crush.Translation.HOEncoding` and `Crush.Translation.Translate`:

* every complete source arrow type has its own function-value sort;
* its generated `app` symbol takes the function value followed by the *fully
  flattened* source arguments;
* a closure constructor takes its captured values and returns the function-value
  sort for the lambda's complete arrow type.

Keeping these generated declarations as total definitions establishes the first
correspondence between the verified language and the Crush translator. Symbol names and Lean
expression reification remain outside this core; their eventual refinement proof
must show that the emitted declarations have exactly these types.
-/

namespace Crush.Metatheory.FO

/-- First-order target sorts.  `fn domain codomain` is the opaque SMT sort used to
represent values of the complete source type `domain → codomain`.  Retaining that
source arrow identifies distinct arrow sorts without admitting arrows into FO. -/
inductive FOSort where
  | bool : FOSort
  | base : BaseSort → FOSort
  | fn : Ty → Ty → FOSort
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable, Repr

namespace FOSort

/-- Erase a source type to its first-order representation. -/
@[reducible] def ofTy : Ty → FOSort
  | .bool => .bool
  | .base baseSort => .base baseSort
  | .arrow domain codomain => .fn domain codomain

end FOSort

/-- Flatten all leading arrows in a source type.  This mirrors the Crush translator
`arrowShape?`, but dependency cannot arise in the core language. -/
@[reducible] def flattenArrow : Ty → List Ty × Ty
  | .arrow domain codomain =>
      let (domains, result) := flattenArrow codomain
      (domain :: domains, result)
  | result => ([], result)

/-- A first-order symbol declaration with a fixed argument telescope and result
sort.  Constants are precisely declarations with no arguments. -/
structure SymbolDecl where
  args : List FOSort
  result : FOSort
  deriving BEq, DecidableEq, Repr

/-- A typed de Bruijn reference to a declaration in an FO signature. -/
inductive Symbol : (signature : List SymbolDecl) → SymbolDecl → Type where
  | here {decl : SymbolDecl} {signature : List SymbolDecl} :
      Symbol (decl :: signature) decl
  | there {decl head : SymbolDecl} {signature : List SymbolDecl} :
      Symbol signature decl → Symbol (head :: signature) decl
  deriving Repr

/-- A typed de Bruijn reference to a target variable. -/
inductive Var : (context : List FOSort) → FOSort → Type where
  | here {sort : FOSort} {context : List FOSort} : Var (sort :: context) sort
  | there {sort head : FOSort} {context : List FOSort} :
      Var context sort → Var (head :: context) sort
  deriving Repr

mutual
  /-- Intrinsically typed first-order terms.  Symbol application is the only
  general term former; in particular, there is no lambda or higher-order app. -/
  inductive Term (signature : List SymbolDecl) : List FOSort → FOSort → Type where
    | var {context : List FOSort} {sort : FOSort} :
        Var context sort → Term signature context sort
    | symbol {context : List FOSort} {decl : SymbolDecl} :
        Symbol signature decl → Args signature context decl.args →
        Term signature context decl.result
    | boolLit {context : List FOSort} : Bool → Term signature context .bool
    | not {context : List FOSort} :
        Term signature context .bool → Term signature context .bool
    | and {context : List FOSort} :
        Term signature context .bool → Term signature context .bool →
        Term signature context .bool
    | or {context : List FOSort} :
        Term signature context .bool → Term signature context .bool →
        Term signature context .bool
    | imp {context : List FOSort} :
        Term signature context .bool → Term signature context .bool →
        Term signature context .bool
    | iff {context : List FOSort} :
        Term signature context .bool → Term signature context .bool →
        Term signature context .bool
    | eq {context : List FOSort} {sort : FOSort} :
        Term signature context sort → Term signature context sort →
        Term signature context .bool
    | forallE {context : List FOSort} {domain : FOSort} :
        Term signature (domain :: context) .bool → Term signature context .bool
    | existsE {context : List FOSort} {domain : FOSort} :
        Term signature (domain :: context) .bool → Term signature context .bool

  /-- A heterogeneous vector of symbol arguments indexed by the declaration's
  argument sorts. -/
  inductive Args (signature : List SymbolDecl) :
      List FOSort → List FOSort → Type where
    | nil {context : List FOSort} : Args signature context []
    | cons {context : List FOSort} {sort : FOSort} {sorts : List FOSort} :
        Term signature context sort → Args signature context sorts →
        Args signature context (sort :: sorts)
end

abbrev Signature := List SymbolDecl
abbrev Context := List FOSort
abbrev Formula (signature : Signature) (context : Context) :=
  Term signature context .bool
abbrev ClosedTerm (signature : Signature) (sort : FOSort) :=
  Term signature [] sort
abbrev Sentence (signature : Signature) := Formula signature []
abbrev Theory (signature : Signature) := List (Sentence signature)

namespace Term

def trueE {signature : Signature} {context : Context} : Formula signature context :=
  .boolLit true

def falseE {signature : Signature} {context : Context} : Formula signature context :=
  .boolLit false

def ne {signature : Signature} {context : Context} {sort : FOSort}
    (left right : Term signature context sort) : Formula signature context :=
  .not (.eq left right)

end Term

/-! ## Declarations generated by the translator's defunctionalization scheme -/

/-- The opaque target sort associated with a source arrow. -/
def arrowSort (domain codomain : Ty) : FOSort := .fn domain codomain

/-- The fully flattened declaration of the generated application symbol.

For `σ₁ → σ₂ → τ`, this has arguments
`[Fn_(σ₁→σ₂→τ), ⟦σ₁⟧, ⟦σ₂⟧]` and result `⟦τ⟧`, exactly as the Crush translator does. -/
def appDecl (domain codomain : Ty) : SymbolDecl :=
  let arrow := Ty.arrow domain codomain
  let (domains, result) := flattenArrow arrow
  { args := arrowSort domain codomain :: domains.map FOSort.ofTy
    result := FOSort.ofTy result }

/-- The declaration of a closure constructor with the given captured source
types and complete lambda arrow type. -/
@[reducible] def closureDecl (captures : List Ty) (domain codomain : Ty) : SymbolDecl :=
  { args := captures.map FOSort.ofTy
    result := arrowSort domain codomain }

@[simp] theorem flattenArrow_arrow (domain codomain : Ty) :
    flattenArrow (.arrow domain codomain) =
      (domain :: (flattenArrow codomain).1, (flattenArrow codomain).2) := rfl

@[simp] theorem appDecl_args (domain codomain : Ty) :
    (appDecl domain codomain).args =
      arrowSort domain codomain ::
        (domain :: (flattenArrow codomain).1).map FOSort.ofTy := rfl

@[simp] theorem appDecl_result (domain codomain : Ty) :
    (appDecl domain codomain).result = FOSort.ofTy (flattenArrow codomain).2 := rfl

@[simp] theorem closureDecl_args (captures : List Ty) (domain codomain : Ty) :
    (closureDecl captures domain codomain).args = captures.map FOSort.ofTy := rfl

@[simp] theorem closureDecl_result (captures : List Ty) (domain codomain : Ty) :
    (closureDecl captures domain codomain).result = arrowSort domain codomain := rfl

end Crush.Metatheory.FO
