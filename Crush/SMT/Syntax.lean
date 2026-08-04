import Lean
open Lean

/-!
# SMT-LIB 2.6 Abstract Syntax

A typed representation of the fragment of SMT-LIB we emit and parse. This is the
*target language* of translation: everything upstream (reification, HO encoding,
user annotations) ultimately produces `Crush.SMT.Command`s.

Design notes:
* We keep sorts, terms, and commands as plain inductives with `ToString`, but we
  additionally derive `Repr` everywhere so failures print structurally.
* `Term` carries an optional annotation slot (`.annot`) used for `:named`
  bindings so we can recover unsat-core provenance without string surgery.
* Higher-order function *values* never appear here — they are eliminated upstream
  by the encoding layer (see `Crush/Translation/HOEncoding.lean`). This module is
  deliberately first-order so that it maps 1:1 onto what solvers accept.
* The SMT sort type is named `SSort` (not `Sort`) to avoid clashing with Lean's
  universe keyword.
-/

namespace Crush.SMT

/-- An SMT identifier: a plain symbol or an indexed identifier `(_ s i₀ i₁ …)`. -/
inductive Ident where
  | symb    : String → Ident
  | indexed : String → Array (String ⊕ Nat) → Ident
  deriving BEq, Inhabited, Repr

/-- An SMT sort: a bound variable (only inside `define-sort`) or an applied sort
constructor `(S s₀ … sₙ)`. Nullary constructors render as bare symbols. -/
inductive SSort where
  | bvar : Nat → SSort
  | app  : Ident → Array SSort → SSort
  deriving BEq, Inhabited, Repr

/-- Literal constants. `TODO(reals/floats)` tracked in the implementation plan. -/
inductive Literal where
  | str    : String → Literal
  | num    : Nat → Literal
  | bitvec : (width : Nat) → (value : Nat) → Literal
  | bool   : Bool → Literal
  deriving BEq, Inhabited, Repr

mutual
  /-- SMT terms. De Bruijn indices are used for `forall`/`exists`/`let`-bound
  variables (`bvar`). Free symbols are `app`s with an empty argument array. -/
  inductive Term where
    | lit     : Literal → Term
    | bvar    : Nat → Term
    | app     : Ident → Array Term → Term
    | letE    : Array (String × Term) → Term → Term
    | forallE : Array (String × SSort) → Term → Term
    | existsE : Array (String × SSort) → Term → Term
    /-- A higher-order `lambda` term. Only legal for HO-capable backends under a
        `HO_`-prefixed logic (see `Crush/Translation/HOEncoding.lean`); the
        `defunctionalize`/`combinators` modes never produce one. -/
    | lam     : Array (String × SSort) → Term → Term
    | annot   : Term → Array Attr → Term
    deriving Inhabited, Repr

  /-- SMT-LIB `:keyword value` attributes (used for `:named`, patterns, etc.). -/
  inductive Attr where
    | named   : String → Attr
    | pattern : Array Term → Attr
    | keyword : String → Option String → Attr
    deriving Inhabited, Repr
end

/-- A datatype constructor declaration with its selectors. -/
structure CtorDecl where
  name     : String
  /-- `(selectorName, selectorSort)` pairs. -/
  selDecls : Array (String × SSort)
  deriving Inhabited, Repr

/-- A (possibly parametric) datatype body. -/
structure DatatypeDecl where
  params : Array String := #[]
  ctors  : Array CtorDecl
  deriving Inhabited, Repr

/-- Top-level SMT-LIB commands we can emit. -/
inductive Command where
  | setLogic   : String → Command
  | setOption  : String → String → Command
  | declSort   : (name : String) → (arity : Nat) → Command
  | defSort    : (name : String) → (params : Array String) → (body : SSort) → Command
  | declFun    : (name : String) → (argSorts : Array SSort) → (resSort : SSort) → Command
  | defFun     : (rec_ : Bool) → (name : String) → (args : Array (String × SSort)) →
                   (resSort : SSort) → (body : Term) → Command
  | declDatatypes : Array (String × Nat × DatatypeDecl) → Command
  | assert     : Term → Command
  | checkSat   : Command
  | getModel   : Command
  | getProof   : Command
  | getUnsatCore : Command
  | echo       : String → Command
  | exit       : Command
  deriving Inhabited, Repr

/-- Convenience: apply a symbol by name. -/
def Term.symbApp (s : String) (args : Array Term) : Term := .app (.symb s) args

/-- Convenience: a nullary symbol reference. -/
def Term.const (s : String) : Term := .app (.symb s) #[]

end Crush.SMT
