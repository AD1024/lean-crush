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
* The default defunctionalizing pipeline removes higher-order function values
  upstream (see `Crush/Translation/HOEncoding.lean`). Direct higher-order mode
  may instead emit `Term.lam` for a capable backend. The proved lowering
  metatheory selects the first-order subset explicitly.
* The SMT sort type is named `SSort` (not `Sort`) to avoid clashing with Lean's
  universe keyword.
-/

namespace Crush.SMT

/-- An SMT identifier: a plain symbol or an indexed identifier `(_ s i₀ i₁ …)`. -/
inductive Ident where
  | symb    : String → Ident
  | indexed : String → Array (String ⊕ Nat) → Ident
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Whether an identifier is an SMT-LIB built-in sort constructor recognized
by the shared syntax and checker. -/
def Ident.isBuiltinSort : Ident → Bool
  | .symb "Bool" | .symb "Int" | .symb "String"
  | .symb "Array" | .symb "->" => true
  | .indexed "BitVec" #[.inr _] => true
  | _ => false

/-- Fixed arity of a recognized SMT-LIB built-in sort constructor. The
variadic function sort `->` and unknown identifiers both return `none`;
`isBuiltinSort` distinguishes those cases. -/
def Ident.builtinSortArity? : Ident → Option Nat
  | .symb "Bool" | .symb "Int" | .symb "String" => some 0
  | .symb "Array" => some 2
  | .symb "->" => none
  | .indexed "BitVec" #[.inr _] => some 0
  | _ => none

/-- An SMT sort: a bound parameter in a parametric sort declaration or an
applied sort constructor `(S s₀ … sₙ)`. Nullary constructors render as bare
symbols. The proved monomorphic fragment never uses `bvar`. -/
inductive SSort where
  | bvar : Nat → SSort
  | app  : Ident → Array SSort → SSort
  deriving BEq, Inhabited, Repr

/-- Shallow quotation for a nullary SMT sort symbol. -/
syntax "(smtSort|" ident ")" : term

macro_rules
  | `(term| (smtSort| $name:ident)) =>
      `(SSort.app (.symb $(quote name.getId.toString)) #[])

/-- Standard nullary SMT Boolean sort. -/
def boolSort : SSort := (smtSort| Bool)

/-- Standard nullary SMT integer sort. -/
def intSort : SSort := (smtSort| Int)

/-- Standard nullary SMT string sort. -/
def stringSort : SSort := (smtSort| String)

/-- SMT bit-vector sort of a fixed width. -/
def bitvecSort (width : Nat) : SSort :=
  .app (.indexed "BitVec" #[.inr width]) #[]

namespace SSort

mutual
  /-- Structural size of one SMT sort, used to justify recursion through
  compound sort arguments. -/
  def structuralSize : SSort → Nat
    | .bvar _ => 1
    | .app _ arguments => listStructuralSize arguments.toList + 1

  /-- Structural size of a list of SMT sorts. -/
  def listStructuralSize : List SSort → Nat
    | [] => 0
    | sort :: sorts => structuralSize sort + listStructuralSize sorts + 1
end

/- Executable equality for the nested recursive sort syntax. Lean's standard
deriver does not recurse through `Array`, so the list helper makes the structural
decrease explicit. -/
mutual
  def decEq : (left right : SSort) → Decidable (left = right)
    | .bvar left, .bvar right =>
      if equal : left = right then
        isTrue (by cases equal; rfl)
      else
        isFalse fun assumed => by
          cases assumed
          exact equal rfl
    | .bvar _, .app _ _ | .app _ _, .bvar _ => isFalse nofun
    | .app leftName leftArgs, .app rightName rightArgs =>
      if namesEqual : leftName = rightName then
        match listDecEq leftArgs.toList rightArgs.toList with
        | isFalse different => isFalse fun equal => by
            injection equal with _ argsEqual
            exact different (congrArg Array.toList argsEqual)
        | isTrue argsEqual => isTrue (by
            cases namesEqual
            have arraysEqual := Array.toList_inj.mp argsEqual
            cases arraysEqual
            rfl)
      else
        isFalse fun equal => by
          injection equal with equalNames
          exact namesEqual equalNames
  termination_by left right => structuralSize left + structuralSize right
  decreasing_by all_goals simp [structuralSize] <;> omega

  def listDecEq : (left right : List SSort) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse nofun
    | left :: lefts, right :: rights =>
      match decEq left right with
      | isFalse different => isFalse fun equal => by
          injection equal with headEqual
          exact different headEqual
      | isTrue headEqual =>
        match listDecEq lefts rights with
        | isFalse different => isFalse fun equal => by
            injection equal with _ tailEqual
            exact different tailEqual
        | isTrue tailEqual => isTrue (by cases headEqual; cases tailEqual; rfl)
  termination_by left right => listStructuralSize left + listStructuralSize right
  decreasing_by all_goals simp [listStructuralSize] <;> omega
end

end SSort

instance : DecidableEq SSort := SSort.decEq

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
        `defunctionalize` mode never produces one. -/
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

namespace Term

mutual
  /-- Structural size of one SMT term. This measure is shared by total
  recursive operations over the array-nested term syntax. -/
  def structuralSize : Term → Nat
    | .lit _ | .bvar _ => 1
    | .app _ arguments => listStructuralSize arguments.toList + 1
    | .letE bindings body =>
        bindingListStructuralSize bindings.toList + structuralSize body + 1
    | .forallE _ body | .existsE _ body | .lam _ body => structuralSize body + 1
    | .annot body attributes =>
        structuralSize body + attrListStructuralSize attributes.toList + 1

  /-- Structural size of one SMT term attribute. -/
  def attrStructuralSize : Attr → Nat
    | .named _ | .keyword _ _ => 1
    | .pattern terms => listStructuralSize terms.toList + 1

  /-- Structural size of a list of SMT terms. -/
  def listStructuralSize : List Term → Nat
    | [] => 0
    | term :: terms => structuralSize term + listStructuralSize terms + 1

  /-- Structural size of a list of SMT term attributes. -/
  def attrListStructuralSize : List Attr → Nat
    | [] => 0
    | attr :: attributes =>
        attrStructuralSize attr + attrListStructuralSize attributes + 1

  /-- Structural size of simultaneous SMT `let` bindings. -/
  def bindingListStructuralSize : List (String × Term) → Nat
    | [] => 0
    | (_, term) :: bindings =>
        structuralSize term + bindingListStructuralSize bindings + 1
end

end Term

/-- A datatype constructor declaration with its selectors. -/
structure CtorDecl where
  name     : String
  /-- `(selectorName, selectorSort)` pairs. -/
  selDecls : Array (String × SSort)
  deriving DecidableEq, Inhabited, Repr

/-- A (possibly parametric) datatype body. -/
structure DatatypeDecl where
  params : Array String := #[]
  ctors  : Array CtorDecl
  deriving DecidableEq, Inhabited, Repr

/-- One SMT function definition, used either alone by `define-fun` or in a
mutually recursive `define-funs-rec` group. -/
structure FunDef where
  name    : String
  args    : Array (String × SSort)
  resSort : SSort
  body    : Term
  deriving Inhabited, Repr

/-- Top-level SMT-LIB commands we can emit. -/
inductive Command where
  | setLogic   : String → Command
  | setOption  : String → String → Command
  | declSort   : (name : String) → (arity : Nat) → Command
  | declFun    : (name : String) → (argSorts : Array SSort) → (resSort : SSort) → Command
  /-- A nonrecursive SMT-LIB `define-fun`. Recursive definitions use
      `defFunsRec`, including singleton recursive groups. -/
  | defFun     : FunDef → Command
  | defFunsRec : Array FunDef → Command
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
