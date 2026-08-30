/-!
# Typed higher-order core language

This is the proof-facing source language for the metatheory of lean-crush's
defunctionalization encoding. It deliberately contains only the higher-order logical
structure needed by that proof:

* opaque base sorts and Booleans;
* typed uninterpreted constants;
* nondependent function types, lambda abstraction, and application;
* Boolean connectives, typed equality, and first-order or higher-order quantification.

`Term` is intrinsically typed. Its indices record the constant signature, local
context, and result type, so malformed applications and equalities cannot be
constructed. Variables and constants use typed de Bruijn references. Keeping this
language independent of `Lean.Expr` and `Crush.SMT.Term` lets its semantics and the
defunctionalization transformation be total, pure definitions.
-/

namespace Crush.Metatheory

/-- An identifier for a base sort whose elements and operations are left abstract. -/
structure BaseSort where
  name : String
  deriving DecidableEq, Hashable, Repr

instance : BEq BaseSort := ⟨fun left right => left.name == right.name⟩

instance : LawfulBEq BaseSort where
  rfl := by
    intro sort
    cases sort with
    | mk name =>
      change (name == name) = true
      exact beq_iff_eq.mpr rfl
  eq_of_beq := by
    intro left right equal
    cases left with
    | mk leftName =>
      cases right with
      | mk rightName =>
        change (leftName == rightName) = true at equal
        cases beq_iff_eq.mp equal
        rfl

/-- Types of the higher-order core language.

Arrows are nondependent. Multiple-argument functions are represented by nested arrows,
matching Lean's curried function types before Crush optionally flattens them for SMT. -/
inductive Ty where
  | bool : Ty
  | base : BaseSort → Ty
  | arrow : Ty → Ty → Ty
  deriving BEq, DecidableEq, Hashable, Repr

/-- A local typing context, with the most recently introduced binder at its head. -/
abbrev Context := List Ty

/-- A global signature of uninterpreted constants, represented by their types.

Function constants need no separate declaration form: a constant whose type is an arrow
is an uninterpreted function. Positions distinguish constants with the same type. -/
abbrev Signature := List Ty

/-- A typed de Bruijn reference into a list of types. -/
inductive Ref : (types : List Ty) → Ty → Type where
  | here {ty : Ty} {types : List Ty} : Ref (ty :: types) ty
  | there {types : List Ty} {ty head : Ty} : Ref types ty → Ref (head :: types) ty
  deriving Repr

namespace Ref

/-- Embed a typed reference in the left side of an extended signature. -/
def inLeft {types : List Ty} {type : Ty} (ref : Ref types type)
    (tail : List Ty) : Ref (types ++ tail) type :=
  match ref with
  | .here => .here
  | .there ref => .there (ref.inLeft tail)

/-- Embed a typed reference after a newly prepended signature. -/
def inRight (head : List Ty) {types : List Ty} {type : Ty}
    (ref : Ref types type) : Ref (head ++ types) type :=
  match head with
  | [] => ref
  | _ :: head => .there (ref.inRight head)

end Ref

/-- A typed reference to a locally bound variable. -/
abbrev Var := Ref

/-- A typed reference to an uninterpreted constant in a signature. -/
abbrev Const := Ref

/-- Intrinsically typed terms and formulas.

The `.bool` terms are formulas. Quantifier bodies and Boolean connectives can therefore
only contain formulas, equality can only compare terms of the same type, and application
requires the argument type expected by the function. -/
inductive Term (signature : Signature) : Context → Ty → Type where
  | var {context : Context} {ty : Ty} : Var context ty → Term signature context ty
  | const {context : Context} {ty : Ty} : Const signature ty → Term signature context ty
  | boolLit {context : Context} : Bool → Term signature context .bool
  | not {context : Context} : Term signature context .bool → Term signature context .bool
  | and {context : Context} : Term signature context .bool → Term signature context .bool →
      Term signature context .bool
  | or {context : Context} : Term signature context .bool → Term signature context .bool →
      Term signature context .bool
  | imp {context : Context} : Term signature context .bool → Term signature context .bool →
      Term signature context .bool
  | iff {context : Context} : Term signature context .bool → Term signature context .bool →
      Term signature context .bool
  | eq {context : Context} {ty : Ty} :
      Term signature context ty → Term signature context ty →
      Term signature context .bool
  | lam {context : Context} {domain codomain : Ty} :
      Term signature (domain :: context) codomain →
      Term signature context (.arrow domain codomain)
  | app {context : Context} {domain codomain : Ty} :
      Term signature context (.arrow domain codomain) →
      Term signature context domain → Term signature context codomain
  | forallE {context : Context} {domain : Ty} :
      Term signature (domain :: context) .bool →
      Term signature context .bool
  | existsE {context : Context} {domain : Ty} :
      Term signature (domain :: context) .bool →
      Term signature context .bool

/-- A Boolean-valued term. -/
abbrev Formula (signature : Signature) (context : Context) :=
  Term signature context .bool

/-- A term with no locally bound variables. -/
abbrev ClosedTerm (signature : Signature) (ty : Ty) := Term signature [] ty

/-- A closed formula over an uninterpreted signature. -/
abbrev Sentence (signature : Signature) := Formula signature []

namespace Term

/-- Formula-level truth. -/
def trueE {signature : Signature} {context : Context} : Formula signature context :=
  .boolLit true

/-- Formula-level falsity. -/
def falseE {signature : Signature} {context : Context} : Formula signature context :=
  .boolLit false

/-- Typed disequality. -/
def ne {signature : Signature} {context : Context} {ty : Ty}
    (left right : Term signature context ty) : Formula signature context :=
  .not (.eq left right)

end Term

end Crush.Metatheory
