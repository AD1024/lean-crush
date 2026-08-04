import Lean
open Lean

/-!
# Reified simply-typed λ-calculus IR (`CSort` / `CTerm`)

This is lean-crush's intermediate logic: monomorphic, simply-typed λ-calculus
(= higher-order logic without polymorphism). Lean `Expr`s are reified into
`CTerm` (after monomorphization), the HO-elimination layer rewrites `CTerm`s, and
the translator lowers `CTerm` into `Crush.SMT.Term`.

Two representation choices worth calling out:

* The argument sort is stored on every application node (`app`), so type inference
  (`check?`) is a single unification-free bottom-up pass.
* Symbols are split into `atom` (ordinary) and `etom` (existential/Skolem,
  introduced by an encoding pass), so a later pass can tell which symbols it is
  free to reinterpret.

Well-formedness is a plain `Option`-returning `check?` rather than an inductive
family indexed by a typing derivation. The latter is what you need to *state and
prove* a verified checker's soundness theorem; since the SMT path trusts the
solver's verdict instead of replaying it through a checker, that machinery would
be dead weight here.
-/

namespace Crush.Reify

/-- Interpreted base sorts. Uninterpreted Lean types become `CSort.atom`. -/
inductive BaseSort where
  | prop
  | bool
  | nat
  | int
  | string
  | bitvec : Nat → BaseSort
  /-- The empty type; used to keep inhabitation reasoning sound. -/
  | empty
  deriving BEq, Hashable, Inhabited, Repr

/-- Reified sorts: STLC types over atoms and base sorts. No polymorphism, no
dependency (dependent function types are abstracted to `atom` during reification). -/
inductive CSort where
  | atom : Nat → CSort
  | base : BaseSort → CSort
  | func : CSort → CSort → CSort
  deriving BEq, Hashable, Inhabited, Repr

/-- The argument sorts of a (possibly nullary) function sort, in order. -/
def CSort.argTys : CSort → List CSort
  | .func a b => a :: b.argTys
  | _ => []

/-- The ultimate result sort after peeling all arrows. -/
def CSort.resTy : CSort → CSort
  | .func _ b => b.resTy
  | s => s

/-- `true` iff the sort is first-order (no arrow appears to the left of an arrow),
i.e. it can be a plain SMT function signature. -/
def CSort.isFirstOrder : CSort → Bool
  | .atom _ | .base _ => true
  | .func a b => (match a with | .func _ _ => false | _ => true) && b.isFirstOrder

/-- Interpreted constant symbols (theory literals & operators). This is where the
theory vocabulary lives; it is kept flat and extends as theories are added. -/
inductive BaseTerm where
  -- propositional / boolean
  | trueP | falseP | not | and | or | imp | iff
  | trueB | falseB
  -- equality, quantifiers, ite are sort-indexed
  | eq      : CSort → BaseTerm
  | forallE : CSort → BaseTerm
  | existsE : CSort → BaseTerm
  | ite     : CSort → BaseTerm
  -- numerals & literals
  | natLit : Nat → BaseTerm
  | intLit : Int → BaseTerm
  | strLit : String → BaseTerm
  | bvLit  : (width : Nat) → (value : Nat) → BaseTerm
  -- opaque theory operator, resolved by a translation handler via its name.
  -- Lets the reifier stay agnostic about the growing operator set: it records
  -- *which* Lean constant this is, and the translator's handlers decide the SMT.
  | op     : Name → BaseTerm
  deriving BEq, Hashable, Inhabited, Repr

/-- Reified terms. de Bruijn indices for bound variables. -/
inductive CTerm where
  | atom : Nat → CTerm
  | etom : Nat → CTerm
  | base : BaseTerm → CTerm
  | bvar : Nat → CTerm
  | lam  : CSort → CTerm → CTerm
  /-- Application; the `CSort` is the *argument* sort (see module docs). -/
  | app  : CSort → CTerm → CTerm → CTerm
  deriving BEq, Hashable, Inhabited, Repr

/-- Head-spine view: peel off a left-nested application into (head, args). -/
def CTerm.spine (t : CTerm) : CTerm × Array CTerm :=
  go t #[]
where
  go : CTerm → Array CTerm → CTerm × Array CTerm
  | .app _ f a, acc => go f (acc.push a)
  | h, acc => (h, acc.reverse)

end Crush.Reify
