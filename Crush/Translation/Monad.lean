import Lean
import Crush.SMT.Syntax
import Crush.Frontend.Config
open Lean

/-!
# The translation monad `TranslateM`

`TranslateM` is the shared context in which a Lean `Expr` is turned into a
`Crush.SMT.Term`. It is the monad that **user translation metaprograms run in**,
so its public surface is part of lean-crush's extension API and must stay stable
and ergonomic.

Responsibilities:
* Allocate and remember SMT symbols for Lean atoms (sorts, constants, e-vars),
  keeping a bijective high↔low name map like lean-auto's `IR.SMT.State`.
* Accumulate the `Command` list (declarations, definitions, assertions).
* Provide the recursive entry points (`emitSort`, `emitTerm`) that user handlers
  call to translate sub-expressions, so a handler can translate a constant while
  delegating its arguments back to the default machinery.
* Track provenance so `:named` assertions map back to source lemmas for unsat
  cores and error reporting.
-/

namespace Crush

open SMT

/-- A high-level construct we assign a stable SMT symbol to. Kept abstract from
the printer; only the name map cares about identity. -/
inductive Atom where
  /-- A Lean type mapped to an SMT sort. Keyed by a canonical `Expr`. -/
  | sort  : Expr → Atom
  /-- A Lean constant/fvar mapped to an SMT function symbol. -/
  | fn    : Expr → Atom
  /-- A fresh existential/Skolem symbol introduced by encoding. -/
  | fresh : Nat → Atom
  deriving Inhabited

/-- Provenance for an emitted assertion, used for unsat-core reporting. -/
structure FactSource where
  /-- Stable id embedded in the `:named` attribute (`crush_fact_<id>`). -/
  id       : Nat
  /-- The Lean proof term whose type this assertion encodes (if any). -/
  proof    : Option Expr := none
  /-- Human-readable origin for diagnostics. -/
  descr    : String
  deriving Inhabited

/-- Mutable translation state. -/
structure TranslateState where
  cfg        : Config
  /-- Bijection between high-level atoms and emitted SMT symbols. -/
  atomToName : Std.HashMap String String := {}
  nameToAtom : Std.HashMap String String := {}
  /-- Name-collision counter, mirroring lean-auto's `usedNames`. -/
  usedNames  : Std.HashMap String Nat := {}
  /-- Emitted commands, in order. -/
  commands   : Array SMT.Command := #[]
  /-- Provenance table indexed by fact id. -/
  facts      : Array FactSource := #[]
  /-- Counter for fresh Skolem/e-vars. -/
  nextFresh  : Nat := 0
  deriving Inhabited

/-- The translation monad. `MetaM` at the bottom gives us `whnf`, unification,
instance synthesis, and access to the environment — everything a user handler
needs to inspect the term it is translating. -/
abbrev TranslateM := StateRefT TranslateState MetaM

namespace TranslateM

def run {α : Type} (cfg : Config) (x : TranslateM α) : MetaM (α × TranslateState) :=
  StateRefT'.run x { cfg := cfg }

@[inline] def getConfig : TranslateM Config := return (← get).cfg

/-- Emit a command into the running script. -/
def emitCommand (c : SMT.Command) : TranslateM Unit :=
  modify fun s => { s with commands := s.commands.push c }

/-- Allocate a fresh internal symbol not tied to any Lean atom. -/
def freshSymbol (hint : String := "x") : TranslateM String := do
  let n := (← get).nextFresh
  modify fun s => { s with nextFresh := n + 1 }
  sanitizeAndReserve s!"{hint}_{n}"
where
  /-- Turn an arbitrary hint into a legal, collision-free SMT symbol. -/
  sanitizeAndReserve (hint : String) : TranslateM String := do
    let base := sanitize hint
    let used := (← get).usedNames
    match used.get? base with
    | some k =>
      modify fun s => { s with usedNames := s.usedNames.insert base (k + 1) }
      return s!"{base}_{k}"
    | none =>
      modify fun s => { s with usedNames := s.usedNames.insert base 0 }
      return base
  sanitize (s : String) : String :=
    let ok (c : Char) := c.isAlphanum || "~!@$%^&*_-+=<>.?/".contains c
    let s := String.ofList (s.toList.map (fun c => if ok c then c else '_'))
    let s := if s.isEmpty || s.front.isDigit then "cr_" ++ s else s
    s

/-- Look up or allocate the SMT symbol for a high-level atom, keyed by a string
identity `key` (typically the atom's pretty/canonical form). `hint` seeds the
generated name. Idempotent. -/
def symbolFor (key : String) (hint : String) : TranslateM String := do
  match (← get).atomToName.get? key with
  | some name => return name
  | none =>
    let name ← freshSymbol hint
    modify fun s => { s with
      atomToName := s.atomToName.insert key name
      nameToAtom := s.nameToAtom.insert name key }
    return name

/-- Register an emitted assertion's provenance, returning the fact id to embed in
its `:named` attribute. -/
def recordFact (descr : String) (proof : Option Expr := none) : TranslateM Nat := do
  let id := (← get).facts.size
  modify fun s => { s with facts := s.facts.push { id, proof, descr } }
  return id

end TranslateM

end Crush
