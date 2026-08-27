import Lean
import Crush.SMT.Syntax
import Crush.Metatheory.Bridge.Command
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
  keeping a bijective high↔low name map.
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

/-- A collision-free identity for generated SMT symbols whose meaning depends on
Lean expressions. Structural `Expr` equality includes universe levels and never
elides deep terms, unlike pretty-printing. `tag` separates distinct symbol roles
that happen to use the same expressions.

Types need stronger normalization than terms: reducible aliases and projections
can give definitionally equal types different syntax, but they must still map to
one SMT sort. Put those expressions in `typeExprs`; ordinary term identity stays
in `exprs` and is not unfolded. -/
structure StructuralKey where
  tag       : String
  name      : Name := .anonymous
  exprs     : Array Expr := #[]
  typeExprs : Array Expr := #[]
  deriving BEq, Hashable

/-- Proof-carrying history of expression-derived symbol allocation.

`structuralToName` is the executable lookup table.  This trace is its small
proof-facing companion: every newly allocated structural identity is recorded,
and its projected SMT name list is intrinsically duplicate-free.  Consequently
two distinct recorded allocations can never be represented by the same SMT
symbol.  Reusing an existing key does not append another allocation. -/
structure StructuralAllocationTrace where
  entries : List (StructuralKey × String)
  namesNodup : (entries.map Prod.snd).Nodup

instance : Inhabited StructuralAllocationTrace where
  default := { entries := [], namesNodup := by simp }

namespace StructuralAllocationTrace

private theorem pair_eq_of_snd_eq_of_nodup
    {α β : Type} {entries : List (α × β)} {left right : α × β}
    (nodup : (entries.map Prod.snd).Nodup)
    (leftMem : left ∈ entries) (rightMem : right ∈ entries)
    (sameName : left.2 = right.2) : left = right := by
  induction entries <;> grind

/-- Extend an allocation trace with a name proved fresh for that trace. -/
def cons (trace : StructuralAllocationTrace) (key : StructuralKey) (name : String)
    (fresh : name ∉ trace.entries.map Prod.snd) : StructuralAllocationTrace where
  entries := (key, name) :: trace.entries
  namesNodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨fresh, trace.namesNodup⟩

/-- A name occurs at most once in the structural allocation history. -/
theorem uniqueName (trace : StructuralAllocationTrace) :
    trace.entries.map Prod.snd |>.Nodup :=
  trace.namesNodup

/-- The allocation trace is injective: equality of emitted names identifies the
same structural allocation, and hence the same normalized structural key. -/
theorem entry_eq_of_name_eq (trace : StructuralAllocationTrace)
    {left right : StructuralKey × String}
    (leftMem : left ∈ trace.entries) (rightMem : right ∈ trace.entries)
    (sameName : left.2 = right.2) : left = right :=
  pair_eq_of_snd_eq_of_nodup trace.namesNodup leftMem rightMem sameName

theorem key_eq_of_name_eq (trace : StructuralAllocationTrace)
    {leftKey rightKey : StructuralKey} {leftName rightName : String}
    (leftMem : (leftKey, leftName) ∈ trace.entries)
    (rightMem : (rightKey, rightName) ∈ trace.entries)
    (sameName : leftName = rightName) : leftKey = rightKey := by
  have := trace.entry_eq_of_name_eq leftMem rightMem sameName
  exact congrArg Prod.fst this

end StructuralAllocationTrace

/-- Semantic identity for a symbol derived from an already allocated SMT symbol. -/
structure DerivedSymbolKey where
  tag    : String
  parent : String
  member : Name := .anonymous
  index  : Option Nat := none
  deriving BEq, Hashable

/-- Provenance for an emitted assertion, used for unsat-core reporting. -/
structure FactSource where
  /-- Stable id embedded in the `:named` attribute (`crush_fact_<id>`). -/
  id       : Nat
  /-- The Lean proof term whose type this assertion encodes (if any). -/
  proof    : Option Expr := none
  /-- The source proposition translated into the named assertion. Retained so an
      internal SMT sort error can report the exact Lean expression. -/
  prop     : Option Expr := none
  /-- For a normalized negated goal, converts the original `¬goal` hypothesis
      introduced during Alethe replay into the translated proposition. -/
  negationTransform : Option Expr := none
  /-- Specialized equality from the original negated goal to its normalized
      assertion, always supplied to core-directed reconstruction. -/
  reconstructionProof : Option Expr := none
  /-- Quantified parent proof retained as provenance for a generated instance. -/
  instanceOf : Option Expr := none
  /-- Human-readable origin for diagnostics. -/
  descr    : String
  deriving Inhabited

/-- Handler-registry lookups resolved once per `TranslateM.run`.

The persistent extensions store declaration names, but `emitSort` and `emitTerm` consult
them on every node. The environment cannot change during one translation, so evaluated
handler closures are stored here as type-tagged `Dynamic` values and reused. -/
structure RegistryCache where
  translation     : Option (Array Dynamic) := none
  sort            : Option (Array Dynamic) := none
  lowerings       : Std.HashMap Name (Array Dynamic) := {}
  certifiedLowerings : Std.HashMap Name (Array Dynamic) := {}
  resultLowerings : Std.HashMap Name (Array Dynamic) := {}
  hasTranslation  : Option Bool := none
  hasSort         : Option Bool := none
  hasResult       : Option Bool := none
  deriving Inhabited

/-- Auditable link from one retained defunctionalization command certificate to
the structural symbols whose allocation it relies on. Links are created only by
`emitCertifiedStructuralCommand`, after checking every name against the
proof-carrying allocation trace. -/
structure DefunAllocationLink where
  certificateIndex : Nat
  symbols : Array String
  allocation : StructuralAllocationTrace
  symbolsAllocated : ∀ symbol ∈ symbols.toList,
    symbol ∈ allocation.entries.map Prod.snd

/-- One successful dispatch through the restricted certified primitive registry. -/
structure CertifiedHookUse where
  declaration : Name
  targetSymbol : String
  deriving Inhabited, Repr

/-- Mutable translation state. -/
structure TranslateState where
  cfg        : Config
  /-- Bijection between high-level atoms and emitted SMT symbols. -/
  atomToName : Std.HashMap String String := {}
  /-- Structural identities for expression-derived symbols. Kept separate from
      `atomToName`, whose string keys are part of the user extension API. -/
  structuralToName : Std.HashMap StructuralKey String := {}
  /-- Auditable, proof-carrying allocation history for `structuralToName`. -/
  structuralAllocations : StructuralAllocationTrace := default
  nameToAtom : Std.HashMap String String := {}
  /-- Emitted SMT symbol → the Lean term it stands for.

      `nameToAtom` records only a diagnostic label, which cannot be turned back
      into an `Expr`. Proof replay
      (`Crush/Solver/AletheReplay.lean`) needs the real term: an Alethe proof mentions
      the emitted symbols, and each step has to be restated as a Lean proposition. This
      map is the inverse direction, populated where a symbol is allocated for a Lean
      head (`defaultApp`). Absence is not an error — a symbol with no recorded term
      simply makes replay decline that step. -/
  nameToExpr : Std.HashMap String Expr := {}
  /-- Name-collision counter: how many times each sanitized base name is taken. -/
  usedNames  : Std.HashMap String Nat := {}
  /-- Requested derived symbol → collision-free allocated symbol. -/
  derivedNames : Std.HashMap String String := {}
  /-- Semantic derived-symbol identity → collision-free allocated symbol. -/
  derivedSymbols : Std.HashMap DerivedSymbolKey String := {}
  /-- Emitted commands, in order. -/
  commands   : Array SMT.Command := #[]
  /-- Proof-carrying declarations emitted by the live defunctionalization path. -/
  defunCertificates : Array Metatheory.Bridge.CommandCertificate := #[]
  /-- Checked structural-name dependencies of `defunCertificates`. -/
  defunAllocationLinks : Array DefunAllocationLink := #[]
  /-- Type-erased dependent `LiveCertifiedClosure` proofs, referenced by
  `ClosureEquationCertificate.verifiedClosureIndex`. -/
  verifiedClosures : Array Dynamic := #[]
  /-- Type-erased identity-bearing semantic certificates for live source symbols. -/
  verifiedConstants : Array Dynamic := #[]
  /-- Auditable successful uses of proof-carrying primitive mappings. -/
  certifiedHookUses : Array CertifiedHookUse := #[]
  /-- Provenance table indexed by fact id. -/
  facts      : Array FactSource := #[]
  /-- Counter for fresh Skolem/e-vars. -/
  nextFresh  : Nat := 0
  /-- Lean fvars currently bound by an SMT quantifier, mapped to their SMT
      variable name. Consulted by the translator before treating an fvar as an
      uninterpreted symbol, so quantified variables render as references rather
      than fresh `declare-fun`s. -/
  boundVars  : Std.HashMap FVarId String := {}
  /-- Higher-order encoding bookkeeping (`Translation/HOEncoding.lean`).

      A function-typed *bound* variable cannot be a `declare-fun` — it is a value
      of an `Fn` sort, applied via that sort's `app` symbol. This records, for each
      such variable, the `app` symbol to route its applications through, keyed the
      same way as `boundVars`. -/
  funVars    : Std.HashMap FVarId String := {}
  /-- Registry lookups already resolved during this run. -/
  registries : RegistryCache := {}
  deriving Inhabited

/-- The translation monad. `MetaM` at the bottom gives us `whnf`, unification,
instance synthesis, and access to the environment — everything a user handler
needs to inspect the term it is translating. -/
abbrev TranslateM := StateRefT TranslateState MetaM

/-- Test definitional equality without retaining metavariable assignments. -/
def isDefEqReadOnly (left right : Expr) : MetaM Bool :=
  withoutModifyingState do
    Meta.isDefEqGuarded left right

namespace TranslateM

def run {α : Type} (cfg : Config) (x : TranslateM α) : MetaM (α × TranslateState) :=
  StateRefT'.run x { cfg := cfg }

@[inline] def getConfig : TranslateM Config := return (← get).cfg

/-- Emit a command into the running script. -/
def emitCommand (c : SMT.Command) : TranslateM Unit :=
  modify fun s => { s with commands := s.commands.push c }

/-- Atomically emit the command stored in a defunctionalization certificate and
retain that same certificate. This rules out command/certificate drift in the
stateful production path. -/
def emitCertifiedCommand
    (certificate : Metatheory.Bridge.CommandCertificate) : TranslateM Unit :=
  modify fun s => { s with
    commands := s.commands.push certificate.command
    defunCertificates := s.defunCertificates.push certificate }

/-- Emit a certified command only when all of its structural symbol dependencies
have already been allocated and recorded in the uniqueness trace. The command,
certificate, and dependency link are appended atomically. -/
def emitCertifiedStructuralCommand
    (certificate : Metatheory.Bridge.CommandCertificate) : TranslateM Unit := do
  let symbols := certificate.structuralSymbols
  let state ← get
  let allocatedNames := state.structuralAllocations.entries.map Prod.snd
  if allocated : ∀ symbol ∈ symbols.toList, symbol ∈ allocatedNames then
    let index := state.defunCertificates.size
    modify fun s => { s with
      commands := s.commands.push certificate.command
      defunCertificates := s.defunCertificates.push certificate
      defunAllocationLinks := s.defunAllocationLinks.push {
        certificateIndex := index
        symbols
        allocation := state.structuralAllocations
        symbolsAllocated := allocated } }
  else
    let missing := symbols.filter fun symbol => !allocatedNames.contains symbol
    throwError
      "crush: internal certified command refers to unallocated structural symbols: {missing}"

def recordVerifiedClosure (certificate : Dynamic) : TranslateM Nat := do
  let index := (← get).verifiedClosures.size
  modify fun s => { s with verifiedClosures := s.verifiedClosures.push certificate }
  return index

def recordVerifiedConstant (certificate : Dynamic) : TranslateM Nat := do
  let index := (← get).verifiedConstants.size
  modify fun s => { s with verifiedConstants := s.verifiedConstants.push certificate }
  return index

def recordCertifiedHookUse (declaration : Name) (targetSymbol : String) :
    TranslateM Unit :=
  modify fun s => { s with certifiedHookUses := s.certifiedHookUses.push {
    declaration
    targetSymbol } }

private def sanitizeSymbol (s : String) : String :=
  -- The same alphabet the printer accepts unquoted (`Print.simpleSymbolSpecials`).
  let ok (c : Char) := c.isAlphanum || "~!@%^&*_-+=<>.?/".contains c
  let s := String.ofList (s.toList.map (fun c => if ok c then c else '_'))
  if s.isEmpty || s.front.isDigit then "cr_" ++ s else s

/-- Turn an arbitrary hint into a legal, collision-free SMT symbol. -/
private def reserveSymbol (hint : String) : TranslateM String := do
  let base := sanitizeSymbol hint
  let used := (← get).usedNames
  if !used.contains base then
    modify fun s => { s with usedNames := s.usedNames.insert base 0 }
    return base
  else
    let rec findUnused : Nat → Nat → String × Nat
      | 0, k => (s!"{base}_{k}", k + 1)
      | fuel + 1, k =>
        let candidate := s!"{base}_{k}"
        if used.contains candidate then
          findUnused fuel (k + 1)
        else
          (candidate, k + 1)
    let (name, next) := findUnused (used.size + 1) (used.getD base 0)
    modify fun s => { s with usedNames :=
      (s.usedNames.insert base next).insert name 0 }
    return name

/-- Allocate a fresh internal symbol not tied to any Lean atom. -/
def freshSymbol (hint : String := "x") : TranslateM String := do
  let n := (← get).nextFresh
  modify fun s => { s with nextFresh := n + 1 }
  reserveSymbol s!"{hint}_{n}"

/-- Allocate a stable symbol for a semantic derived-symbol identity. -/
def reserveDerivedFor (key : DerivedSymbolKey) (hint : String) : TranslateM String := do
  if let some allocated := (← get).derivedSymbols.get? key then
    return allocated
  let allocated ← reserveSymbol hint
  modify fun s => { s with derivedSymbols := s.derivedSymbols.insert key allocated }
  return allocated

/-- Allocate a stable symbol identified by its requested name. -/
def reserveDerived (name : String) : TranslateM String := do
  if let some allocated := (← get).derivedNames.get? name then
    return allocated
  let allocated ← reserveSymbol name
  modify fun s => { s with derivedNames := s.derivedNames.insert name allocated }
  return allocated

/-- Look up or allocate an SMT symbol for a user-provided or internal string key.
Expression-derived identities must use `symbolForStructural`. -/
def symbolFor (key : String) (hint : String) : TranslateM String := do
  match (← get).atomToName.get? key with
  | some name => return name
  | none =>
    let name ← freshSymbol hint
    modify fun s => { s with
      atomToName := s.atomToName.insert key name
      nameToAtom := s.nameToAtom.insert name key }
    return name

/-- Normalize expression-derived identities before lookup.

All expressions have metavariables instantiated and universe levels normalized.
Type components additionally undergo recursive reducible reduction, which
canonicalizes abbreviations and record projections below an outer type
constructor. This is deliberately not applied to `exprs`: unfolding a function
head or closure body would erase the term identity those keys represent. -/
private def normalizeStructuralKey (key : StructuralKey) : TranslateM StructuralKey := do
  let exprs ← key.exprs.mapM fun e => do
    Meta.Sym.normalizeLevels (← instantiateMVars e)
  let typeExprs ← key.typeExprs.mapM fun e => do
    let e ← instantiateMVars e
    Meta.Sym.normalizeLevels (← Meta.withReducible <| Meta.reduceAll e)
  return { key with exprs, typeExprs }

/-- Look up or allocate an expression-derived symbol using structural identity. -/
def symbolForStructural (key : StructuralKey) (hint : String) : TranslateM String := do
  let key ← normalizeStructuralKey key
  match (← get).structuralToName.get? key with
  | some name => return name
  | none =>
    let name ← freshSymbol hint
    let trace := (← get).structuralAllocations
    if fresh : name ∉ trace.entries.map Prod.snd then
      modify fun s => { s with
        structuralToName := s.structuralToName.insert key name
        structuralAllocations := trace.cons key name fresh
        nameToAtom := s.nameToAtom.insert name key.tag }
      return name
    else
      throwError
        "crush: internal structural symbol collision for freshly reserved name `{name}`"

/-- Existing symbol for a structural identity, if one has been allocated. -/
def structuralSymbol? (key : StructuralKey) : TranslateM (Option String) := do
  let key ← normalizeStructuralKey key
  return (← get).structuralToName.get? key

/-- Record that SMT symbol `name` stands for the Lean term `e`, for proof replay.
Idempotent; the first recording wins, so a symbol reused across occurrences keeps its
original term. -/
def recordSymbolExpr (name : String) (e : Expr) : TranslateM Unit := do
  unless (← get).nameToExpr.contains name do
    modify fun s => { s with nameToExpr := s.nameToExpr.insert name e }

/-- Register an emitted assertion's provenance, returning the fact id to embed in
its `:named` attribute. -/
def recordFact (descr : String) (proof : Option Expr := none) (prop : Option Expr := none)
    (negationTransform : Option Expr := none) (reconstructionProof : Option Expr := none)
    (instanceOf : Option Expr := none) :
    TranslateM Nat := do
  let id := (← get).facts.size
  modify fun s => { s with facts := s.facts.push {
    id, proof, prop, negationTransform, reconstructionProof, instanceOf, descr } }
  return id

/-- Bind `fvar` to SMT variable name `name` for the duration of `k` (a quantifier
body), restoring the previous binding afterwards. -/
def withBoundVar {α : Type} (fvar : FVarId) (name : String) (k : TranslateM α) : TranslateM α := do
  let prev := (← get).boundVars
  modify fun s => { s with boundVars := s.boundVars.insert fvar name }
  try k finally modify fun s => { s with boundVars := prev }

/-- The SMT variable name for `fvar` if it is a bound quantifier variable. -/
def boundVar? (fvar : FVarId) : TranslateM (Option String) := do
  return (← get).boundVars.get? fvar

/-- Bind `fvar` as a *function-typed* quantifier variable whose applications route
through the `app` symbol `appSym`, for the duration of `k`. Used by the
higher-order encoding: such a variable is a value of an `Fn` sort, so
`f x` becomes `(app f x)` rather than a direct application. -/
def withFunVar {α : Type} (fvar : FVarId) (appSym : String) (k : TranslateM α) :
    TranslateM α := do
  let prev := (← get).funVars
  modify fun s => { s with funVars := s.funVars.insert fvar appSym }
  try k finally modify fun s => { s with funVars := prev }

/-- The `app` symbol for `fvar` if it is a function-typed bound variable. -/
def funVar? (fvar : FVarId) : TranslateM (Option String) := do
  return (← get).funVars.get? fvar

end TranslateM

end Crush
