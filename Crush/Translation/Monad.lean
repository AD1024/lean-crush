import Lean
import Crush.SMT.Syntax
import Crush.Metatheory.VCG.Command
import Crush.Metatheory.VCG.Datatype
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

open Metatheory.VCG

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
structure StructuralAllocTrace where
  entries : List (StructuralKey × String)
  namesNodup : (entries.map Prod.snd).Nodup

instance : Inhabited StructuralAllocTrace where
  default := { entries := [], namesNodup := by simp }

/-- Every concrete symbol returned by the shared allocator, independent of its
semantic key class. This is the global freshness witness needed when ordinary,
datatype, closure, and derived identifiers share one SMT namespace. -/
structure NameAllocTrace where
  names : List String
  nodup : names.Nodup

instance : Inhabited NameAllocTrace where
  default := { names := [], nodup := by simp }

namespace NameAllocTrace

def push (trace : NameAllocTrace) (name : String)
    (fresh : name ∉ trace.names) : NameAllocTrace where
  names := name :: trace.names
  nodup := by simp [fresh, trace.nodup]

end NameAllocTrace

namespace StructuralAllocTrace

private theorem pair_eq_of_snd_eq_of_nodup
    {α β : Type} {entries : List (α × β)} {left right : α × β}
    (nodup : (entries.map Prod.snd).Nodup)
    (leftMem : left ∈ entries) (rightMem : right ∈ entries)
    (sameName : left.2 = right.2) : left = right := by
  induction entries <;> grind

/-- Extend an allocation trace with a name proved fresh for that trace. -/
def cons (trace : StructuralAllocTrace) (key : StructuralKey) (name : String)
    (fresh : name ∉ trace.entries.map Prod.snd) : StructuralAllocTrace where
  entries := (key, name) :: trace.entries
  namesNodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨fresh, trace.namesNodup⟩

/-- A name occurs at most once in the structural allocation history. -/
theorem uniqueName (trace : StructuralAllocTrace) :
    trace.entries.map Prod.snd |>.Nodup :=
  trace.namesNodup

/-- The allocation trace is injective: equality of emitted names identifies the
same structural allocation, and hence the same normalized structural key. -/
theorem entry_eq_of_name_eq (trace : StructuralAllocTrace)
    {left right : StructuralKey × String}
    (leftMem : left ∈ trace.entries) (rightMem : right ∈ trace.entries)
    (sameName : left.2 = right.2) : left = right :=
  pair_eq_of_snd_eq_of_nodup trace.namesNodup leftMem rightMem sameName

theorem key_eq_of_name_eq (trace : StructuralAllocTrace)
    {leftKey rightKey : StructuralKey} {leftName rightName : String}
    (leftMem : (leftKey, leftName) ∈ trace.entries)
    (rightMem : (rightKey, rightName) ∈ trace.entries)
    (sameName : leftName = rightName) : leftKey = rightKey := by
  have := trace.entry_eq_of_name_eq leftMem rightMem sameName
  exact congrArg Prod.fst this

end StructuralAllocTrace

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

/-- Auditable link from one retained command encoding to the globally allocated
symbols it references. Every allocator key class contributes to this one name trace,
so ordinary structural commands and datatype guards use the same mechanism. -/
structure CommandAllocLink where
  encodingIndex : Nat
  commandIndex : Nat
  symbols : Array String
  allocation : NameAllocTrace
  symbolsAllocated : ∀ symbol ∈ symbols.toList,
    symbol ∈ allocation.names

/-- Exact state position and global-allocation support for one checked native
datatype command. -/
structure DatatypeDeclAlloc where
  commandIndex : Nat
  declarationIndex : Nat
  names : Array String
  allocation : NameAllocTrace
  namesAllocated : ∀ name ∈ names.toList, name ∈ allocation.names

/-- One successful dispatch through the restricted certified primitive registry. -/
structure CertifiedHookUse where
  declaration : Name
  targetSymbol : String
  deriving Inhabited, Repr

/-- Whole-run classification before dependent representation evidence is
attached by the proved VCG route. -/
inductive RunStatus where
  | proved
  | trusted (reasons : Array TrustReason)

/-- Mutable translation state. -/
structure TranslateState where
  cfg        : Config
  /-- Bijection between high-level atoms and emitted SMT symbols. -/
  atomToName : Std.HashMap String String := {}
  /-- Structural identities for expression-derived symbols. Kept separate from
      `atomToName`, whose string keys are part of the user extension API. -/
  structuralToName : Std.HashMap StructuralKey String := {}
  /-- Auditable, proof-carrying allocation history for `structuralToName`. -/
  structuralAllocs : StructuralAllocTrace := default
  /-- Global proof-facing history of every allocated SMT symbol. -/
  nameAllocs : NameAllocTrace := default
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
  /-- Syntax encodings retained for declarations, assertions, and datatype
      guards. Their semantic meaning is established separately. -/
  commandEncodings : Array CommandEncoding := #[]
  /-- Checked global-name dependencies of `commandEncodings`. -/
  commandAllocLinks : Array CommandAllocLink := #[]
  /-- Every step that crossed the explicit trusted translation boundary. -/
  trustReasons : Array TrustReason := #[]
  /-- Root expression of the legacy direct translator, recorded once even when
      recursive emission revisits many subterms. -/
  directSource : Option Expr := none
  /-- Type-erased identity-bearing semantic certificates for elaborated source symbols. -/
  verifiedConstants : Array Dynamic := #[]
  /-- Source facts whose datatype environments and command locations were
      retained for the proof-facing translator comparison. -/
  factTranslations : Array FactTranslation := #[]
  /-- Fact-local datatype environment used while emitting SMT datatype declarations.
      Restored after the fact has been translated. -/
  activeDataSignature : Option Metatheory.Reification.SomeDataSignature := none
  /-- SMT datatype declarations paired with their exact typed block and command
      well-formedness proof. -/
  datatypeDecls : Array SomeDatatypeDecl := #[]
  /-- Command-array positions appended atomically with `datatypeDecls`. -/
  datatypeDeclIndices : Array Nat := #[]
  datatypeDeclAllocs : Array DatatypeDeclAlloc := #[]
  /-- Globally duplicate-free names declared by all retained SMT datatype declarations. -/
  datatypeDeclNames : NameAllocTrace := default
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

namespace TranslateState

/-- Operational status of a completed translation run. -/
def status (state : TranslateState) : RunStatus :=
  if state.trustReasons.isEmpty then .proved else .trusted state.trustReasons

/-- The Crush translator used no operation marked as trusted. -/
def Proved (state : TranslateState) : Prop :=
  state.trustReasons = #[]

@[simp] theorem status_eq_proved_iff (state : TranslateState) :
    state.status = .proved ↔ state.Proved := by
  simp [status, Proved, Array.isEmpty_iff]

/-- Retained datatype-guard encodings in their emission order. The allocation
links select them from the shared command-encoding trace without duplicating
mutable state. -/
def datatypeGuardDefs (state : TranslateState) : Array DatatypeGuardDef :=
  state.commandAllocLinks.filterMap fun link =>
    match state.commandEncodings[link.encodingIndex]? with
    | some (CommandEncoding.datatypeGuard encoding) => some encoding
    | _ => none

/-- Emitted command positions aligned with `datatypeGuardDefs`. -/
def datatypeGuardDefIndices (state : TranslateState) : Array Nat :=
  state.commandAllocLinks.filterMap fun link =>
    match state.commandEncodings[link.encodingIndex]? with
    | some (CommandEncoding.datatypeGuard _) => some link.commandIndex
    | _ => none

end TranslateState

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

/-- Emit an encoded command only when all symbols determined by its witness have
already been recorded in the global uniqueness trace. The command, encoding,
and dependency link are appended atomically. -/
def emitAllocatedCommand
    (encoding : CommandEncoding) : TranslateM Unit := do
  let symbols := encoding.allocatedSymbols
  let state ← get
  let allocatedNames := state.nameAllocs.names
  if allocated : ∀ symbol ∈ symbols.toList, symbol ∈ allocatedNames then
    let index := state.commandEncodings.size
    let commandIndex := state.commands.size
    modify fun s => { s with
      commands := s.commands.push encoding.command
      commandEncodings := s.commandEncodings.push encoding
      commandAllocLinks := s.commandAllocLinks.push {
        encodingIndex := index
        commandIndex
        symbols
        allocation := state.nameAllocs
        symbolsAllocated := allocated } }
  else
    let missing := symbols.filter fun symbol => !allocatedNames.contains symbol
    throwError
      "crush: internal encoded command refers to unallocated symbols: {missing}"

def markTrusted (reason : TrustReason) : TranslateM Unit :=
  modify fun state => { state with
    trustReasons := state.trustReasons.push reason }

def markDatatypeTrusted
    (reason : Metatheory.Reification.DatatypeReject) : TranslateM Unit := do
  let rendered := reprStr reason
  unless (← get).trustReasons.any fun
      | .datatype existing => reprStr existing == rendered
      | _ => false do
    markTrusted (.datatype reason)

/-- Classify the extensible direct Lean-to-SMT route as trusted exactly once.
The metatheory proves the separately defined proof-defined command generator and
applies to the Crush translator only after `CommandEquiv.build?` succeeds. -/
def markDirect (source : Expr) : TranslateM Unit := do
  if (← get).directSource.isNone then
    modify fun state => { state with
      directSource := some source
      trustReasons := state.trustReasons.push (.direct source) }

def recordVerifiedConstant (certificate : Dynamic) : TranslateM Nat := do
  let index := (← get).verifiedConstants.size
  modify fun s => { s with verifiedConstants := s.verifiedConstants.push certificate }
  return index

def recordFactTranslation
    (factTranslation : FactTranslation) : TranslateM Nat := do
  let index := (← get).factTranslations.size
  modify fun state => {
    state with factTranslations := state.factTranslations.push factTranslation }
  return index

/-- Recompute every fact's datatype-command locations after all facts have been
translated. A fact is first recorded while its own assertion is being emitted;
this final pass makes every retained `FactTranslation` refer to the complete
final `TranslateState.commands` array. -/
def finalizeFactTranslations : TranslateM Unit := do
  let state ← get
  let mut finalizedFacts : Array FactTranslation := #[]
  for factTranslation in state.factTranslations do
    let some factTranslation := factTranslation.withCommands? state.commands
        state.datatypeDecls state.datatypeDeclIndices
        state.datatypeGuardDefs state.datatypeGuardDefIndices
      | throwError "crush: emitted command sequence lost an SMT datatype declaration"
    finalizedFacts := finalizedFacts.push factTranslation
  modify fun current => { current with factTranslations := finalizedFacts }

def withDataSignature {α : Type}
    (signature : Metatheory.Reification.SomeDataSignature)
    (body : TranslateM α) : TranslateM α := do
  let previous := (← get).activeDataSignature
  modify fun state => { state with activeDataSignature := some signature }
  try body finally
    modify fun state => { state with activeDataSignature := previous }

/-- Emit an SMT datatype declaration and retain its typed description in the same
state update, so they cannot disagree. -/
def emitDatatypeDecl
    (declaration : SomeDatatypeDecl) : TranslateM Nat := do
  let state ← get
  let commandIndex := state.commands.size
  let declarationIndex := state.datatypeDecls.size
  let names := declaration.names
  if allocated : ∀ name ∈ names.toList, name ∈ state.nameAllocs.names then
    if namesNodup : (names.toList ++ state.datatypeDeclNames.names).Nodup then
      modify fun current => {
        current with
          commands := current.commands.push declaration.command
          datatypeDecls := current.datatypeDecls.push declaration
          datatypeDeclIndices :=
            current.datatypeDeclIndices.push commandIndex
          datatypeDeclAllocs :=
            current.datatypeDeclAllocs.push {
              commandIndex
              declarationIndex
              names
              allocation := state.nameAllocs
              namesAllocated := allocated }
          datatypeDeclNames := {
            names := names.toList ++ state.datatypeDeclNames.names
            nodup := namesNodup } }
      return commandIndex
    else
      throwError "crush: retained SMT datatype declarations declare the same symbol"
  else
    let missing := names.filter fun name => !state.nameAllocs.names.contains name
    throwError "crush: SMT datatype declaration uses unallocated names: {missing}"

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

/-- Names with fixed meaning in the proved untyped semantics. The opt-in
datatype path reserves them before allocation so a user declaration cannot make
a reified datatype sort equal to `Bool`/`Int`/`String`, or make an SMT datatype
constructor/selector parse as a logical connective. -/
private def proofReservedName (name : String) : Bool :=
  name == "Bool" || name == "Int" || name == "String" || name == "=" ||
    name == "not" || name == "=>" || name == "and" || name == "or"

/-- Turn an arbitrary hint into a legal, collision-free SMT symbol. -/
private def reserveSymbol (hint : String) : TranslateM String := do
  let sanitized := sanitizeSymbol hint
  let base :=
    if (← get).cfg.certifyDatatype && proofReservedName sanitized then
      "cr_" ++ sanitized
    else sanitized
  let used := (← get).usedNames
  if !used.contains base then
    let trace := (← get).nameAllocs
    if fresh : base ∉ trace.names then
      modify fun state => {
        state with
          usedNames := state.usedNames.insert base 0
          nameAllocs := trace.push base fresh }
      return base
    else
      throwError "crush: internal allocator freshness drift for `{base}`"
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
    let trace := (← get).nameAllocs
    if fresh : name ∉ trace.names then
      modify fun state => {
        state with
          usedNames := (state.usedNames.insert base next).insert name 0
          nameAllocs := trace.push name fresh }
      return name
    else
      throwError "crush: internal allocator freshness drift for `{name}`"

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
    let trace := (← get).structuralAllocs
    if fresh : name ∉ trace.entries.map Prod.snd then
      modify fun s => { s with
        structuralToName := s.structuralToName.insert key name
        structuralAllocs := trace.cons key name fresh
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
