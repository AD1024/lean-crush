import Lean
import Crush.SMT.Syntax
import Crush.Translation.Monad
import Crush.Translation.Instances

/-!
# User-extensible translation: handlers and head-indexed lowerings

Register metaprograms for general term translation, head-indexed lowerings,
result-indexed lowerings, and sort translation. Handlers receive elaborated spines
and recursive translation callbacks; `none` defers to the next applicable handler.
General term handlers have first refusal, and priorities order each registry.

Term dispatch preserves the syntactic head. Result dispatch uses the immediate type
head or a syntactic dependent codomain, so aliases remain distinct keys. Sort handlers
also see the weak-head-normalized type after declining the original. These extensions
are part of the trusted translation boundary under the trusting discharge policies.
-/

open Lean Elab Meta

namespace Crush

open SMT

/-- The recursion callbacks and payload handed to a user translation handler.
The callbacks are supplied by the core translator so a handler never needs to
know the internal representation of `TranslateM`'s recursion. -/
structure TranslationCtx where
  /-- The application being translated: syntactic `fn` applied to the original
      elaborated `args`. No weak-head normalization is implied. -/
  fn        : Expr
  args      : Array Expr
  /-- Recurse into a subterm, producing an SMT term. -/
  emitTerm  : Expr → TranslateM SMT.Term
  /-- Recurse into a type, producing an SMT sort. -/
  emitSort  : Expr → TranslateM SMT.SSort
  /-- Ensure a declaration (declare-fun/sort/datatype) is emitted for `key`,
      generating it via the supplied thunk on first request. Returns the symbol. -/
  declare   : (key : String) → (hint : String) →
                (String → TranslateM (Array SMT.Command)) → TranslateM String

/-- A user translation handler. Returns `some t` to claim the term, or `none` to
defer to the next handler / the default translator. Runs in `TranslateM`, so it
may emit declarations, allocate symbols, and inspect the environment. -/
abbrev TranslationHandler := TranslationCtx → TranslateM (Option SMT.Term)

/-- A lowering registered for one specific Lean head constant.

This is definitionally the same callback as `TranslationHandler`; the separate name
documents that head matching is performed by the `@[crush_lower target]` registry.
A lowering may still return `none` when the application shape, type, or typeclass
instance is not one it can encode soundly. -/
abbrev LoweringHandler := TranslationHandler

instance : TypeName TranslationHandler := unsafe (TypeName.mk _ ``TranslationHandler)

private def unpackHandlers (cached : Array Dynamic) : Array TranslationHandler :=
  cached.filterMap fun value => Dynamic.get? TranslationHandler value

private def packHandlers (handlers : Array TranslationHandler) : Array Dynamic :=
  handlers.map fun handler => Dynamic.mk handler

/-- Whether argument `i` is the fixed library instance of an operator supported by
the structural translator. Unsupported operations return `false`. Extension
lowerings should use `hasExpectedInstance` to specify the dictionary they model. -/
def TranslationCtx.hasCanonicalInstance (ctx : TranslationCtx) (i : Nat) :
    TranslateM Bool := do
  return ← hasExpectedOverloadInstance (mkAppN ctx.fn ctx.args) i

/-- Whether argument `i` is definitionally equal to the exact instance dictionary
whose semantics a lowering implements. This is the sound check for assigning a fixed
library operation its SMT meaning, even when users register higher-priority instances. -/
def TranslationCtx.hasExpectedInstance
    (ctx : TranslationCtx) (i : Nat) (expected : Expr) : TranslateM Bool := do
  let some actual := ctx.args[i]? | return false
  isDefEqRigid actual expected

/-- Whether argument `i` has the given declaration head.

Use this instead of full definitional equality only when the standard dictionary has
a unique declaration head and its dependent parameters contain elaboration-specific
proof predicates, as with Array `GetElem`. -/
def TranslationCtx.hasInstanceHead (ctx : TranslationCtx) (i : Nat) (expected : Name) : Bool :=
  match ctx.args[i]? with
  | some actual => actual.getAppFn.isConstOf expected
  | none => false

/-- A user **sort** handler: claims a Lean *type* and maps it to an SMT sort. The
`fn`/`args` of the `TranslationCtx` are the type's head constant and its arguments
(`Map`, `#[Int, Bool]`), and `emitSort` recurses into the argument types. Returns
`some s` to claim the type, `none` to defer.

This is the sort-level counterpart to `TranslationHandler`, needed to retarget a
Lean type to a *theory* sort — e.g. encoding a finite map as SMT's `(Array K V)`
rather than an uninterpreted datatype. Without it a user could remap a type's
operations but not the type itself, so `(select m k)` would be applied to a
datatype-sorted `m` and the script would be ill-sorted. -/
abbrev SortHandler := TranslationCtx → TranslateM (Option SMT.SSort)

instance : TypeName SortHandler := unsafe (TypeName.mk _ ``SortHandler)

private def unpackSortHandlers (cached : Array Dynamic) : Array SortHandler :=
  cached.filterMap fun value => Dynamic.get? SortHandler value

private def packSortHandlers (handlers : Array SortHandler) : Array Dynamic :=
  handlers.map fun handler => Dynamic.mk handler

/-- A registered handler together with its metadata. -/
structure HandlerEntry where
  declName : Name
  priority : Nat
  deriving Inhabited

/-- Declaration names of a registry's entries, highest priority first. -/
private def sortedNames (entries : Array HandlerEntry) : Array Name :=
  (entries.qsort (fun a b => a.priority > b.priority)).map (·.declName)

/-- Persistent environment extension holding registered handler declaration names.
We store *names*, not closures, and `evalConst` them at tactic time; this keeps
the extension serializable across files and imports. -/
initialize crushTranslateExt :
    SimplePersistentEnvExtension HandlerEntry (Array HandlerEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun arr e => arr.push e
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- Priority argument for the attribute, defaulting to `1000` (lower = tried later,
matching Lean's `simp` convention where higher priority fires first). -/
syntax (name := crushTranslateAttr) "crush_translate" (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `crushTranslateAttr
  descr := "Register a lean-crush translation handler (TranslationHandler)."
  applicationTime := .afterCompilation
  add := fun declName stx _ => do
    -- `stx` is `crush_translate (prio)?`; the optional prio is child #1.
    let prio ← getAttrParamOptPrio stx[1]
    -- Type-check that `declName : TranslationHandler`, so registration errors
    -- surface at declaration time, not deep inside the tactic.
    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration {declName}"
    let expectedTy := mkConst ``Crush.TranslationHandler
    unless (← MetaM.run' (isDefEqReadOnly info.type expectedTy)) do
      throwError "@[crush_translate] expects a declaration of type `TranslationHandler`, \
                  but {declName} has type{indentExpr info.type}"
    modifyEnv fun env =>
      crushTranslateExt.addEntry env { declName, priority := prio }
}

/-- Retrieve all registered handlers, highest priority first, resolving each name
to its runtime `TranslationHandler` closure. `evalConst` is `unsafe` (it runs
compiled code from the environment), so the real work lives in an `unsafe` def
exposed through a safe `@[implemented_by]` wrapper — the standard Lean idiom for
attribute-driven plugins (cf. `KeyedDeclsAttribute`). -/
unsafe def getTranslationHandlersUnsafe : TranslateM (Array TranslationHandler) := do
  if let some cached := (← get).registries.translation then
    return unpackHandlers cached
  let env ← getEnv
  let opts ← getOptions
  let names := sortedNames (crushTranslateExt.getState env)
  let handlers ← names.filterMapM fun declName => do
    match env.evalConst TranslationHandler opts declName with
    | .ok h => return some h
    | .error _ => return none
  modify fun s => { s with registries :=
    { s.registries with translation := some (packHandlers handlers) } }
  return handlers

@[implemented_by getTranslationHandlersUnsafe]
opaque getTranslationHandlers : TranslateM (Array TranslationHandler)

/-- Whether any `@[crush_translate]` handler is registered. A cheap array read on
the persistent extension, with no `evalConst` — so the common case of no user
handlers skips handler resolution entirely on the hot path of `emitTerm`. -/
def hasTranslationHandlersInEnv (env : Environment) : Bool :=
  !(crushTranslateExt.getState env).isEmpty

def hasTranslationHandlers : TranslateM Bool := do
  match (← get).registries.hasTranslation with
  | some flag => return flag
  | none =>
    let flag := hasTranslationHandlersInEnv (← getEnv)
    modify fun s => { s with registries := { s.registries with hasTranslation := some flag } }
    return flag

/-! ## Head-indexed lowerings (`@[crush_lower target]`)

Index callbacks by the application head. General handlers retain first refusal;
higher-priority targeted handlers run before defaults for that head.
-/

/-- Serializable entry for one head-indexed lowering. -/
structure LoweringEntry where
  head     : Name
  declName : Name
  priority : Nat
  deriving Inhabited

private def addLoweringEntry
    (state : NameMap (Array HandlerEntry)) (entry : LoweringEntry) :
    NameMap (Array HandlerEntry) :=
  state.alter entry.head fun entries =>
    (entries.getD #[]).push { declName := entry.declName, priority := entry.priority }

initialize crushLoweringExt :
    SimplePersistentEnvExtension LoweringEntry (NameMap (Array HandlerEntry)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addLoweringEntry
    addImportedFn := mkStateFromImportedEntries addLoweringEntry {}
  }

/-- Register a `LoweringHandler` for applications of one Lean constant.

Example:
```
@[crush_lower Int.natAbs]
def lowerNatAbs : LoweringHandler := fun ctx => ...
```
As with `simp`, an optional priority (`low`, `high`, or a number) controls ordering
when several lowerings target the same constant. -/
syntax (name := crushLowerAttr) "crush_lower " ident (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `crushLowerAttr
  descr := "Register a head-indexed lean-crush SMT lowering (LoweringHandler)."
  applicationTime := .afterCompilation
  add := fun declName stx _ => do
    let headStx := stx[1]
    let head ← Elab.realizeGlobalConstNoOverloadWithInfo headStx
    let prio ← getAttrParamOptPrio stx[2]
    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration {declName}"
    let expectedTy := mkConst ``Crush.LoweringHandler
    unless (← MetaM.run' (isDefEqReadOnly info.type expectedTy)) do
      throwError "@[crush_lower] expects a declaration of type `LoweringHandler`, \
                  but {declName} has type{indentExpr info.type}"
    modifyEnv fun env =>
      crushLoweringExt.addEntry env { head, declName, priority := prio }
}

/-- Whether `head` has any targeted lowerings, without evaluating their declarations. -/
def hasLoweringsForInEnv (env : Environment) (head : Name) : Bool :=
  (crushLoweringExt.getState env).contains head

def hasLoweringsFor (head : Name) : TranslateM Bool := do
  return hasLoweringsForInEnv (← getEnv) head

unsafe def getLoweringsForUnsafe (head : Name) : TranslateM (Array LoweringHandler) := do
  if let some cached := (← get).registries.lowerings.get? head then
    return unpackHandlers cached
  let env ← getEnv
  let opts ← getOptions
  let names := sortedNames ((crushLoweringExt.getState env).getD head #[])
  let handlers ← names.filterMapM fun declName => do
    match env.evalConst LoweringHandler opts declName with
    | .ok handler => return some handler
    | .error _ => return none
  modify fun s => { s with registries := { s.registries with
    lowerings := s.registries.lowerings.insert head (packHandlers handlers) } }
  return handlers

@[implemented_by getLoweringsForUnsafe]
opaque getLoweringsFor (head : Name) : TranslateM (Array LoweringHandler)

/-! ## Result-indexed lowerings (`@[crush_lower_result target]`)

Dispatch by the immediate result head or the codomain of a syntactic dependent
function type. Register named aliases separately when they must also be recognized.
-/

initialize crushResultLoweringExt :
    SimplePersistentEnvExtension LoweringEntry (NameMap (Array HandlerEntry)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addLoweringEntry
    addImportedFn := mkStateFromImportedEntries addLoweringEntry {}
  }

/-- Register a lowering selected by the head of a term's result type.

For example, `@[crush_lower_result Decidable]` sees ordinary `Decidable p` values
and syntactic dependent function types ending in `Decidable (...)`. Register
`DecidableEq` separately to catch terms whose inferred type retains that alias. -/
syntax (name := crushLowerResultAttr) "crush_lower_result " ident (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `crushLowerResultAttr
  descr := "Register a result-indexed lean-crush SMT lowering (LoweringHandler)."
  applicationTime := .afterCompilation
  add := fun declName stx _ => do
    let headStx := stx[1]
    let head ← Elab.realizeGlobalConstNoOverloadWithInfo headStx
    let prio ← getAttrParamOptPrio stx[2]
    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration {declName}"
    let expectedTy := mkConst ``Crush.LoweringHandler
    unless (← MetaM.run' (isDefEqReadOnly info.type expectedTy)) do
      throwError "@[crush_lower_result] expects a declaration of type \
                  `LoweringHandler`, but {declName} has type{indentExpr info.type}"
    modifyEnv fun env =>
      crushResultLoweringExt.addEntry env { head, declName, priority := prio }
}

def hasResultLoweringsFor (head : Name) : TranslateM Bool := do
  return (crushResultLoweringExt.getState (← getEnv)).contains head

unsafe def getResultLoweringsForUnsafe
    (head : Name) : TranslateM (Array LoweringHandler) := do
  if let some cached := (← get).registries.resultLowerings.get? head then
    return unpackHandlers cached
  let env ← getEnv
  let opts ← getOptions
  let names := sortedNames ((crushResultLoweringExt.getState env).getD head #[])
  let handlers ← names.filterMapM fun declName => do
    match env.evalConst LoweringHandler opts declName with
    | .ok handler => return some handler
    | .error _ => return none
  modify fun s => { s with registries := { s.registries with
    resultLowerings :=
      s.registries.resultLowerings.insert head (packHandlers handlers) } }
  return handlers

@[implemented_by getResultLoweringsForUnsafe]
opaque getResultLoweringsFor (head : Name) : TranslateM (Array LoweringHandler)

def hasResultLowerings : TranslateM Bool := do
  match (← get).registries.hasResult with
  | some flag => return flag
  | none =>
    let flag := !(crushResultLoweringExt.getState (← getEnv)).isEmpty
    modify fun s => { s with registries := { s.registries with hasResult := some flag } }
    return flag

/-! ## Sort handlers (`@[crush_translate_sort]`)

Use an independent registry so term and sort handlers for the same type do not
interfere.
-/

initialize crushTranslateSortExt :
    SimplePersistentEnvExtension HandlerEntry (Array HandlerEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun arr e => arr.push e
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

syntax (name := crushTranslateSortAttr) "crush_translate_sort" (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `crushTranslateSortAttr
  descr := "Register a lean-crush sort handler (SortHandler)."
  applicationTime := .afterCompilation
  add := fun declName stx _ => do
    let prio ← getAttrParamOptPrio stx[1]
    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration {declName}"
    let expectedTy := mkConst ``Crush.SortHandler
    unless (← MetaM.run' (isDefEqReadOnly info.type expectedTy)) do
      throwError "@[crush_translate_sort] expects a declaration of type `SortHandler`, \
                  but {declName} has type{indentExpr info.type}"
    modifyEnv fun env =>
      crushTranslateSortExt.addEntry env { declName, priority := prio }
}

unsafe def getSortHandlersUnsafe : TranslateM (Array SortHandler) := do
  if let some cached := (← get).registries.sort then
    return unpackSortHandlers cached
  let env ← getEnv
  let opts ← getOptions
  let names := sortedNames (crushTranslateSortExt.getState env)
  let handlers ← names.filterMapM fun declName => do
    match env.evalConst SortHandler opts declName with
    | .ok h => return some h
    | .error _ => return none
  modify fun s => { s with registries :=
    { s.registries with sort := some (packSortHandlers handlers) } }
  return handlers

@[implemented_by getSortHandlersUnsafe]
opaque getSortHandlers : TranslateM (Array SortHandler)

/-- Whether any `@[crush_translate_sort]` handler is registered. Guards the sort
hot path (`emitSort`) the same way `hasTranslationHandlers` guards `emitTerm`. -/
def hasSortHandlers : TranslateM Bool := do
  match (← get).registries.hasSort with
  | some flag => return flag
  | none =>
    let flag := !(crushTranslateSortExt.getState (← getEnv)).isEmpty
    modify fun s => { s with registries := { s.registries with hasSort := some flag } }
    return flag

end Crush
