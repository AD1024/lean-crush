import Lean
import Crush.SMT.Syntax
import Crush.Translation.Monad
open Lean Elab Meta

/-!
# User-extensible translation: handlers and head-indexed lowerings

This is lean-crush's central new capability. A user annotates a Lean declaration
with a metaprogram describing how to translate a matched `Expr` into SMT. Handlers
are ordinary Lean terms of type `TranslationHandler`, evaluated **at elaboration
time** (via `evalConst`) when the tactic runs. This means the "SMT code" is
produced *programmatically*, with the full power of `MetaM` and recursion back
into the default translator, rather than being a fixed table baked into the tool.

Four extension surfaces are provided:

1. `@[crush_translate]` on a `def h : TranslationHandler` — the general form. `h`
   inspects the head `Expr` and either returns `some smtTerm` or defers (`none`).

2. `@[crush_lower Target.constant]` on a `def h : LoweringHandler` — the targeted
   form. The registry dispatches `h` only for applications of `Target.constant`,
   so the handler can focus on argument validation and SMT construction without
   matching every term itself. Multiple lowerings for one head use priorities.

3. `@[crush_lower_result Target.type]` on a `def h : LoweringHandler` — the
   result-indexed form. It dispatches on the immediate result head when one is
   present, or peels a syntactic dependent function type to find its codomain
   head. Register named aliases separately when both forms must be handled; the
   built-in decision lowering registers both `Decidable` and `DecidableEq`.

4. `crush_map`/`crush_map_sort` macros (see `Crush/Translation/Builtins.lean`) —
   sugar for the common cases of "map this constant to this SMT symbol/sort", which
   desugar to a `TranslationHandler`.

A handler receives:
* the instantiated expression's syntactic head,
* its original elaborated argument spine,
* callbacks `emitSort`/`emitTerm` to recurse,
all bundled in `TranslationCtx`. Handlers are tried in priority order; the first
returning `some` wins within that dispatch layer. The translator does not
weak-head-normalize the term before constructing this context; a handler that
needs reduction must request it through `MetaM`. If no extension claims the
term, the default structural translator runs.
-/

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

/-- Whether argument `i` is the ambient global instance selected by typeclass synthesis.

Local instances are disabled while synthesizing the baseline; otherwise a local
override would compare equal to itself. A scoped or imported high-priority global
instance still becomes the baseline. Therefore, a lowering that models one particular
library dictionary should use `hasExpectedInstance` instead. -/
def TranslationCtx.hasCanonicalInstance (ctx : TranslationCtx) (i : Nat) :
    TranslateM Bool := do
  let some inst := ctx.args[i]? | return false
  let instTy ← inferType inst
  try
    let lctx ← getLCtx
    let canonical ← withLCtx lctx {} do synthInstance instTy
    isDefEq inst canonical
  catch _ =>
    return false

/-- Whether argument `i` is definitionally equal to the exact instance dictionary
whose semantics a lowering implements. This is the sound check for assigning a fixed
library operation its SMT meaning, even when users register higher-priority instances. -/
def TranslationCtx.hasExpectedInstance
    (ctx : TranslationCtx) (i : Nat) (expected : Expr) : TranslateM Bool := do
  let some actual := ctx.args[i]? | return false
  isDefEq actual expected

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

/-- A registered handler together with its metadata. -/
structure HandlerEntry where
  declName : Name
  priority : Nat
  deriving Inhabited

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
    unless (← MetaM.run' (Meta.isDefEq info.type expectedTy)) do
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
  let env ← getEnv
  let opts ← getOptions
  let entries := crushTranslateExt.getState env
  let sorted := entries.qsort (fun a b => a.priority > b.priority)
  sorted.filterMapM fun e => do
    match env.evalConst TranslationHandler opts e.declName with
    | .ok h => return some h
    | .error _ => return none

@[implemented_by getTranslationHandlersUnsafe]
opaque getTranslationHandlers : TranslateM (Array TranslationHandler)

/-- Whether any `@[crush_translate]` handler is registered. A cheap array read on
the persistent extension, with no `evalConst` — so the common case of no user
handlers skips handler resolution entirely on the hot path of `emitTerm`. -/
def hasTranslationHandlersInEnv (env : Environment) : Bool :=
  !(crushTranslateExt.getState env).isEmpty

def hasTranslationHandlers : TranslateM Bool := do
  return hasTranslationHandlersInEnv (← getEnv)

/-! ## Head-indexed lowerings (`@[crush_lower target]`)

The general handler extension above intentionally permits dynamic matching, but it
requires every handler to inspect every translated term. Lowerings cover the common
case where one Lean constant has a custom SMT encoding: the persistent extension is
indexed by the head constant, so only relevant callbacks are evaluated.

General handlers run before targeted lowerings in `emitTerm`, preserving the original
contract that `@[crush_translate]` can override every built-in mapping. Within the
targeted registry, higher priority runs first, so applications can override a default
lowering with `@[crush_lower Target high]`.
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
    unless (← MetaM.run' (Meta.isDefEq info.type expectedTy)) do
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
  let env ← getEnv
  let opts ← getOptions
  let entries := (crushLoweringExt.getState env).getD head #[]
  let sorted := entries.qsort (fun a b => a.priority > b.priority)
  sorted.filterMapM fun entry => do
    match env.evalConst LoweringHandler opts entry.declName with
    | .ok handler => return some handler
    | .error _ => return none

@[implemented_by getLoweringsForUnsafe]
opaque getLoweringsFor (head : Name) : TranslateM (Array LoweringHandler)

/-! ## Result-indexed lowerings (`@[crush_lower_result target]`)

Some operations have no stable application head to register: a generated
decision procedure may be a lambda or an auxiliary declaration. Its result family
is stable, however. This registry first uses the immediate head of the term's type.
If the type is syntactically a dependent `∀`, it peels the binders and uses the
codomain head. A named alias is therefore a distinct dispatch key and should also
be registered when callers may retain that alias in the inferred type. -/

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
    unless (← MetaM.run' (Meta.isDefEq info.type expectedTy)) do
      throwError "@[crush_lower_result] expects a declaration of type \
                  `LoweringHandler`, but {declName} has type{indentExpr info.type}"
    modifyEnv fun env =>
      crushResultLoweringExt.addEntry env { head, declName, priority := prio }
}

def hasResultLoweringsFor (head : Name) : TranslateM Bool := do
  return (crushResultLoweringExt.getState (← getEnv)).contains head

unsafe def getResultLoweringsForUnsafe
    (head : Name) : TranslateM (Array LoweringHandler) := do
  let env ← getEnv
  let opts ← getOptions
  let entries := (crushResultLoweringExt.getState env).getD head #[]
  let sorted := entries.qsort (fun a b => a.priority > b.priority)
  sorted.filterMapM fun entry => do
    match env.evalConst LoweringHandler opts entry.declName with
    | .ok handler => return some handler
    | .error _ => return none

@[implemented_by getResultLoweringsForUnsafe]
opaque getResultLoweringsFor (head : Name) : TranslateM (Array LoweringHandler)

def hasResultLowerings : TranslateM Bool := do
  return !(crushResultLoweringExt.getState (← getEnv)).isEmpty

/-! ## Sort handlers (`@[crush_translate_sort]`)

The sort-level counterpart of the above, with an independent extension so a sort
handler and a term handler for the same type do not interfere. -/

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
    unless (← MetaM.run' (Meta.isDefEq info.type expectedTy)) do
      throwError "@[crush_translate_sort] expects a declaration of type `SortHandler`, \
                  but {declName} has type{indentExpr info.type}"
    modifyEnv fun env =>
      crushTranslateSortExt.addEntry env { declName, priority := prio }
}

unsafe def getSortHandlersUnsafe : TranslateM (Array SortHandler) := do
  let env ← getEnv
  let opts ← getOptions
  let entries := crushTranslateSortExt.getState env
  let sorted := entries.qsort (fun a b => a.priority > b.priority)
  sorted.filterMapM fun e => do
    match env.evalConst SortHandler opts e.declName with
    | .ok h => return some h
    | .error _ => return none

@[implemented_by getSortHandlersUnsafe]
opaque getSortHandlers : TranslateM (Array SortHandler)

/-- Whether any `@[crush_translate_sort]` handler is registered. Guards the sort
hot path (`emitSort`) the same way `hasTranslationHandlers` guards `emitTerm`. -/
def hasSortHandlers : TranslateM Bool := do
  return !(crushTranslateSortExt.getState (← getEnv)).isEmpty

end Crush
