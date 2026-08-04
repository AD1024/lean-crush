import Lean
import Crush.SMT.Syntax
import Crush.Translation.Monad
open Lean Elab Meta

/-!
# User-extensible translation: the `@[crush_translate]` framework

This is lean-crush's central new capability. A user annotates a Lean declaration
with a metaprogram describing how to translate a matched `Expr` into SMT. Handlers
are ordinary Lean terms of type `TranslationHandler`, evaluated **at elaboration
time** (via `evalConst`) when the tactic runs. This means the "SMT code" is
produced *programmatically*, with the full power of `MetaM` and recursion back
into the default translator, rather than being a fixed table baked into the tool.

Two registration surfaces are provided:

1. `@[crush_translate]` on a `def h : TranslationHandler` — the general form. `h`
   inspects the head `Expr` and either returns `some smtTerm` or defers (`none`).

2. `crush_map`/`crush_map_sort` macros (see `Crush/Translation/Builtins.lean`) —
   sugar for the common cases of "map this constant to this SMT symbol/sort", which
   desugar to a `TranslationHandler`.

A handler receives:
* the `Expr` being translated (already in whnf-of-head form),
* its spine of arguments,
* callbacks `emitSort`/`emitTerm` to recurse,
all bundled in `TranslationCtx`. Handlers are tried in priority order; the first
returning `some` wins. If none match, the default structural translator runs.
-/

namespace Crush

open SMT

/-- The recursion callbacks and payload handed to a user translation handler.
The callbacks are supplied by the core translator so a handler never needs to
know the internal representation of `TranslateM`'s recursion. -/
structure TranslationCtx where
  /-- The application being translated: `fn` applied to `args`. -/
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
def hasTranslationHandlers : TranslateM Bool := do
  return !(crushTranslateExt.getState (← getEnv)).isEmpty

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
