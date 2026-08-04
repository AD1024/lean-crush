import Lean
import Crush.Translation.Attr
open Lean Elab Meta

/-!
# User-facing translation sugar

The `crush_map`/`crush_map_sort` macros make the common "this constant ↦ this SMT
symbol/sort" case a one-liner, desugaring to a `@[crush_translate]` handler:

```
crush_map Nat.add    => "+"          -- map a Lean constant to an SMT symbol
crush_map_sort MyT   => "MySort"     -- map a Lean type to an SMT sort symbol
```

Both dispatch through the same handler path as a hand-written
`@[crush_translate] def`, so — like any handler — they run *before* the built-in
structural translator and override it for their head constant (see
`Crush/Translation/Translate.lean` `emitTerm`).

**Scope.** The target string is emitted verbatim as an SMT symbol with **no**
`declare-fun`, so it must be a symbol the solver already knows: an SMT-LIB theory
operator (`+`, `abs`, `str.++`, …) or a sort/symbol declared elsewhere in the
script. Mapping to a fresh name the solver has never seen yields an
"unknown constant" error from the backend. To introduce a genuinely new
uninterpreted symbol (with its declaration), write a full handler and use the
`declare` callback in `TranslationCtx`.

Note: the built-in theory mappings themselves are *not* handlers — they live in the
structural translator in `Crush/Translation/Translate.lean` for directness and
because several need type-directed dispatch (`bitvecTerm?`, `stringTerm?`) that the
head-constant handler shape does not express. A user handler still overrides them,
so the extension surface is not second-class; it is simply not implemented by
dogfooding.
-/

namespace Crush.Builtins

open Crush SMT

/-- Sugar: map a fully-applied Lean constant to a first-order SMT symbol,
translating each argument recursively. Generates a `TranslationHandler`. -/
syntax (name := crushMap) "crush_map " ident " => " str : command

macro_rules
  | `(command| crush_map $c:ident => $sym:str) => do
    let handlerName := mkIdentFrom c (c.getId.str "crushHandler")
    `(@[crush_translate]
      def $handlerName : Crush.TranslationHandler := fun ctx => do
        let .const n _ := ctx.fn | return none
        if n == $(quote c.getId) then
          let args ← ctx.args.mapM ctx.emitTerm
          return some (SMT.Term.app (.symb $sym) args)
        else
          return none)

/-- Sugar: map a Lean type constant to a nullary SMT sort symbol. -/
syntax (name := crushMapSort) "crush_map_sort " ident " => " str : command

macro_rules
  | `(command| crush_map_sort $c:ident => $sym:str) => do
    let handlerName := mkIdentFrom c (c.getId.str "crushSortHandler")
    `(@[crush_translate]
      def $handlerName : Crush.TranslationHandler := fun ctx => do
        let .const n _ := ctx.fn | return none
        if n == $(quote c.getId) then
          return some (SMT.Term.const $sym)
        else
          return none)

end Crush.Builtins
