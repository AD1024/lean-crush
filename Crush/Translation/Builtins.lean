import Lean
import Crush.Translation.Attr
open Lean Elab Meta

/-!
# Built-in translation handlers and user-facing sugar

The default theory mappings (Bool, Nat→Int, Int, BitVec, String, `=`, logical
connectives) are themselves registered as ordinary `@[crush_translate]` handlers.
This dogfoods the extension API: the built-ins have no privileged path, so any
behaviour a built-in relies on is available to user handlers too.

We also expose sugar macros so the common cases are one-liners:

```
crush_map Nat.add    => "+"          -- map a Lean constant to an SMT symbol
crush_map_sort MyT   => "MySort"     -- map a Lean type to an SMT sort symbol
```

These desugar to `@[crush_translate] def … : TranslationHandler := …`.
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
