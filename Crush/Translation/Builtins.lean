import Lean
import Crush.Translation.Attr

/-!
# User-facing translation sugar

`crush_map` and `crush_map_sort` register simple symbol mappings through the same
extension paths as handwritten term and sort handlers, before built-in translation.
They emit no declarations: the mapped symbol must already be known to the solver.
Use a full handler and its `declare` callback to introduce an uninterpreted symbol.
Library operation lowerings live in `DefaultLowerings`; structural forms remain in
`Translate`. General handlers may override either path.
-/

open Lean Elab Meta

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
    `(@[crush_translate_sort]
      def $handlerName : Crush.SortHandler := fun ctx => do
        let .const n _ := ctx.fn | return none
        if n == $(quote c.getId) then
          return some (SMT.SSort.app (.symb $sym) #[])
        else
          return none)

end Crush.Builtins
