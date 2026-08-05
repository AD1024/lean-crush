import Crush

/-!
Tests for the user-extensible translation layer: that `@[crush_translate]`
handlers are not merely *registered* but actually *run*, and that they **override**
the built-in structural/theory mappings for the same head constant. The contract is
that user handlers override built-ins for the same constant — there is no privileged
built-in path.

Each theorem below is provable *only* if the handler fired in place of the built-in
translation, so a regression that shadowed handlers behind the built-ins (as an
earlier ordering did) makes these fail to elaborate.

Handlers register into a persistent environment extension, so a handler is active
for every `crush` call *after* it in this file. Nothing imports this file, so the
handlers stay local to it.
-/

open Crush

set_option crush.trust "trust"

/-! ## A handler fires on an otherwise-uninterpreted constant

`mystery` has no built-in mapping, so without a handler `crush` treats it as an
uninterpreted symbol and cannot prove `mystery 3 = 4`. The handler maps
`mystery n` to `(+ n 1)`, after which the goal is a linear-arithmetic identity. -/

opaque mystery : Int → Int

@[crush_translate]
def mysteryHandler : TranslationHandler := fun ctx => do
  let .const ``mystery _ := ctx.fn | return none
  match ctx.args with
  | #[n] => return some (.symbApp "+" #[← ctx.emitTerm n, .lit (.num 1)])
  | _ => return none

-- Provable only because the handler ran (an uninterpreted `mystery` could be
-- anything, so a countermodel with `mystery 3 ≠ 4` would otherwise exist).
theorem handler_fires (h : mystery 3 = 4) : mystery 2 = 3 := by crush

/-! ## A handler overrides a built-in mapping

`Nat.succ n` has a built-in translation to `(+ n 1)`. This handler overrides it to
`(+ n 2)`. The theorem below is *false* under the built-in (`n + 1 = 5 ⇒ n = 4 ≠ 3`)
and *true* under the override (`n + 2 = 5 ⇒ n = 3`), so it elaborates only if the
handler took precedence over the built-in. -/

@[crush_translate high]
def succOverride : TranslationHandler := fun ctx => do
  let .const ``Nat.succ _ := ctx.fn | return none
  match ctx.args with
  | #[n] => return some (.symbApp "+" #[← ctx.emitTerm n, .lit (.num 2)])
  | _ => return none

theorem handler_overrides_builtin (n : Nat) (h : Nat.succ n = 5) : n = 3 := by crush

/-! ## The `crush_map` sugar also runs on the handler path

`crush_map` desugars to a handler, so it participates in the same dispatch. It maps a
constant to an SMT-LIB *theory* symbol (which needs no `declare-fun`); here the
otherwise-uninterpreted `Int.natAbs` is mapped to SMT's built-in `abs`. Congruence
through it holds, confirming the sugar-generated handler fired. -/

crush_map Int.natAbs => "abs"

theorem sugar_handler_congruence (a b : Int) (h : a = b) :
    Int.natAbs a = Int.natAbs b := by crush
