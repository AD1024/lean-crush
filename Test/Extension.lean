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

/-! ## SMT-LIB term quotations

The `(smt| ...)` quotation expands nested SMT-LIB syntax into the typed SMT term IR.
`$t` splices an existing `SMT.Term`; literals and symbols need no constructors. -/

open Crush.SMT

def quotationExample (x : SMT.Term) : SMT.Term :=
  (smt| (ite (> $x 0) 1 (ite (= $x 0) 0 (- 1))))

#guard toString (quotationExample (.const "x")) =
  "(ite (> x 0) 1 (ite (= x 0) 0 (- 1)))"

#guard toString (smt| (and true (= "a" "a"))) = "(and true (= \"a\" \"a\"))"

#guard toString (smt| (str.++ "a" "b")) = "(str.++ \"a\" \"b\")"

#guard toString (smt| (= $(quotationExample (.const "x")) false)) =
  "(= (ite (> x 0) 1 (ite (= x 0) 0 (- 1))) false)"

/-! ## A head-indexed lowering fires

Unlike a general translation handler, this callback is considered only for
applications of `loweredMystery`; it does not need to inspect `ctx.fn`. -/

opaque loweredMystery : Int → Int

@[crush_lower loweredMystery]
def loweredMysteryHandler : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (+ $sx 3))

theorem targeted_lowering_fires (x : Int) : loweredMystery x = x + 3 := by crush

/-! ## A handler fires on an otherwise-uninterpreted constant

`mystery` has no built-in mapping, so without a handler `crush` treats it as an
uninterpreted symbol and cannot prove `mystery 3 = 4`. The handler maps
`mystery n` to `(+ n 1)`, after which the goal is a linear-arithmetic identity. -/

opaque mystery : Int → Int

@[crush_translate]
def mysteryHandler : TranslationHandler := fun ctx => do
  let .const ``mystery _ := ctx.fn | return none
  match ctx.args with
  | #[n] =>
    let sn ← ctx.emitTerm n
    return some (smt| (+ $sn 1))
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
  | #[n] =>
    let sn ← ctx.emitTerm n
    return some (smt| (+ $sn 2))
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

/-! ## The `crush_map_sort` sugar runs on the sort-handler path

`MappedInt` is representation-isomorphic to `Int`. Mapping its sort to SMT `Int`
and lowering its projection and arithmetic wrapper to identity/arithmetic is
therefore exact. If `crush_map_sort` were incorrectly registered as a term
handler, `x` below would retain a datatype sort and the generated `(+ x 1)` would
fail the SMT sort checker. -/

structure MappedInt where
  value : Int

namespace MappedInt

def next (x : MappedInt) : MappedInt :=
  ⟨x.value + 1⟩

end MappedInt

crush_map_sort MappedInt => "Int"

@[crush_lower MappedInt.value]
def mappedIntValue : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  return some (← ctx.emitTerm x)

@[crush_lower MappedInt.next]
def mappedIntNext : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (+ $sx 1))

theorem sort_sugar_fires (x : MappedInt) :
    (MappedInt.next x).value = x.value + 1 := by
  crush
