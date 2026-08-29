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

/-! ## Axiom-free certified definition lowering

A defined mapping supplies no SMT body.  The fixed dispatcher delta-reduces the
actual Lean definition and translates the kernel-equivalent result. -/

#guard_msgs(error, substring := true) in
@[crush_certified_def]
opaque invalidCertifiedDef : Prop → Prop

@[crush_certified_def]
def releaseReady (testsPassed reviewApproved : Prop) : Prop :=
  testsPassed ∧ reviewApproved

@[crush_certified_def]
def certifiedCountdown : Nat → Nat
  | 0 => 0
  | n + 1 => certifiedCountdown n

#guard_msgs(error, substring := true) in
example (n : Nat) : certifiedCountdown n = 0 := by
  crush

set_option crush.trust "reconstruct" in
theorem certified_definition_fires (testsPassed reviewApproved : Prop)
    (ready : releaseReady testsPassed reviewApproved) :
    testsPassed ∧ reviewApproved := by
  crush

example : True := by
  run_tac
    let expression := Lean.mkApp2 (Lean.mkConst ``releaseReady)
      (Lean.mkConst ``True) (Lean.mkConst ``False)
    let (translated, state) ← TranslateM.run {} (emitTerm expression)
    unless toString translated == "(and true false)" do
      throwError "certified definition did not lower through its Lean body"
    unless state.commands.isEmpty do
      throwError "definition lowering unexpectedly introduced an SMT assumption"
    unless state.certifiedHookUses.isEmpty do
      throwError "definition lowering was incorrectly audited as an external SMT hook"
    let definitions := crushCertifiedDefExt.getState (← Lean.getEnv)
    unless definitions.contains ``releaseReady do
      throwError "certified definition was not registered"
  trivial

/-! ## Certified definition lowering with integer arithmetic -/

@[crush_certified_def]
def intMax (a b : Int) : Int :=
  if a ≥ b then a else b

set_option crush.trust "reconstruct" in
theorem certified_intMax3 (a b c : Int) :
    let greatest := intMax a (intMax b c)
    a ≤ greatest ∧ b ≤ greatest ∧ c ≤ greatest ∧
      (greatest = a ∨ greatest = b ∨ greatest = c) := by
  dsimp only
  crush using (simp_all [intMax]; grind)

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

@[crush_translate_head loweredMystery]
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

@[crush_translate_head MappedInt.value]
def mappedIntValue : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  return some (← ctx.emitTerm x)

@[crush_translate_head MappedInt.next]
def mappedIntNext : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (+ $sx 1))

theorem sort_sugar_fires (x : MappedInt) :
    (MappedInt.next x).value = x.value + 1 := by
  crush

/-! ## A result-indexed lowering fires

This is the executable counterpart of the Verso example. The term handler is
selected from `IndexedInt index`, while the sort handler keeps the dependent
family's representation aligned with SMT `Int`. -/

structure IndexedInt (index : Int) where
  value : Int

def indexedInt (index : Int) : IndexedInt index :=
  ⟨index⟩

@[crush_translate_sort]
def translateIndexedIntSort : SortHandler := fun ctx => do
  let .const ``IndexedInt _ := ctx.fn
    | return none
  let #[_] := ctx.args | return none
  return some (.app (.symb "Int") #[])

@[crush_translate_family IndexedInt]
def lowerIndexedInt : LoweringHandler := fun ctx => do
  let .const ``indexedInt _ := ctx.fn
    | return none
  let #[index] := ctx.args | return none
  return some (← ctx.emitTerm index)

@[crush_translate_head IndexedInt.value]
def lowerIndexedIntValue : LoweringHandler := fun ctx => do
  let #[_, value] := ctx.args | return none
  return some (← ctx.emitTerm value)

theorem result_lowering_fires (index : Int) :
    (indexedInt index).value = index := by
  crush

/-! ## A sort handler can target a `def`-defined type

`emitSort` offers the type to handlers before normalizing it, so an alias introduced by
`def` is a usable dispatch key. Normalizing first would unfold the alias and hand the
handler its expansion instead. -/

structure BoxedInt where
  contents : Int

def AliasedInt := BoxedInt

def aliasedValue (a : AliasedInt) : Int := a.contents

-- Claims the alias for SMT `Int`; `BoxedInt` itself is left to the datatype path.
@[crush_translate_sort]
def translateAliasedIntSort : SortHandler := fun ctx => do
  let .const ``AliasedInt _ := ctx.fn | return none
  return some (.app (.symb "Int") #[])

@[crush_translate_head aliasedValue]
def lowerAliasedValue : LoweringHandler := fun ctx => do
  let #[a] := ctx.args | return none
  return some (← ctx.emitTerm a)

theorem alias_sort_handler_fires (a : AliasedInt) (h : aliasedValue a = 0) :
    aliasedValue a + 1 = 1 := by
  crush
