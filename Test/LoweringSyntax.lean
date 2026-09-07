import Test.LoweringSyntaxImport

open Lean Meta Crush Crush.SMT

namespace LoweringSyntaxTest

def bump (x : Int) : Int := x + 3

register_lowering term <<
  (bump (term x)) => (smt| (+ $x 3))
>>

def lowerRaw (x : Expr) : TranslateM SMT.Term := do
  let x ← emitTerm x
  return (smt| (+ $x 4))

def bumpRaw (x : Int) : Int := x + 4

register_lowering term <<
  (bumpRaw x) => lowerRaw x
>>

structure Indexed (index : Int) where
  value : Int

def indexedValue (index : Int) : Indexed index := ⟨index⟩

register_lowering sort <<
  (Indexed _) => (smt| Int)
>>

register_lowering result-type <<
  (Indexed (term index)) => do
    unless ctx.fn.isConstOf ``indexedValue && ctx.args.size == 1 do return none
    return some (smt| $index)
>>

structure Map (key value : Type) where
  get : key → value

register_lowering sort <<
  (Map (sort key) (sort value)) => (smt| (Array $key $value))
>>

private def checkTerm (value : Expr) (expected : String) : MetaM Unit := do
  let (actual, _) ← TranslateM.run {} (emitTerm value)
  unless toString actual == expected do
    throwError "expected {expected}, got {actual}"

run_meta do
  checkTerm (mkApp (mkConst ``bump) (mkIntLit 2)) "(+ 2 3)"
  checkTerm (mkApp (mkConst ``bumpRaw) (mkIntLit 2)) "(+ 2 4)"
  checkTerm (mkApp (mkConst ``indexedValue) (mkIntLit 7)) "7"
  let (sort, _) ← TranslateM.run {} <|
    emitSort (mkApp2 (mkConst ``Map) (mkConst ``Int) (mkConst ``Bool))
  unless toString sort == "(Array Int Bool)" do
    throwError "unexpected sort: {sort}"

example (x : Int) : bump x = x + 3 := by crush
example (x : Int) : bumpRaw x = x + 4 := by crush

-- Private generated handlers remain available after importing their module.
example (x : Int) : LoweringSyntaxImported.increment x = x + 1 := by crush

def pureTemplate (x : SMT.Term) : SMT.Term := (smt| (+ $x 5))
def bumpPure (x : Int) : Int := x + 5

register_lowering term << (bumpPure (term x)) => pureTemplate x >>

def bumpDo (x : Int) : Int := x + 6

register_lowering term <<
  (bumpDo x) => do
    let x ← ctx.emitTerm x
    return (smt| (+ $x 6))
>>

def typed {α : Type} (x : α) : α := x

-- Exact constant patterns are parenthesized; bare identifiers capture Exprs.
register_lowering term low << (typed (Int) (term x)) => (smt| (+ $x 0)) >>
register_lowering term high << (typed _ (term x : Int)) => (smt| $x) >>

-- A named metaprogram can decline, preserving lower-priority dispatch.
def decline : TranslateM (Option SMT.Term) := pure none
register_lowering term 2000 << (typed _ _) => decline >>

def nested (x y : Nat) : Nat := x + y

register_lowering term <<
  (nested (term x) (Nat.succ (term y))) => (smt| (+ $x (+ $y 1)))
>>

def guardedType {α : Type} (x : α) : α := x
register_lowering term << (guardedType _ (term x : Int)) => (smt| $x) >>

private def handlerResult (head : Name) (expression : Expr) :
    MetaM (Option SMT.Term × TranslateState) :=
  TranslateM.run {} do
    let handlers ← getLoweringsFor head
    let some handler := handlers[0]? | throwError "missing handler"
    handler {
      fn := expression.getAppFn
      args := expression.getAppArgs
      emitTerm := fun _ => throwError "a declined pattern translated a capture"
      emitSort := fun _ => throwError "a declined pattern translated a sort"
      declare := declareViaThunk }

run_meta do
  checkTerm (mkApp (mkConst ``bumpPure) (mkIntLit 2)) "(+ 2 5)"
  checkTerm (mkApp (mkConst ``bumpDo) (mkIntLit 2)) "(+ 2 6)"
  checkTerm (mkApp2 (mkConst ``typed [.zero]) (mkConst ``Int) (mkIntLit 2)) "2"
  checkTerm (mkApp2 (mkConst ``nested) (mkNatLit 2)
    (mkApp (mkConst ``Nat.succ) (mkNatLit 3))) "(+ 2 (+ 3 1))"
  -- Wrong arity and a late nested mismatch both decline before translating x.
  for expression in #[mkConst ``nested, mkApp (mkConst ``nested) (mkNatLit 2),
      mkApp2 (mkConst ``nested) (mkNatLit 2) (mkNatLit 0)] do
    let (result, state) ← handlerResult ``nested expression
    unless result.isNone && state.commands.isEmpty do
      throwError "a mismatched pattern was accepted or emitted commands"
  let (result, state) ← handlerResult ``guardedType <|
    mkApp2 (mkConst ``guardedType [.zero]) (mkConst ``Bool) (mkConst ``Bool.true)
  unless result.isNone && state.commands.isEmpty do
    throwError "a mismatched type was accepted or emitted commands"

-- Same-priority registration names must not collide, and open namespaces resolve
-- constants at registration rather than at the eventual tactic call.
open LoweringSyntaxImported in
register_lowering term high << (increment (term x)) => (smt| (+ $x 1)) >>

structure Byte where
  value : BitVec 8

register_lowering sort << Byte => (smt| (_ BitVec 8)) >>

structure SortViaHelper where
  value : Int

private def intSort : TranslateM SSort := return (smt| Int)
register_lowering sort << SortViaHelper => intSort >>

structure SortViaDo where
  value : Int

register_lowering sort << SortViaDo => do return (smt| Int) >>

run_meta do
  for (name, expected) in #[(``Byte, "(_ BitVec 8)"),
      (``SortViaHelper, "Int"), (``SortViaDo, "Int")] do
    let (sort, _) ← TranslateM.run {} (emitSort (mkConst name))
    unless toString sort == expected do throwError "unexpected sort: {sort}"
  let sort : SSort := (smt| (Array Int (_ BitVec 8)))
  unless toString sort == "(Array Int (_ BitVec 8))" do
    throwError "sort quotation lost its nested/indexed structure"

-- Dynamic result-family matching is independent of the term's application head.
structure Family (α : Type) where
  value : α

register_lowering sort << (Family (sort α)) => (smt| $α) >>

def familyValue (x : Int) : Family Int := ⟨x⟩

register_lowering result-type <<
  (Family (Int)) => do
    let #[x] := ctx.args | return none
    unless ctx.fn.isConstOf ``familyValue do return none
    return some (← ctx.emitTerm x)
>>

run_meta do
  checkTerm (mkApp (mkConst ``familyValue) (mkIntLit 9)) "9"

-- A general translation handler still takes precedence over the DSL's registry.
@[crush_translate]
def generalOverride : TranslationHandler := fun ctx => do
  unless ctx.fn.isConstOf ``bump do return none
  let #[x] := ctx.args | return none
  let x ← ctx.emitTerm x
  return some (smt| (+ $x 3 0))

run_meta do
  checkTerm (mkApp (mkConst ``bump) (mkIntLit 2)) "(+ 2 3 0)"

/-- error: duplicate lowering capture -/
#guard_msgs(error, substring := true) in
register_lowering term << (nested x (term x)) => (smt| 0) >>

/-- error: a lowering pattern must have a constant application head -/
#guard_msgs(error, substring := true) in
register_lowering term << _ => (smt| 0) >>

/-- error: `ctx` is reserved -/
#guard_msgs(error, substring := true) in
register_lowering term << (bump ctx) => (smt| 0) >>

/-- error: Unknown constant -/
#guard_msgs(error, substring := true) in
register_lowering term << (missingLoweringConstant x) => (smt| 0) >>

/-- error: expected an SMT sort, not a term literal -/
#guard_msgs(error, substring := true) in
register_lowering sort << Byte => (smt| 5) >>

/-- error: Application type mismatch -/
#guard_msgs(error, substring := true) in
register_lowering term << (bump x) => (smt| $x) >>

-- A false SMT verdict from a custom lowering must still fail checked replay.
def bad (x : Int) : Int := x
register_lowering term << (bad (term x)) => (smt| (+ $x 1)) >>

/-- error: crush: -/
#guard_msgs(error, substring := true) in
set_option crush.trust "reconstruct" in
example (x : Int) : bad x = x + 1 := by crush

set_option crush.backend "cvc5" in
set_option crush.trust "reconstruct" in
set_option crush.reconstruct "alethe" in
theorem checkedLowering (x : Int) : bumpDo x = x + 6 := by crush

/-- info: 'LoweringSyntaxTest.checkedLowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkedLowering

end LoweringSyntaxTest
