import Crush

open Lean Meta Crush

set_option linter.unusedVariables false

/-! Constructor productivity concerns recursive fields of the declaration.
Substituting a nested product for a type parameter must not make that parameter
look like an unproductive recursive field. Paxos updates depend on the resulting
SMT tuple constructors retaining injectivity. -/

private def isDeclaredDatatype (sort : SMT.SSort) (state : TranslateState) : Bool :=
  match sort with
  | .app (.symb name) _ => state.commands.any fun command =>
      match command with
      | .declDatatypes declarations => declarations.any fun declaration => declaration.1 == name
      | _ => false
  | _ => false

-- Check the translation directly: Lean's preliminary proof search can otherwise
-- close a tuple-injectivity theorem without exercising the SMT datatype path.
run_meta do
  let inner := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Bool) (mkConst ``Int)
  let outer := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Int) inner
  let (sort, state) ← TranslateM.run {} (emitSort outer)
  unless isDeclaredDatatype sort state do
    throwError "nested product lost its SMT datatype and constructor injectivity"

example (a b : Int) (x y : Bool) (m n : Int) (h : (a, x, m) = (b, y, n)) :
    a = b ∧ x = y ∧ m = n := by
  crush [h]

inductive ProductivityNoBase (α : Type) where
  | next : ProductivityNoBase α → α → ProductivityNoBase α

mutual
  inductive ProductivityLeft (α : Type) where
    | next : ProductivityRight α → α → ProductivityLeft α
  inductive ProductivityRight (α : Type) where
    | next : ProductivityLeft α → ProductivityRight α
end

-- Real recursion still needs a base constructor, including in generic and
-- mutually recursive declarations. An SMT datatype block cannot encode these
-- empty types, even when their nonrecursive parameter is inhabited.
run_meta do
  for name in [``ProductivityNoBase, ``ProductivityLeft, ``ProductivityRight] do
    let ty := mkApp (mkConst name) (mkConst ``Int)
    let ((sort, guard), state) ← TranslateM.run {} do
      let sort ← emitSort ty
      return (sort, ← wfCondition ty (.const "value"))
    if isDeclaredDatatype sort state then
      throwError "unproductive inductive was emitted as an SMT datatype: {name}"
    if guard.isNone then
      throwError "unproductive inductive lost its validity guard: {name}"

set_option crush.timeout 2 in
example (h : ∀ x : ProductivityNoBase Int, False) : True := by
  fail_if_success have : False := by crush [h]
  trivial

set_option crush.timeout 2 in
example (h : ∀ x : ProductivityLeft Int, False) : True := by
  fail_if_success have : False := by crush [h]
  trivial
