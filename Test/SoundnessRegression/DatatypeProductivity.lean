import Crush

/-!
Constructor productivity follows recursive fields of the declaration. Nested type
parameters must retain SMT datatype constructors and their injectivity; genuine
recursion without a base constructor must retain an empty-carrier guard, including
in generic and mutually recursive declarations.
-/

open Lean Meta Crush

set_option linter.unusedVariables false

private def isDeclaredDatatype (sort : SMT.SSort) (state : TranslateState) : Bool :=
  match sort with
  | .app (.symb name) _ => state.commands.any fun command =>
      match command with
      | .declDatatypes declarations => declarations.any fun declaration => declaration.1 == name
      | _ => false
  | _ => false

-- Inspect translation directly so preliminary proof search cannot mask the datatype path.
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

-- An inhabited parameter does not supply a missing base constructor.
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
