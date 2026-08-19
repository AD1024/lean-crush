import Crush

/-!
Regression tests for the pre-solver SMT sort validator.

The first two scripts model the P0 failures found during the Cedar evaluation:
using integer `<` at an opaque sort, and reusing a declared function at a different
arrow sort. Both must fail before a backend sees the script. A corresponding
uninterpreted relation is valid.
-/

open Crush.SMT

private def opaqueSort : SSort := .app (.symb "U") #[]
private def fnA : SSort := .app (.symb "FnA") #[]
private def fnB : SSort := .app (.symb "FnB") #[]

#eval show IO Unit from do
  let script : Array Command := #[
    .declSort "U" 0,
    .declFun "x" #[] opaqueSort,
    .assert (smt| (< x x))]
  match checkScript script with
  | .error error =>
    unless error.commandIndex == 2 && error.message.contains "expected `Int`" do
      throw <| IO.userError s!"unexpected checker error: {error}"
  | .ok () => throw <| IO.userError "ill-sorted integer comparison was accepted"

#eval show IO Unit from do
  let script : Array Command := #[
    .declSort "FnA" 0,
    .declSort "FnB" 0,
    .declFun "apply" #[fnA] (.app (.symb "Int") #[]),
    .declFun "f" #[] fnB,
    .assert (smt| (= (apply f) 0))]
  match checkScript script with
  | .error error =>
    unless error.commandIndex == 4 && error.message.contains "expected `FnA`" do
      throw <| IO.userError s!"unexpected checker error: {error}"
  | .ok () => throw <| IO.userError "incompatible declared application was accepted"

#eval show IO Unit from do
  let script : Array Command := #[
    .declSort "U" 0,
    .declFun "ltU" #[opaqueSort, opaqueSort] (.app (.symb "Bool") #[]),
    .declFun "x" #[] opaqueSort,
    .assert (smt| (=> (ltU x x) (ltU x x)))]
  match checkScript script with
  | .ok () => pure ()
  | .error error => throw <| IO.userError s!"valid uninterpreted relation failed: {error}"

#eval show IO Unit from do
  let tooHigh := String.singleton (Char.ofNat 0x30000)
  for command in [Command.assert (.lit (.str tooHigh)), .echo tooHigh] do
    match checkScript #[command] with
    | .error error =>
      unless error.message.contains "outside SMT-LIB 2.6" do
        throw <| IO.userError s!"unexpected string validation error: {error}"
    | .ok () => throw <| IO.userError "out-of-range SMT string codepoint was accepted"

#eval show IO Unit from do
  let script : Array Command := #[
    .defSort "Alias" #["T"] (.app (.symb "Array")
      #[.bvar 0, .app (.symb "Int") #[]]),
    .declFun "a" #[] (.app (.symb "Alias") #[opaqueSort]),
    .declFun "x" #[] opaqueSort,
    .assert (.app (.symb "=") #[
      .app (.symb "select") #[.const "a", .const "x"],
      .lit (.num 0)])]
  match checkScript script with
  | .ok () => pure ()
  | .error error =>
    throw <| IO.userError s!"parameterized sort alias was not expanded: {error}"

#eval show IO Unit from do
  let aliasSort : SSort := .app (.symb "IntAlias") #[]
  let script : Array Command := #[
    .defSort "IntAlias" #[] (.app (.symb "Int") #[]),
    .defFunsRec #[{
      name := "countdown"
      args := #[("n", aliasSort)]
      resSort := aliasSort
      body := (smt| (+ n 0))
    }]]
  match checkScript script with
  | .ok () => pure ()
  | .error error =>
    throw <| IO.userError s!"recursive definition did not resolve sort aliases: {error}"

#eval show IO Unit from do
  let intSort : SSort := .app (.symb "Int") #[]
  let script : Array Command := #[
    .declFun "x" #[] intSort,
    .declFun "y" #[] intSort,
    .declFun "z" #[] intSort,
    .assert (smt| (distinct x y z))]
  match checkScript script with
  | .ok () => pure ()
  | .error error =>
    throw <| IO.userError s!"valid variadic `distinct` failed: {error}"

#eval show IO Unit from do
  let script : Array Command := #[
    .declFun "x" #[] (.app (.symb "Int") #[]),
    .assert (smt| (distinct x))]
  match checkScript script with
  | .error error =>
    unless error.message.contains "at least two" do
      throw <| IO.userError s!"unexpected unary `distinct` error: {error}"
  | .ok () => throw <| IO.userError "unary `distinct` was accepted"

#eval show IO Unit from do
  let bitVec3 : SSort := .app (.indexed "BitVec" #[.inr 3]) #[]
  let script : Array Command := #[
    .declFun "x" #[] bitVec3,
    .declFun "y" #[] bitVec3,
    .assert (smt| (and (bvsgt x y) (bvsge x y)))]
  match checkScript script with
  | .ok () => pure ()
  | .error error =>
    throw <| IO.userError s!"valid signed comparison aliases failed: {error}"
