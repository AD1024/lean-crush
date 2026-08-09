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
