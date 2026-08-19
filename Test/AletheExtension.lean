import Crush

/-!
End-to-end coverage for custom lowering inversion during Alethe replay.
-/

open Lean Meta
open Crush Crush.Alethe Crush.SMT

def MultipleOfThree (value : Int) : Prop :=
  value % 3 = 0

@[crush_lower MultipleOfThree]
def lowerMultipleOfThree : LoweringHandler := fun ctx => do
  let #[value] := ctx.args | return none
  let value ← ctx.emitTerm value
  return some (.app (.indexed "divisible" #[.inr 3]) #[value])

private def intIndex? : Sexp → Option Expr
  | .atom value => value.toInt?.map Lean.toExpr
  | _ => none

@[crush_alethe "divisible"]
def decodeDivisible : AletheDecoder := fun ctx => do
  let pair? :=
    match ctx.indices, ctx.args with
    | #[index], #[value] => (intIndex? index).map fun divisor => (divisor, value)
    | #[], #[divisor, value] => some (divisor, value)
    | _, _ => none
  let some (divisor, value) := pair? | return none
  let remainder ← mkAppM ``HMod.hMod #[value, divisor]
  return some (← mkEq remainder (Lean.toExpr (0 : Int)))

private def parseTerm (source : String) : MetaM Sexp := do
  let some (term, rest) := parseSexp source
    | throwError "failed to parse Alethe term `{source}`"
  unless rest.trimAscii.isEmpty do
    throwError "trailing input after Alethe term `{source}`"
  return term

private def assertDecoded (symbols : Std.HashMap String Expr)
    (source : String) (expected : Expr) : MetaM Unit := do
  let decoders ← getAletheDecoders
  let context : TermCtx := { symbols, named := {}, decoders }
  let some actual ← toExpr? context 64 (← parseTerm source)
    | throwError "failed to decode Alethe term `{source}`"
  unless ← isDefEq actual expected do
    throwError "Alethe term `{source}` decoded as `{actual}`, expected `{expected}`"

run_meta do
  unless ← hasAletheDecodersFor "divisible" do
    throwError "the `divisible` Alethe decoder was not registered"
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let remainder ← mkAppM ``HMod.hMod #[x, Lean.toExpr (3 : Int)]
    let expected ← mkEq remainder (Lean.toExpr (0 : Int))
    let symbols := ({} : Std.HashMap String Expr).insert "x" x
    assertDecoded symbols "((_ divisible 3) x)" expected
    assertDecoded symbols "(divisible 3 x)" expected

section Replay

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option crush.timeout 10

theorem custom_divisibility_replay (x : Int)
    (hx : MultipleOfThree x) :
    ¬x % 3 ≠ 0 := by
  crush

#print axioms custom_divisibility_replay

end Replay
