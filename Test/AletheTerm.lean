import Crush.Solver.AletheTerm

/-!
Focused tests for cvc5 Alethe term forms. Live certificate replay is exercised in
`Test/AletheReplay.lean`; these checks keep decoder coverage stable when cvc5 rewrites
an integration proof differently.
-/

open Lean Meta
open Crush.Alethe Crush.SMT

private def parseTerm (source : String) : MetaM Sexp := do
  let some (term, rest) := parseSexp source
    | throwError "failed to parse Alethe term `{source}`"
  unless rest.trimAscii.isEmpty do
    throwError "trailing input after Alethe term `{source}`"
  return term

private def assertTermType (source : String) (expected : Expr) : MetaM Unit := do
  let term ← parseTerm source
  let some value ← toExpr? ({ symbols := {}, named := {} } : TermCtx) 64 term
    | throwError "failed to decode Alethe term `{source}`"
  let actual ← inferType value
  unless ← isDefEq actual expected do
    throwError "Alethe term `{source}` has type `{actual}`, expected `{expected}`"

private def assertTermEq (source : String) (expected : Expr) : MetaM Unit := do
  let term ← parseTerm source
  let some value ← toExpr? ({ symbols := {}, named := {} } : TermCtx) 64 term
    | throwError "failed to decode Alethe term `{source}`"
  unless ← isDefEq value expected do
    throwError "Alethe term `{source}` decoded as `{value}`, expected `{expected}`"

private def bitVecType (width : Nat) : Expr :=
  mkApp (mkConst ``BitVec) (mkNatLit width)

run_meta do
  let bv8 := bitVecType 8
  assertTermType "(bvshl #x01 #x01)" bv8
  assertTermType "(bvlshr #x80 #x01)" bv8
  assertTermType "(bvashr #x80 #x01)" bv8
  assertTermType "(rotate_left 3 #x01)" bv8
  assertTermType "((_ rotate_right 3) #x01)" bv8
  assertTermType "(extract 7 0 #x01)" bv8
  assertTermType "((_ extract 7 0) #x01)" bv8
  assertTermType "(zero_extend 4 #x01)" (bitVecType 12)
  assertTermType "((_ sign_extend 4) #x01)" (bitVecType 12)
  assertTermType "(concat #x0 #x0)" bv8
  assertTermType "(int_to_bv 8 1)" bv8
  assertTermType "((_ int_to_bv 8) 1)" bv8
  assertTermType "(ubv_to_int #x01)" (mkConst ``Int)
  assertTermType "(@bbterm false true)" (bitVecType 2)
  assertTermEq "(int.ispow2 8)" (mkConst ``True)
  assertTermEq "(int.ispow2 6)" (mkConst ``False)
  assertTermEq "(int.log2 8)" (Lean.toExpr (3 : Int))
