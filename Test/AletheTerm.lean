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
  for op in ["bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"] do
    assertTermType s!"({op} #b000 #b001)" (mkConst ``Bool)
  assertTermEq "(int.ispow2 8)" (mkConst ``True)
  assertTermEq "(int.ispow2 6)" (mkConst ``False)
  assertTermEq "(int.log2 8)" (Lean.toExpr (3 : Int))
  withLocalDeclD `x (bitVecType 3) fun x => do
    let ctx : TermCtx := {
      symbols := ({} : Std.HashMap String Expr).insert "x" x
      named := {}
    }
    let term ← parseTerm
      "(@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x) ((_ @bit_of 2) x))"
    let some value ← toExpr? ctx 64 term
      | throwError "failed to decode symbolic Alethe `@bbterm`"
    unless ← isDefEq value x do
      throwError "symbolic Alethe `@bbterm` did not recover its source vector"
  withLocalDeclD `low (mkConst ``Bool) fun low =>
    withLocalDeclD `high (mkConst ``Bool) fun high => do
      let ctx : TermCtx := {
        symbols := (({} : Std.HashMap String Expr).insert "low" low).insert "high" high
        named := {}
      }
      let term ← parseTerm "(@bbterm low high)"
      let some value ← toExpr? ctx 64 term
        | throwError "failed to assemble symbolic Alethe `@bbterm` bits"
      let expected ←
        mkAppM ``BitVec.ofBoolListLE #[← mkListLit (mkConst ``Bool) [low, high]]
      unless ← isDefEq value expected do
        throwError "symbolic Alethe `@bbterm` bits were assembled in the wrong order"
  withLocalDeclD `p (mkConst ``Bool) fun p =>
    withLocalDeclD `q (mkConst ``Bool) fun q => do
      let ctx : TermCtx := {
        symbols := (({} : Std.HashMap String Expr).insert "p" p).insert "q" q
        named := {}
      }
      let nestedOr ← parseTerm "(or p q)"
      let some literals ← clauseLiteralsToExprs? ctx 64 #[nestedOr]
        | throwError "failed to decode an Alethe clause containing Boolean `or`"
      unless literals.size == 1 && literals[0]!.isAppOfArity ``Or 2 do
        throwError "Boolean `or` was confused with the enclosing Alethe clause"
  withLocalDeclD `x (mkConst ``Int) fun x =>
    withLocalDeclD `y (mkConst ``Int) fun y =>
      withLocalDeclD `z (mkConst ``Int) fun z => do
        let ctx : TermCtx := {
          symbols := ((({} : Std.HashMap String Expr).insert "x" x).insert "y" y).insert "z" z
          named := {}
        }
        let term ← parseTerm "(distinct x y z)"
        let some value ← toExpr? ctx 64 term
          | throwError "failed to decode variadic SMT `distinct`"
        let xy ← mkAppM ``Not #[← mkEq x y]
        let xz ← mkAppM ``Not #[← mkEq x z]
        let yz ← mkAppM ``Not #[← mkEq y z]
        let expected ← mkAppM ``And #[xy, ← mkAppM ``And #[xz, yz]]
        unless ← isDefEq value expected do
          throwError "SMT `distinct` did not decode to canonical pairwise inequalities"
