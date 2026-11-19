import Crush.Solver.Alethe.Term

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

/-- A context with a `:named` cache, over `named` and `symbols`. -/
private def cachedCtx (named : List (String × String)) (symbols : Std.HashMap String Expr := {}) :
    MetaM TermCtx := do
  let mut defs : Std.HashMap String Sexp := {}
  for (name, source) in named do
    defs := defs.insert name (← parseTerm source)
  return { symbols, named := defs, namedCache := some (← NamedCache.new) }

-- A cached `:named` term is reused only within its fuel need, whatever ran first.
run_meta do
  let chain := [("@a", "@b"), ("@b", "@c"), ("@c", "true")]
  if (← toExpr? (← cachedCtx chain) 2 (.atom "@a")).isSome then
    throwError "decoded `@a` beyond its fuel"
  let ctx ← cachedCtx chain
  unless (← toExpr? ctx 2 (.atom "@b")).isSome do
    throwError "failed to decode `@b`"
  if (← toExpr? ctx 2 (.atom "@a")).isSome then
    throwError "a cached `@b` let `@a` exceed its fuel"
  unless (← toExpr? ctx 3 (.atom "@a")).isSome do
    throwError "failed to decode `@a` with enough fuel"
  -- The need of a bit pattern counts its expanded names.
  withLocalDeclD `x (bitVecType 2) fun x => do
    let pattern := [("@v", "(@bbterm @b0 @b1)"), ("@b0", "@d0"), ("@d0", "((_ @bit_of 0) x)"),
      ("@b1", "((_ @bit_of 1) x)"), ("@u", "@v")]
    let symbols := (({} : Std.HashMap String Expr).insert "x" x)
    if (← toExpr? (← cachedCtx pattern symbols) 3 (.atom "@u")).isSome then
      throwError "decoded `@u` beyond its fuel"
    let ctx ← cachedCtx pattern symbols
    unless (← toExpr? ctx 3 (.atom "@v")).isSome do
      throwError "failed to decode `@v`"
    if (← toExpr? ctx 3 (.atom "@u")).isSome then
      throwError "a cached bit pattern let `@u` exceed its fuel"

-- A bit pattern decodes its operands through the cache: a 40-level chain, each level
-- naming its predecessor twice. Inline and named operands still form one pattern.
run_meta do
  withLocalDeclD `x (bitVecType 2) fun x => do
    let mut chain := [("@p0", "(bvand x x)")]
    for i in [1:41] do
      chain := (s!"@p{i}", s!"(bvand @p{i-1} @p{i-1})") :: chain
    let symbols := (({} : Std.HashMap String Expr).insert "x" x)
    let ctx ← cachedCtx chain symbols
    let some direct ← toExpr? ctx 64 (.atom "@p40") | throwError "failed to decode `@p40`"
    let some bits ← toExpr? ctx 64 (← parseTerm "(@bbterm ((_ @bit_of 0) @p40) ((_ @bit_of 1) @p40))")
      | throwError "failed to decode the bit pattern over `@p40`"
    unless bits == direct do throwError "the bit pattern did not decode to `@p40`"
    let some mixed ← toExpr? ctx 64
        (← parseTerm "(@bbterm (not ((_ @bit_of 0) (bvand x x))) (not ((_ @bit_of 1) @p0)))")
      | throwError "failed to decode a bit pattern with inline and named operands"
    unless mixed.isAppOf ``BitVec.not do
      throwError "inline and named operands did not form one pattern: {mixed}"
    -- A bit that is a 40-level DAG of named connectives is decoded bit by bit.
    let mut dag := [("@q0", "((_ @bit_of 0) x)")]
    for i in [1:41] do
      dag := (s!"@q{i}", s!"(and @q{i-1} @q{i-1})") :: dag
    let some wide ← toExpr? (← cachedCtx dag symbols) 64
        (← parseTerm "(@bbterm @q40 ((_ @bit_of 1) x))")
      | throwError "failed to decode a bit-blasted term over a connective DAG"
    unless wide.isAppOf ``BitVec.ofBoolListLE do
      throwError "a connective DAG decoded as a whole-vector operation: {wide}"
    -- Bits that are parallel 40-level DAGs of named connectives decode as one operation.
    let mut parallel := [("@r0", "((_ @bit_of 1) x)")] ++ dag
    for i in [1:41] do
      parallel := (s!"@r{i}", s!"(and @r{i-1} @r{i-1})") :: parallel
    let some whole ← toExpr? (← cachedCtx parallel symbols) 64 (← parseTerm "(@bbterm @q40 @r40)")
      | throwError "failed to decode parallel connective DAGs"
    unless whole.isAppOf ``BitVec.and do
      throwError "parallel connective DAGs did not decode as `BitVec.and`: {whole}"

/-- Decode `source` over `x y : BitVec 2`, and compare it with `expected x y`, or with a
bit list if `expected` is `none`. -/
private def assertBitVector (source : String)
    (expected : Option (Expr → Expr → MetaM Expr) := none) : MetaM Unit := do
  let ty := bitVecType 2
  withLocalDeclD `x ty fun x => withLocalDeclD `y ty fun y => do
    let symbols := ((({} : Std.HashMap String Expr).insert "x" x).insert "y" y)
    let some value ← toExpr? { symbols, named := {} } 64 (← parseTerm source)
      | throwError "failed to decode `{source}`"
    let some expected := expected
      | unless value.isAppOf ``BitVec.ofBoolListLE do
          throwError "`{source}` decoded as `{value}`, expected a bit list"
    let expected ← expected x y
    unless value == expected do
      throwError "`{source}` decoded as `{value}`, expected `{expected}`"

-- Each connective's decoded bits read as the whole-vector operation.
run_meta do
  let bits (f : Nat → String) := s!"(@bbterm {f 0} {f 1})"
  let bit (v : String) (i : Nat) := s!"((_ @bit_of {i}) {v})"
  assertBitVector (bits fun i => s!"(and {bit "x" i} {bit "y" i})")
    (some fun x y => mkAppM ``BitVec.and #[x, y])
  assertBitVector (bits fun i => s!"(or {bit "x" i} {bit "y" i})")
    (some fun x y => mkAppM ``BitVec.or #[x, y])
  assertBitVector (bits fun i => s!"(not {bit "x" i})")
    (some fun x _ => mkAppM ``BitVec.not #[x])
  -- `xor` of `Bool` bits decodes as `Bool.xor`, of `Prop` bits as `¬(p ↔ q)`.
  assertBitVector (bits fun i => s!"(xor {bit "x" i} {bit "y" i})")
    (some fun x y => mkAppM ``BitVec.xor #[x, y])
  assertBitVector (bits fun i => s!"(xor (not {bit "x" i}) {bit "y" i})")
    (some fun x y => do mkAppM ``BitVec.xor #[← mkAppM ``BitVec.not #[x], y])
  -- `and` with three operands nests to the right.
  assertBitVector (bits fun i => s!"(and {bit "x" i} {bit "y" i} (not {bit "x" i}))")
    (some fun x y => do
      mkAppM ``BitVec.and #[x, ← mkAppM ``BitVec.and #[y, ← mkAppM ``BitVec.not #[x]]])
  -- A width mismatch, an index out of place, or swapped operands leave a bit list.
  assertBitVector s!"(@bbterm {bit "x" 0})"
  assertBitVector s!"(@bbterm {bit "x" 1} {bit "x" 0})"
  assertBitVector (bits fun i =>
    if i == 0 then s!"(and {bit "x" i} {bit "y" i})" else s!"(and {bit "y" i} {bit "x" i})")

-- A bit-blasted term nested inline in its own first bit decodes each level once.
run_meta do
  let mut term := Sexp.atom "#b00"
  for _ in [:30] do
    term := .list #[.atom "@bbterm", .list #[.list #[.atom "_", .atom "@bit_of", .atom "0"], term],
      .atom "true"]
  let decode := toExpr? ({ symbols := {}, named := {} } : TermCtx) 64 term
  -- About 2000 heartbeats a level; decoding a level twice would double each one.
  let some value ← withCurrHeartbeats <|
      withTheReader Core.Context ({ · with maxHeartbeats := 1000000 }) decode
    | throwError "failed to decode a nested bit-blasted term"
  unless value.isAppOf ``BitVec.ofBoolListLE do
    throwError "a nested bit-blasted term decoded as `{value}`"
