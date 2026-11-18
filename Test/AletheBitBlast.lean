import Crush

/-!
Checked replay of cvc5's bit-blasted addition, multiplication and equality. The steps
below are cvc5 1.3.4 certificate steps with their `:named` subterms expanded.
-/

open Lean Meta Elab Tactic Crush Crush.Alethe

namespace AletheBitBlast

/-- Decode `clause` over `x y : BitVec w` (or `type`) and run the registered handlers for
`rule`. Returns whether a proof of the decoded step came back. -/
def replayStep (w : Nat) (rule clause : String) (type? : Option Expr := none) :
    TacticM Bool := do
  let some (term, _) := SMT.parseSexp clause | throwError "unparsable test step"
  let type := type?.getD (mkApp (mkConst ``BitVec) (mkNatLit w))
  withLocalDeclD `x type fun x => withLocalDeclD `y type fun y => do
    let symbols : Std.HashMap String Expr := ((∅ : Std.HashMap String Expr).insert "x_0" x).insert "y_1" y
    let ctx : TermCtx := { symbols, named := {} }
    let some target ← toExpr? ctx 64 term | throwError "undecodable test step"
    let registry ← getReplayRuleHandlers
    let some proof ← runReplayRuleHandlers registry {
        stepId := "test"
        rule
        target
        targetLiterals := #[target]
        premises := #[]
        args := #[]
        decodeTerm := fun _ => pure none
        decodeSort := fun _ => pure none
        toProp := pure }
      | return false
    unless ← isDefEq (← inferType proof) target do
      throwError "the replayed proof does not prove the step"
    return true

def addStep : String := r#"
(= (bvadd (@bbterm ((_ @bit_of 0) x_0) ((_ @bit_of 1) x_0) ((_ @bit_of 2) x_0) ((_ @bit_of 3)
x_0)) (@bbterm ((_ @bit_of 0) y_1) ((_ @bit_of 1) y_1) ((_ @bit_of 2) y_1) ((_ @bit_of 3) y_1)))
(@bbterm (xor (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) false) (xor (xor ((_ @bit_of 1) x_0)
((_ @bit_of 1) y_1)) (or (and ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0)
x_0) ((_ @bit_of 0) y_1)) false))) (xor (xor ((_ @bit_of 2) x_0) ((_ @bit_of 2) y_1)) (or (and
((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (or
(and ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1))
false))))) (xor (xor ((_ @bit_of 3) x_0) ((_ @bit_of 3) y_1)) (or (and ((_ @bit_of 2) x_0) ((_
@bit_of 2) y_1)) (and (xor ((_ @bit_of 2) x_0) ((_ @bit_of 2) y_1)) (or (and ((_ @bit_of 1) x_0)
((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (or (and ((_ @bit_of 0)
x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) false)))))))))
"#

def mulStep : String := r#"
(= (bvmul (@bbterm ((_ @bit_of 0) x_0) ((_ @bit_of 1) x_0) ((_ @bit_of 2) x_0)) (@bbterm ((_
@bit_of 0) y_1) ((_ @bit_of 1) y_1) ((_ @bit_of 2) y_1))) (@bbterm (and ((_ @bit_of 0) y_1) ((_
@bit_of 0) x_0)) (xor (xor (and ((_ @bit_of 0) y_1) ((_ @bit_of 1) x_0)) (and ((_ @bit_of 1)
y_1) ((_ @bit_of 0) x_0))) false) (xor (xor (xor (xor (and ((_ @bit_of 0) y_1) ((_ @bit_of 2)
x_0)) (and ((_ @bit_of 1) y_1) ((_ @bit_of 1) x_0))) (or (and (and ((_ @bit_of 0) y_1) ((_
@bit_of 1) x_0)) (and ((_ @bit_of 1) y_1) ((_ @bit_of 0) x_0))) (and (xor (and ((_ @bit_of 0)
y_1) ((_ @bit_of 1) x_0)) (and ((_ @bit_of 1) y_1) ((_ @bit_of 0) x_0))) false))) (and ((_
@bit_of 2) y_1) ((_ @bit_of 0) x_0))) false)))
"#

/-- Operands decoded as bit lists with constant bits (`x &&& 1`, `y &&& 1`). -/
def maskedMulStep : String := r#"
(= (bvmul (@bbterm ((_ @bit_of 0) x_0) false false) (@bbterm ((_ @bit_of 0) y_1) false false))
(@bbterm (and ((_ @bit_of 0) y_1) ((_ @bit_of 0) x_0)) (xor (xor (and ((_ @bit_of 0) y_1) false)
(and false ((_ @bit_of 0) x_0))) false) (xor (xor (xor (xor (and ((_ @bit_of 0) y_1) false) (and
false false)) (or (and (and ((_ @bit_of 0) y_1) false) (and false ((_ @bit_of 0) x_0))) (and
(xor (and ((_ @bit_of 0) y_1) false) (and false ((_ @bit_of 0) x_0))) false))) (and false ((_
@bit_of 0) x_0))) false)))
"#

/-- Bit 0 with carry-in `true`: false, so the step must decline. -/
def wrongAddStep : String := r#"
(= (bvadd (@bbterm ((_ @bit_of 0) x_0) ((_ @bit_of 1) x_0) ((_ @bit_of 2) x_0) ((_ @bit_of 3)
x_0)) (@bbterm ((_ @bit_of 0) y_1) ((_ @bit_of 1) y_1) ((_ @bit_of 2) y_1) ((_ @bit_of 3) y_1)))
(@bbterm (xor (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) true) (xor (xor ((_ @bit_of 1) x_0)
((_ @bit_of 1) y_1)) (or (and ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0)
x_0) ((_ @bit_of 0) y_1)) false))) (xor (xor ((_ @bit_of 2) x_0) ((_ @bit_of 2) y_1)) (or (and
((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (or
(and ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1))
false))))) (xor (xor ((_ @bit_of 3) x_0) ((_ @bit_of 3) y_1)) (or (and ((_ @bit_of 2) x_0) ((_
@bit_of 2) y_1)) (and (xor ((_ @bit_of 2) x_0) ((_ @bit_of 2) y_1)) (or (and ((_ @bit_of 1) x_0)
((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (or (and ((_ @bit_of 0)
x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) false)))))))))
"#

/-- An adder's output compared with a constant. -/
def sumEqStep : String := r#"
(= (= (@bbterm (xor (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) false) (xor (xor ((_ @bit_of
1) x_0) ((_ @bit_of 1) y_1)) (or (and ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_
@bit_of 0) x_0) ((_ @bit_of 0) y_1)) false))) (xor (xor ((_ @bit_of 2) x_0) ((_ @bit_of 2) y_1))
(or (and ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1)
y_1)) (or (and ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_
@bit_of 0) y_1)) false))))) (xor (xor ((_ @bit_of 3) x_0) ((_ @bit_of 3) y_1)) (or (and ((_
@bit_of 2) x_0) ((_ @bit_of 2) y_1)) (and (xor ((_ @bit_of 2) x_0) ((_ @bit_of 2) y_1)) (or (and
((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (or
(and ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1))
false)))))))) (@bbterm false false false false)) (and (= (xor (xor ((_ @bit_of 0) x_0) ((_
@bit_of 0) y_1)) false) false) (= (xor (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (or (and
((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1))
false))) false) (= (xor (xor ((_ @bit_of 2) x_0) ((_ @bit_of 2) y_1)) (or (and ((_ @bit_of 1)
x_0) ((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (or (and ((_
@bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1))
false))))) false) (= (xor (xor ((_ @bit_of 3) x_0) ((_ @bit_of 3) y_1)) (or (and ((_ @bit_of 2)
x_0) ((_ @bit_of 2) y_1)) (and (xor ((_ @bit_of 2) x_0) ((_ @bit_of 2) y_1)) (or (and ((_
@bit_of 1) x_0) ((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) x_0) ((_ @bit_of 1) y_1)) (or (and
((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1))
false))))))) false)))
"#

/-- A constant compared with a bit list. -/
def constEqStep : String := r#"
(= (= (@bbterm true false false false) (@bbterm ((_ @bit_of 0) x_0) false false false)) (and (=
true ((_ @bit_of 0) x_0)) (= false false) (= false false) (= false false)))
"#

/-- `constEqStep` with its first bit equation negated: false, so it must decline. -/
def wrongEqStep : String := r#"
(= (= (@bbterm true false false false) (@bbterm ((_ @bit_of 0) x_0) false false false)) (and (=
false ((_ @bit_of 0) x_0)) (= false false) (= false false) (= false false)))
"#

/-- Bit equations over bits of the compound operand `x &&& y`. -/
def andEqStep : String := r#"
(= (= (bvand x_0 y_1) y_1) (and (= ((_ @bit_of 0) (bvand x_0 y_1)) ((_ @bit_of 0) y_1)) (= ((_
@bit_of 1) (bvand x_0 y_1)) ((_ @bit_of 1) y_1)) (= ((_ @bit_of 2) (bvand x_0 y_1)) ((_ @bit_of
2) y_1)) (= ((_ @bit_of 3) (bvand x_0 y_1)) ((_ @bit_of 3) y_1))))
"#

/-- An adder over bits of the compound operand `x &&& y`. -/
def andAddStep : String := r#"
(= (bvadd (bvand x_0 y_1) y_1) (@bbterm (xor (xor ((_ @bit_of 0) (bvand x_0 y_1)) ((_ @bit_of 0)
y_1)) false) (xor (xor ((_ @bit_of 1) (bvand x_0 y_1)) ((_ @bit_of 1) y_1)) (or (and ((_ @bit_of
0) (bvand x_0 y_1)) ((_ @bit_of 0) y_1)) (and (xor ((_ @bit_of 0) (bvand x_0 y_1)) ((_ @bit_of 0)
y_1)) false))) (xor (xor ((_ @bit_of 2) (bvand x_0 y_1)) ((_ @bit_of 2) y_1)) (or (and ((_
@bit_of 1) (bvand x_0 y_1)) ((_ @bit_of 1) y_1)) (and (xor ((_ @bit_of 1) (bvand x_0 y_1)) ((_
@bit_of 1) y_1)) (or (and ((_ @bit_of 0) (bvand x_0 y_1)) ((_ @bit_of 0) y_1)) (and (xor ((_
@bit_of 0) (bvand x_0 y_1)) ((_ @bit_of 0) y_1)) false)))))))
"#

/-- Bit equations of `x = y` over symbols. -/
def symbolEqStep : String := r#"
(= (= x_0 y_1) (and (= ((_ @bit_of 0) x_0) ((_ @bit_of 0) y_1)) (= ((_ @bit_of 1) x_0) ((_
@bit_of 1) y_1))))
"#

abbrev Word := BitVec 2

-- An alias of `BitVec 2` replays like `BitVec 2`.
example : True := by
  run_tac do
    unless ← replayStep 2 "bv_bitblast_step_bvequal" symbolEqStep do
      throwError "the symbol equality step was not replayed"
    unless ← replayStep 2 "bv_bitblast_step_bvequal" symbolEqStep (some (mkConst ``Word)) do
      throwError "the equality step over an alias was not replayed"
  trivial

-- Bit projection is linear in the DAG: a 64-deep shared `v &&& v` and a 4096-bit list.
example : True := by
  run_tac do
    let w := mkNatLit 8
    withLocalDeclD `x (mkApp (mkConst ``BitVec) w) fun x => do
      let mut v := x
      for _ in [:64] do
        v := mkApp3 (mkConst ``BitVec.and) w v v
      discard <| (BitBlastRules.bitOf w v 0).run' {}
    let n := 4096
    let bits := (List.range n).map fun i => mkConst (if i % 3 == 0 then ``true else ``false)
    let list ← mkListLit (mkConst ``Bool) bits
    let vec := mkApp (mkConst ``BitVec.ofBoolListLE) list
    let wide := mkNatLit n
    let run : BitBlastRules.ReifyM Unit := do
      for k in [:n] do
        discard <| BitBlastRules.bitOf wide vec k
    run.run' {}
  trivial

example : True := by
  run_tac do
    unless ← replayStep 4 "bv_bitblast_step_bvequal" andEqStep do
      throwError "the compound-operand equality step was not replayed"
    unless ← replayStep 3 "bv_bitblast_step_bvadd" andAddStep do
      throwError "the compound-operand addition step was not replayed"
    unless ← replayStep 4 "bv_bitblast_step_bvequal" sumEqStep do
      throwError "the sum equality step was not replayed"
    unless ← replayStep 4 "bv_bitblast_step_bvequal" constEqStep do
      throwError "the constant equality step was not replayed"
    if ← replayStep 4 "bv_bitblast_step_bvequal" wrongEqStep then
      throwError "a wrong equality step was replayed"
    unless ← replayStep 4 "bv_bitblast_step_bvadd" addStep do
      throwError "the addition step was not replayed"
    unless ← replayStep 3 "bv_bitblast_step_bvmult" mulStep do
      throwError "the multiplication step was not replayed"
    unless ← replayStep 3 "bv_bitblast_step_bvmult" maskedMulStep do
      throwError "the masked multiplication step was not replayed"
    if ← replayStep 4 "bv_bitblast_step_bvadd" wrongAddStep then
      throwError "a wrong addition step was replayed"
  trivial

/-- Bit `i` of an 8-bit `(bvnot v)` step's operand: 31 connectives over bit `i` of `x` and
`y`, 64 nodes. The negated bits on the right have 65 nodes each. -/
def wideBit (i : Nat) : String := Id.run do
  let mut term := s!"(not ((_ @bit_of {i}) x_0))"
  for j in [:31] do
    term := s!"({#["or", "xor", "and"][j % 3]!} {term} ((_ @bit_of {i}) y_1))"
  return term

-- Both sides of a `bvnot` step with large bits decode as whole-vector operations, and the
-- certificate replays.
example : True := by
  run_tac do
    let bits := (List.range 8).map wideBit
    let vector := s!"(@bbterm {" ".intercalate bits})"
    let negated := s!"(@bbterm {" ".intercalate (bits.map (s!"(not {·})"))})"
    let clause := s!"(= (bvnot {vector}) {negated})"
    let type := mkApp (mkConst ``BitVec) (mkNatLit 8)
    withLocalDeclD `x type fun x => withLocalDeclD `y type fun y => do
      let symbols : Std.HashMap String Expr := ((∅ : Std.HashMap String Expr).insert "x_0" x).insert "y_1" y
      let some (term, _) := SMT.parseSexp clause | throwError "unparsable test step"
      let some step ← toExpr? { symbols, named := {} } 64 term | throwError "undecodable test step"
      unless (step.getArg! 2).isAppOf ``BitVec.not do
        throwError "the negated bits did not decode as `BitVec.not`: {step.getArg! 2}"
      withLocalDeclD `h (mkNot step) fun h => do
        let certificate := s!"unsat ((assume a0 (not {clause})) (step t0 (cl {clause}) \
          :rule bv_bitblast_step_bvnot) (step t1 (cl) :rule resolution :premises (t0 a0)))"
        let some proof := parseProof certificate | throwError "unparsable certificate"
        let assumptions := (∅ : Std.HashMap String Expr).insert "a0" h
        match ← replay proof (SMT.parseSexps certificate) assumptions symbols with
        | .ok _ => pure ()
        | .error e => throwError "the bvnot certificate did not replay: {e.kind.label} {e.detail}"
  trivial

end AletheBitBlast
