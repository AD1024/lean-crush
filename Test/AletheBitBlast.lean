import Crush

/-!
Checked replay of cvc5's bit-blasted addition, multiplication and equality. The steps
below are cvc5 1.3.4 certificate steps with their `:named` subterms expanded.
-/

open Lean Meta Elab Tactic Crush Crush.Alethe

namespace AletheBitBlast

/-- Decode `clause` over `x y : BitVec w` and run the registered handlers for `rule`.
Returns whether a proof of the decoded step came back. -/
def replayStep (w : Nat) (rule clause : String) : TacticM Bool := do
  let some (term, _) := SMT.parseSexp clause | throwError "unparsable test step"
  let type := mkApp (mkConst ``BitVec) (mkNatLit w)
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

example : True := by
  run_tac do
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

end AletheBitBlast
