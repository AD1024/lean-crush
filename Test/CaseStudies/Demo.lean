import Crush

def Nand (x y : BitVec 4) : BitVec 4 :=
  ~~~(x &&& y)


section NandSelf
set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option crush.trace.script true
set_option trace.crush.result true

attribute [crush_unfold] Nand

theorem Nand_self (x : BitVec 4) : Nand x x = ~~~x := by
  crush

#print axioms Nand_self

set_option pp.all false in
#print Nand_self

end NandSelf

section ComputeMask

register_lowering term <<
  (Nand (term x) (term y)) =>
    (smt| (bvnand $x $y))
>>

register_crush_replay term <<
  (bvnand (term x : BitVec 4) (term y : BitVec 4)) =>
    ~~~(x &&& y)
>>

set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option trace.crush.result true
set_option crush.trace.script true

theorem computes_mask
    (run : (BitVec 4 → BitVec 4) → BitVec 4 → BitVec 4)
    (hrun : ∀ f x, run f x = f x)
    (x mask : BitVec 4) :
    run (fun y => Nand (Nand y mask) (Nand y mask)) x =
      x &&& mask := by
  crush

#print axioms computes_mask
set_option pp.all false in
#print computes_mask
end ComputeMask

namespace AletheResolutionExample

/-- Verbatim cvc5 output for `p ∨ q`, `¬p ∨ r`, `¬q`, and `¬r`. -/
def certificate : String :=
"unsat
(
(assume a0 (! (or p q) :named @p_1))
(assume a1 (! (or (! (not p) :named @p_2) r) :named @p_3))
(assume a2 (! (not q) :named @p_4))
(assume a3 (! (not r) :named @p_5))
(step t0 (cl p q) :rule or :premises (a0))
(step t1 (cl p) :rule resolution :premises (t0 a2))
(step t2 (cl @p_2 r) :rule or :premises (a1))
(step t3 (cl @p_2) :rule resolution :premises (t2 a3))
(step t4 (cl) :rule resolution :premises (t1 t3))
)"

open Lean Meta Elab Tactic Crush

/-- Bind the certificate's symbols and assumptions to the current Lean context,
then replay its steps to construct a proof of `False`. -/
elab "replay_resolution_certificate " p:ident q:ident r:ident
    h0:ident h1:ident h2:ident h3:ident : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let some parsed := Alethe.parseProof certificate
      | throwError "could not parse the Alethe certificate"
    let propositions ← #[p, q, r].mapM fun name => elabTerm name none
    let hypotheses ← #[h0, h1, h2, h3].mapM fun name => elabTerm name none
    let symbols := ({} : Std.HashMap String Expr)
      |>.insert "p" propositions[0]!
      |>.insert "q" propositions[1]!
      |>.insert "r" propositions[2]!
    let facts := ({} : Std.HashMap String Expr)
      |>.insert "a0" hypotheses[0]!
      |>.insert "a1" hypotheses[1]!
      |>.insert "a2" hypotheses[2]!
      |>.insert "a3" hypotheses[3]!
    match ← Alethe.replay parsed (SMT.parseSexps certificate) facts symbols with
    | .error failure => throwError failure.toMessageData
    | .ok proof =>
      goal.assign proof
      replaceMainGoal []

-- The exact certificate ends in the empty clause, i.e. False.
set_option trace.crush.result true in
theorem certificate_refutation (p q r : Prop)
    (h0 : p ∨ q) (h1 : ¬p ∨ r) (h2 : ¬q) (h3 : ¬r) : False := by
  replay_resolution_certificate p q r h0 h1 h2 h3

-- Use that refutation to establish the desired resolvent.
theorem resolution_from_certificate (p q r : Prop)
    (h0 : p ∨ q) (h1 : ¬p ∨ r) : q ∨ r := by
  classical
  apply Classical.byContradiction
  intro h
  have h2 : ¬q := fun hq => h (Or.inl hq)
  have h3 : ¬r := fun hr => h (Or.inr hr)
  exact certificate_refutation p q r h0 h1 h2 h3

-- Ask cvc5 for a fresh certificate and use Alethe-only reconstruction.
set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"

set_option trace.crush.result true in
theorem resolution_via_crush (p q r : Prop)
    (h0 : p ∨ q) (h1 : ¬p ∨ r) : q ∨ r := by
  crush

#print resolution_via_crush

#print axioms certificate_refutation
#print axioms resolution_from_certificate
#print axioms resolution_via_crush

end AletheResolutionExample
