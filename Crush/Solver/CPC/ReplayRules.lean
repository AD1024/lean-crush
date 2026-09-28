import Crush.Solver.Replay.ReplayRules
import Crush.Solver.CPC.Term

/-! CPC inference handlers. Shared theory handlers explicitly register for both
formats; these rules use CPC's native inference names. -/

namespace Crush.CPC
universe u
open Lean Meta Elab Tactic Crush

private theorem notForallAtCounterexample {α : Sort u} [Nonempty α]
    (predicate : α → Prop) (h : ¬∀ x, predicate x) :
    ¬predicate (Classical.epsilon fun x => ¬predicate x) := by
  classical
  exact Classical.epsilon_spec (Classical.not_forall.mp h)

@[crush_replay_rule CPC "skolemize" low]
private def replaySkolemization : ReplayRuleHandler := fun ctx => do
  let #[premise] := ctx.premises | return none
  let some universal := premise.clause.not? | return none
  let .forallE name type body info := universal | return none
  let predicate := Expr.lam name type body info
  let proof ← mkAppM ``notForallAtCounterexample #[predicate, premise.proof]
  unless ← isDefEqGuarded (← inferType proof) ctx.target do return none
  return some proof

@[crush_replay_rule CPC "instantiate" low]
private def replayInstantiation : ReplayRuleHandler := fun ctx => do
  let #[premise] := ctx.premises | return none
  let #[SMT.Sexp.list arguments] := ctx.args | return none
  unless arguments[0]? == some (.atom "@list") do return none
  let mut proof := premise.proof
  for argument in arguments.extract 1 arguments.size do
    let .forallE _ type _ _ ← whnf (← inferType proof) | return none
    let some argument ← ctx.decodeTerm argument | return none
    unless ← isDefEqGuarded (← inferType argument) type do return none
    proof := mkApp proof argument
  unless ← isDefEqGuarded (← inferType proof) ctx.target do return none
  return some proof

register_replay_rule CPC low <<
  (eq_resolve ..) | (true_elim ..) | (false_elim ..) | (contra ..) |
  (modus_ponens ..) | (not_not_elim ..) | (and_elim ..) | (not_and ..) |
  (not_or_elim ..) | (implies_elim ..) | (not_implies_elim1 ..) |
  (not_implies_elim2 ..) | (equiv_elim1 ..) | (equiv_elim2 ..) |
  (not_equiv_elim1 ..) | (not_equiv_elim2 ..) |
  (cnf_and_pos ..) | (cnf_and_neg ..) | (cnf_or_pos ..) | (cnf_or_neg ..) |
  (cnf_implies_pos ..) | (cnf_implies_neg1 ..) | (cnf_implies_neg2 ..) |
  (cnf_equiv_pos1 ..) | (cnf_equiv_pos2 ..) |
  (cnf_equiv_neg1 ..) | (cnf_equiv_neg2 ..) |
  (cnf_xor_pos1 ..) | (cnf_xor_pos2 ..) | (cnf_xor_neg1 ..) | (cnf_xor_neg2 ..) |
  (cnf_ite_pos1 ..) | (cnf_ite_pos2 ..) | (cnf_ite_pos3 ..) |
  (cnf_ite_neg1 ..) | (cnf_ite_neg2 ..) | (cnf_ite_neg3 ..) |
  (scope ..) | (scope_body ..) | (process_scope ..) | (nary_cong ..) => by grind
>>

register_replay_rule CPC low <<
  (arith_sum_ub ..) | (arith_trichotomy ..) | (int_tight_ub ..) |
  (int_tight_lb ..) | (arith_poly_norm ..) | (arith_poly_norm_rel ..) => by omega
>>

register_replay_rule CPC low <<
  (instantiate ..) => by first | grind | (simp_all; omega)
>>

register_replay_rule CPC low <<
  (arith_reduction ..) => by repeat' constructor <;> omega
>>

end Crush.CPC
