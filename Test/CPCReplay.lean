import Test.AletheReplay
import Test.AletheExtension

/-! Re-prove existing Alethe obligations using live cvc5 CPC certificates.
The theorem's type is reused; its existing proof is never supplied to Crush. -/

open Lean Meta Elab Command
open Crush

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "CPC"
set_option crush.reconstruct.fallback false
set_option crush.timeout 30

private def checkCPCReplay (names : Array (TSyntax `ident)) (proofSyntax : TSyntax `term) :
    CommandElabM Unit := do
  for name in names do
    try
      withRef name <| liftTermElabM do
        let declName ← realizeGlobalConstNoOverloadWithInfo name
        let type := (← getConstInfo declName).type
        let snapshot ← KernelCheckSnapshot.capture
        let proof ← Term.withoutErrToSorry <| Term.elabTermEnsuringType proofSyntax type
        Term.synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        let proof ← kernelCheckProof snapshot type proof
        let checked ← mkAuxTheorem type proof
        let axioms ← collectAxioms checked.getAppFn.constName!
        if axioms.any (fun name => name == ``Crush.crushSorry || name == ``sorryAx ||
            name.toString.contains "._native.") then
          throwError "CPC replay escaped kernel-only reconstruction"
    catch ex => logErrorAt name m!"CPC replay of {name} failed: {ex.toMessageData}"

elab "check_cpc_replay " names:ident,+ : command => do
  checkCPCReplay names.getElems (← `(by intros; crush))

elab "check_cpc_replay " names:ident,+ " using " proofTerm:term : command =>
  checkCPCReplay names.getElems proofTerm

check_cpc_replay custom_divisibility_replay

check_cpc_replay bool_pigeonhole5, euf_chain4, euf_binary, euf_diseq,
  bool_chain, bool_diseq, euf_function_chain

check_cpc_replay string_append_fresh, string_append_length, string_append_prefix,
  string_append_suffix, string_append_contains, string_append_isEmpty

check_cpc_replay alethe_linear_arithmetic, alethe_nonlinear_arithmetic,
  alethe_nat_arithmetic, alethe_ite, alethe_int_mod, alethe_int_div_mod,
  alethe_datatype_injective

check_cpc_replay alethe_bitvec_xor, alethe_bitvec_negation, alethe_bitvec_bitwise,
  alethe_bitvec_order, alethe_bitvec_shift_left, alethe_bitvec_logical_shift,
  alethe_bitvec_arithmetic_shift, alethe_bitvec_rotate, alethe_bitvec_extract,
  alethe_bitvec_zero_extend, alethe_bitvec_sign_extend, alethe_bitvec_concat,
  alethe_bitvec_unsigned_conversion, alethe_bitvec_unsigned_division,
  alethe_bitvec_unsigned_remainder, alethe_bitvec_signed_division,
  alethe_bitvec_signed_remainder, alethe_bitvec_unsigned_order,
  alethe_bitvec_signed_order, alethe_bitvec_power_multiplication,
  alethe_bitvec_signed_modulo, alethe_bitvec_unsigned_strict_order,
  alethe_bitvec_unsigned_order_aliases, alethe_bitvec_signed_order_aliases,
  alethe_distinct

check_cpc_replay alethe_quantified, alethe_nat_quantified, alethe_bool_function,
  alethe_exists, alethe_higher_order_defun

check_cpc_replay alethe_restricted_hints using (by intros; crush [])

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example (p q : Bool) : p = q := by crush

/-- error: crush: `crush.reconstruct cpc` requires the cvc5 backend -/
#guard_msgs(error, substring := true) in
set_option crush.backend "z3" in
example : True := by crush
