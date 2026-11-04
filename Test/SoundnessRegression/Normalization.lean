import Crush.Translation.Preprocess

/-!
Normalization is optional: simplifier setup failures and resource limits must
retain the original fact and allow later attempts to succeed. Successful rewrites
must carry proofs checked against the rewritten proposition.
-/

open Lean Meta
open Crush

namespace SoundnessNormalization

def countDown (n : Nat) : Nat :=
  if h : n = 0 then 0 else countDown (n - 1)
termination_by n
decreasing_by omega

def bump (n : Nat) : Nat := n + 1

private def unchanged (source : Expr) (result : NormalizeReport) : MetaM Unit := do
  unless result.rewritten == 0 && result.facts.size == 1 &&
      result.facts[0]!.prop == source do
    throwError "failed normalization did not retain the original fact"

-- Symbolic unfolding repeatedly exposes a recursive call and exhausts the local budget.
run_meta do
  let equations ← eqnLemmasFor ``countDown .unfold
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let source ← mkEq (mkApp (mkConst ``countDown) n) (mkNatLit 1)
    unchanged source (← normalizeFacts #[{ prop := source, proof := none, descr := "recursive" }]
      equations)

-- Fail while preparing the simplifier.
run_meta do
  let source := mkConst ``False
  unchanged source (← normalizeFacts #[{ prop := source, proof := none, descr := "context" }]
    #[`SoundnessNormalization.nonexistent])

-- A recursion-depth limit raises a runtime exception rather than an ordinary tactic error.
set_option maxRecDepth 32 in
run_meta do
  let equations ← eqnLemmasFor ``countDown .unfold
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let source ← mkEq (mkApp (mkConst ``countDown) n) (mkNatLit 1)
    unchanged source (← normalizeFacts #[{ prop := source, proof := none, descr := "depth" }]
      equations)

-- Check a successful rewrite after the failed attempts.
run_meta do
  let equations ← eqnLemmasFor ``bump .unfold
  let proof := mkApp (mkConst equations[0]!) (mkNatLit 2)
  let source ← inferType proof
  let result ← normalizeFacts #[{ prop := source, proof := some proof, descr := "finite" }]
    equations
  unless result.rewritten == 1 do
    throwError "bounded normalization declined a small terminating rewrite"
  let fact := result.facts[0]!
  let some proof := fact.proof | throwError "normalization lost the fact's proof"
  match Kernel.check (← getEnv) (← getLCtx) (mkApp2 (mkConst ``id [0]) fact.prop proof) with
  | .ok _ => pure ()
  | .error _ => throwError "normalization produced an invalid proof"

end SoundnessNormalization
