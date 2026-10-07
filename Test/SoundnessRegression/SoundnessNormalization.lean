import Crush.Translation.Preprocess

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

-- A well-founded equation keeps exposing another recursive call under a symbolic
-- guard. Exceeding the local simplification budget must leave the fact available.
run_meta do
  let equations ← eqnLemmasFor ``countDown .unfold
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let source ← mkEq (mkApp (mkConst ``countDown) n) (mkNatLit 1)
    unchanged source (← normalizeFacts #[{ prop := source, proof := none, descr := "recursive" }]
      equations)

-- Failure while preparing the simplifier is also an optional-optimization decline.
run_meta do
  let source := mkConst ``False
  unchanged source (← normalizeFacts #[{ prop := source, proof := none, descr := "context" }]
    #[`SoundnessNormalization.nonexistent])

-- Exhausting the caller's recursion-depth limit is a runtime exception rather than
-- an ordinary tactic error. It must not prevent a later normalization from working.
set_option maxRecDepth 32 in
run_meta do
  let equations ← eqnLemmasFor ``countDown .unfold
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let source ← mkEq (mkApp (mkConst ``countDown) n) (mkNatLit 1)
    unchanged source (← normalizeFacts #[{ prop := source, proof := none, descr := "depth" }]
      equations)

-- Ordinary normalization still produces a proof checked against the rewritten fact.
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
