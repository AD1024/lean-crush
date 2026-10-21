import Crush.Translation.Unfold

/-!
Automatic unfolding must warn and skip relevant declarations whose metadata exposes
no definition body. Unrelated queries must not inspect unavailable marked definitions.
-/

open Lean Meta Crush

axiom unavailableBody : Nat → Nat
run_cmd crushUnfoldExt.add (``unavailableBody, .unfold) .local

/-- warning: crush: skipping automatic unfolding of `unavailableBody` because its definition body is unavailable -/
#guard_msgs in
#eval show MetaM Unit from do
  unless (← relevantAutoUnfoldLemmas #[``unavailableBody]).isEmpty do
    throwError "unavailable definition contributed an unfolding equation"

#eval show MetaM Unit from do
  unless (← relevantAutoUnfoldLemmas #[``Nat.add]).isEmpty do
    throwError "an unrelated query included unavailable unfolding metadata"
