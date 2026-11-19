import Crush.Translation.Unfold

/-!
Automatic unfolding must warn and skip relevant marked declarations that have no
equation lemmas. Unrelated queries must not inspect unavailable marked definitions.
-/

open Lean Meta Crush

axiom unavailableBody : Nat → Nat
run_cmd crushUnfoldExt.add (``unavailableBody, .unfold) .local

/-- warning: crush: skipping automatic unfolding of `unavailableBody` because it has no equations -/
#guard_msgs in
#eval show MetaM Unit from do
  unless (← relevantAutoUnfoldLemmas #[``unavailableBody]).isEmpty do
    throwError "unavailable definition contributed an unfolding equation"

#eval show MetaM Unit from do
  unless (← relevantAutoUnfoldLemmas #[``Nat.add]).isEmpty do
    throwError "an unrelated query included unavailable unfolding metadata"
