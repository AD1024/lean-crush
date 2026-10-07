import Crush.Translation.Unfold

open Lean Meta Crush

-- Model imported unfolding metadata whose declaration exposes a signature but
-- no body. Traversal must report the unavailable body instead of calling value!.
axiom unavailableBody : Nat → Nat
run_cmd crushUnfoldExt.add (``unavailableBody, .unfold) .local

/-- error: crush: cannot automatically unfold `unavailableBody` because its definition body is unavailable -/
#guard_msgs in
#eval show MetaM Unit from do
  discard <| relevantAutoUnfoldLemmas #[``unavailableBody]

-- An unrelated query does not inspect unavailable marked definitions.
#eval show MetaM Unit from do
  unless (← relevantAutoUnfoldLemmas #[``Nat.add]).isEmpty do
    throwError "an unrelated query included unavailable unfolding metadata"
