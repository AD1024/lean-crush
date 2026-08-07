import Crush

/-!
Tests for proof-producing selected-definition normalization.

Definitions requested through `u[...]`/`d[...]` are rewritten in the collected
facts before monomorphization. Their equations remain available as fallback SMT
facts and during reconstruction.
-/

open Lean Meta
open Crush

set_option crush.trust "reconstruct"

private def wrappedSucc (x : Int) : Int := x + 1

private theorem wrappedSuccQuery (x : Int) : wrappedSucc x = x + 1 := rfl

run_meta do
  let queryProof ← mkConstWithFreshMVarLevels ``wrappedSuccQuery
  let source := mkNot (← inferType queryProof)
  let lemmas ← eqnLemmasFor ``wrappedSucc .unfold
  let report ← normalizeFacts #[{
    prop := source
    proof := none
    descr := "negated query"
    negated := true }] lemmas
  unless report.rewritten == 1 do
    throwError "expected selected-definition normalization to rewrite one fact"
  let normalized := report.facts[0]!
  if normalized.prop.getUsedConstants.contains ``wrappedSucc then
    throwError "selected definition remained in the normalized proposition"
  let some transform := normalized.negationTransform
    | throwError "missing normalized negated-goal proof transformer"
  let expected ← mkArrow source normalized.prop
  unless ← isDefEq (← inferType transform) expected do
    throwError "negated-goal transformer has the wrong type"

/-! This is the Cedar `List.Equiv` shape that motivated direct normalization.
Its exact applications are unfolded before translation; `List.Subset.trans`
then connects the two directions without asking SMT to instantiate the
equivalence definition's equation. -/

private def listEquiv {α : Type} (xs ys : List α) : Prop :=
  xs.Subset ys ∧ ys.Subset xs

theorem list_equiv_trans {α : Type} {xs ys zs : List α}
    (hxy : listEquiv xs ys) (hyz : listEquiv ys zs) :
    listEquiv xs zs := by
  crush [List.Subset.trans, *] u[listEquiv, List.Subset]

private def triple (x : Int) : Int := x + x + x

theorem explicit_defeq_normalizes (x : Int) : triple x = x + x + x := by
  crush d[triple]

@[crush_unfold]
private def markedDouble (x : Int) : Int := x + x

-- Exact-call normalization is independent of lemma monomorphization.
set_option crush.mono.fuel 0 in
theorem auto_unfold_normalizes (x : Int) : markedDouble x = x + x := by
  crush

-- Exercise the negated-goal transformer in certificate replay with no
-- core-directed fallback.
set_option crush.backend "cvc5" in
set_option crush.reconstruct "alethe" in
theorem normalized_goal_replays (x : Int) : triple x = x + x + x := by
  crush d[triple]
