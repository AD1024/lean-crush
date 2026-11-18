import Crush

/-!
Tests for the `@[crush_unfold]` / `@[crush_defeq]` auto-unfold attributes: a marked
definition's equation lemmas are folded into every `crush` query automatically
(relevance-filtered), so no per-call `u[…]`/`d[…]` hint is needed. See `Test/TIP.lean`
for the realistic payoff (the inductive-proof cases carry no unfold hints at all).
-/

open Crush

set_option crush.trust "trust"
set_option crush.timeout 5

/-! ## The attribute fires with no hint

`f` is recursive; without its equations `crush` treats it as uninterpreted and cannot
evaluate `f 2`. With `@[crush_unfold]` the equations arrive automatically. -/

@[crush_unfold]
def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n + 2

theorem f_auto : f 2 = 4 := by crush          -- no `u[f]` needed

/-! ## `@[crush_defeq]` (unfold-equation form) -/

@[crush_defeq]
def g (n : Nat) : Nat := n + n

theorem g_auto (x : Nat) : g x = x + x := by crush   -- no `d[g]` needed

/-! ## Relevance filtering: an unrelated marked def costs nothing

`noise` is marked but never mentioned by this goal, so its (recursive, quantified)
equations are *not* added — the query stays about `f` alone. If relevance filtering
were absent, unrelated recursive equations would bloat every query and risk
instantiation loops. This goal closing quickly is the observable check. -/

@[crush_unfold]
def noise : Nat → Nat
  | 0 => 0
  | n + 1 => noise n + noise n + 1

theorem relevance_ok (x : Nat) (h : f x = 0) : f x + 1 = 1 := by crush

/-! ## Transitive relevance: a marked def reachable *through* another

`uses_f` calls `f`; unfolding `uses_f` exposes `f`, so `f`'s equations must come along
even though the goal only names `uses_f`. -/

@[crush_unfold]
def uses_f (n : Nat) : Nat := f n + 1

theorem transitive_auto : uses_f 2 = 5 := by crush   -- needs both uses_f and f

/-! ## Standard `@[reducible]` predicate wrappers

Reducible predicates are normalized in Lean but are not sent to SMT as quantified
equations. Recursive predicates contribute only constructor-specific equations, so
known constructor applications reduce without expanding symbolic recursive calls. -/

@[reducible]
def inOpenInterval (x lo hi : Int) : Prop :=
  lo < x ∧ x < hi

theorem reducible_predicate_auto (x lo hi : Int)
    (h : inOpenInterval x lo hi) : lo + 1 ≤ x := by
  crush

set_option crush.autoUnfold false in
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem reducible_predicate_disabled (x lo hi : Int)
    (h : inOpenInterval x lo hi) : lo + 1 ≤ x := by
  crush

@[reducible]
def recursiveReducible : Nat → Prop
  | 0 => True
  | n + 1 => recursiveReducible n

run_meta
  let lemmas ← relevantReducibleRewriteLemmas #[``recursiveReducible]
  if lemmas.isEmpty then
    throwError "recursive reducible predicate equations were not selected"

theorem recursive_reducible_auto (n : Nat) (h : recursiveReducible n) :
    recursiveReducible (Nat.succ n) := by
  crush

/-! ## `crush.autoUnfold false` disables the mechanism

With auto-unfold off and no explicit hint, `f` is uninterpreted again, so a goal that
depends on unfolding it is *not* provable — the negative test pins that the option
actually gates the behavior. -/

set_option crush.autoUnfold false in
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem disabled_no_unfold : f 2 = 4 := by crush

-- …and with the option off, the explicit `u[…]` hint still works.
set_option crush.autoUnfold false in
theorem disabled_but_explicit : f 2 = 4 := by crush u[f]

/-! ## Misuse is a declaration-time error

`@[crush_unfold]` on something with no equations (an `opaque`) is rejected at the
attribute, not silently ignored. -/

/-- error: @[crush_unfold] expects a definition with equational lemmas -/
#guard_msgs(error, substring := true) in
@[crush_unfold] opaque noEqns : Nat → Nat

/-! ## Callees of n-ary well-founded definitions (review round 3, C4)

The body of a well-founded `f7` mentions only its `_unary` worker, so the traversal
follows the constants of `f7`'s equation lemmas, which expose the marked `g7`. -/

namespace WellFoundedCallees

@[crush_unfold] def g7 (n : Nat) : Nat := n + 1
@[crush_unfold] def f7 (a b : Nat) : Nat := if a = 0 then g7 b else f7 (a - 1) (b + 1)
termination_by a
decreasing_by omega
@[crush_unfold] def unrelated7 (n : Nat) : Nat := n * 3

theorem wf_callee_unfolds : f7 0 5 = 6 := by crush

open Lean Meta Crush in
run_meta do
  let lemmas ← relevantAutoUnfoldLemmas #[``f7]
  let has (n : Name) := lemmas.any (·.getPrefix == n)
  unless has ``f7 && has ``g7 do
    throwError "the callee of a well-founded definition was not reached: {lemmas}"
  if has ``unrelated7 then
    throwError "an unrelated marked definition was collected: {lemmas}"

end WellFoundedCallees
