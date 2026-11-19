import Crush

/-!
Visible local lets contribute defining equalities with kernel-checked proofs,
subject to explicit hypothesis selection. Hidden nondependent values remain opaque;
local type aliases are reduced by Lean rather than asserted as data equalities.
-/

open Lean Meta
open Crush

namespace SoundnessLocalLets

run_meta do
  withLocalDeclD `y (mkConst ``Int) fun y => do
    let value := mkApp2 (mkConst ``Int.add) y (mkIntLit 1)
    withLetDecl `x (mkConst ``Int) value fun x => do
      let target ← mkEq x (mkIntLit 0)
      let goal ← mkFreshExprMVar target
      let facts ← collectFacts goal.mvarId! {} false
      let definitions := facts.filter fun fact => fact.descr == "let x"
      unless definitions.size == 1 do
        throwError "collector omitted the visible local let's defining equality"
      let fact := definitions[0]!
      unless fact.prop == (← mkEq x value) do
        throwError "local let equality has the wrong endpoints"
      let some proof := fact.proof | throwError "local let equality has no proof"
      match Kernel.check (← getEnv) (← getLCtx)
          (mkApp2 (mkConst ``id [0]) fact.prop proof) with
      | .ok _ => pure ()
      | .error _ => throwError "local let equality's proof is invalid"
      -- An explicit [] continues to omit unselected local facts.
      let restricted ← collectFacts goal.mvarId! { allHyps := false } false
      unless restricted.size == 1 && restricted[0]!.negated do
        throwError "strict hints unexpectedly included a local let equation"

run_meta do
  withLetDecl `x (mkConst ``Int) (mkIntLit 1) (nondep := true) fun x => do
    let goal ← mkFreshExprMVar (← mkEq x (mkIntLit 0))
    let facts ← collectFacts goal.mvarId! {} false
    unless facts.size == 1 && facts[0]!.negated do
      throwError "collector exposed the hidden value of a nondependent local"

run_meta do
  withLetDecl `T (mkSort (.succ .zero)) (mkConst ``Nat) fun _ => do
    let goal ← mkFreshExprMVar (mkConst ``True)
    let facts ← collectFacts goal.mvarId! {} false
    unless facts.size == 1 && facts[0]!.negated do
      throwError "collector asserted an unsupported equality between types"

/-! ## Checked proofs over let-bound locals (review round 3, N1/W1)

A dependent let-bound local becomes a `let` binder of the closed implication that
reconstruction proves, not a `∀` binder, so the checked proof must be applied only to
the `∀` parameters (`closeTarget`). A nondependent `have` stays an ordinary argument. -/

section
set_option crush.timeout 10
set_option crush.trust "reconstruct"

-- Core reconstruction (z3).
theorem withLetCore (f : Int → Int) (a b : Int) :
    let x := f a; x = b → f b = a → f (f x) = b := by
  intro x h h2
  crush

theorem withLetTactic (f : Int → Int) (a b : Int) (h : f a = b) (h2 : f b = a) :
    f (f (f a)) = b := by
  let y : Int := a
  have hy : f y = b := h
  clear h
  crush

theorem withHave (f : Int → Int) (a b : Int) (h : f a = b) (h2 : f b = a) :
    f (f (f a)) = b := by
  have hy : f a = b := h
  clear h
  crush

-- Alethe replay (cvc5).
set_option crush.backend "cvc5" in
set_option crush.reconstruct "alethe" in
theorem withLet (f : Int → Int) (a b : Int) :
    let x := f a; x = b → f b = a → f (f x) = b := by
  intro x h h2
  crush

set_option crush.backend "cvc5" in
set_option crush.reconstruct "alethe" in
theorem withLet2 (f : Int → Int) (a b : Int) (h : f a = b) (h2 : f b = a) :
    f (f (f a)) = b := by
  let y : Int := a
  have hy : f y = b := h
  clear h
  crush

set_option crush.backend "cvc5" in
set_option crush.reconstruct "alethe" in
theorem withHaveAlethe (f : Int → Int) (a b : Int) (h : f a = b) (h2 : f b = a) :
    f (f (f a)) = b := by
  have hy : f a = b := h
  clear h
  crush
end

run_meta do
  for name in [``withLetCore, ``withLetTactic, ``withHave, ``withLet, ``withLet2,
      ``withHaveAlethe] do
    if (← collectAxioms name).contains ``Crush.crushSorry then
      throwError "`{name}` was closed with the trust axiom"

end SoundnessLocalLets
