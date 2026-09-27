import Crush

/-!
Dependent function types are refused rather than encoded.

`Test/HigherOrder.lean` pins the unsoundness that arises when a function-typed
bound variable is declared as an *unrelated* function symbol. The fix there is
reached through `arrowShape?`/`isFunctionType`, both of which are `Expr.isArrow`,
and `isArrow` is false for a dependent `∀`. The same disconnection was therefore
still reachable through a dependent function type, and `crush` closed

```lean
theorem dependent_ho_constant (β : Nat → Type) (F : β 0 → Int)
    (G : ((n : Nat) → β n) → Int) (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = F (k 0)) : G c = G d
```

whose negation is provable in Lean: take `β := fun _ => Nat`, `F := Int.ofNat`,
`G := fun k => (k 0 : Int)`, `c := fun _ => 0`, `d := fun _ => 1`. Every hypothesis
holds (`h` by `rfl`) and the conclusion is `0 = 1`. The emitted script was

```smtlib
(declare-sort s_0 0)                  ; (n : Nat) → β n, opaque, no `app` symbol
(declare-fun G_2 (s_0) Int)
(declare-fun q_1_7 (Int) s_5)         ; `k 0`, a global unrelated to the binder
(assert (forall ((q_1 s_0)) (= (G_2 q_1) (F_4 (q_1_7 0)))))
(assert (not (= (G_2 c_9) (G_2 d_10))))
```

with no occurrence of `q_1` on the right of the quantified equation, so the
hypothesis asserted that `G` is *constant* — strictly stronger than what it says in
Lean, and enough to refute the negated goal.

`quantifier` now refuses a dependent function domain, the way it already refuses an
uninhabited one. The refusal is deliberately by *type*, not by whether the binder
happens to be applied: translation may unfold a definition that introduces an
application the syntactic check would have missed, and an over-approximation is the
safe direction. The completeness cost is pinned in the last section.
-/

open Crush

/-! ## The refusal

This is the goal that used to close. -/

/--
error: crush: cannot translate a quantifier over the dependent function type
-/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (F : β 0 → Int) (G : ((n : Nat) → β n) → Int)
    (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = F (k 0)) : G c = G d := by
  crush

-- The refusal happens during translation, before any solver runs, so it does not
-- depend on the trust policy. Under `trust` the goal used to close with
-- `crushSorry`; it now fails identically to the checked policy.
/--
error: crush: cannot translate a quantifier over the dependent function type
-/
#guard_msgs(error, substring := true) in
set_option crush.trust "reconstruct" in
example (β : Nat → Type) (F : β 0 → Int) (G : ((n : Nat) → β n) → Int)
    (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = F (k 0)) : G c = G d := by
  crush

-- An existential binder takes the same path.
/--
error: crush: cannot translate a quantifier over the dependent function type
-/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (G : ((n : Nat) → β n) → Int) :
    ∃ k : (n : Nat) → β n, G k = 0 := by
  crush

/-! ## Both backends and both higher-order modes

**Requires `cvc5` on `PATH`** (CI installs it), like `Test/Cvc5.lean`.

The hole was not specific to defunctionalization: in `native` mode the arrow branch
of `emitSort` and the `funVar` registration are gated on `isArrow` too, and the same
goal closed under cvc5 with `crush.ho.mode "native"`. The refusal is in shared
translation code, so it covers every backend and mode. -/

/--
error: crush: cannot translate a quantifier over the dependent function type
-/
#guard_msgs(error, substring := true) in
set_option crush.backend "cvc5" in
example (β : Nat → Type) (F : β 0 → Int) (G : ((n : Nat) → β n) → Int)
    (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = F (k 0)) : G c = G d := by
  crush

/--
error: crush: cannot translate a quantifier over the dependent function type
-/
#guard_msgs(error, substring := true) in
set_option crush.backend "cvc5" in
set_option crush.ho.mode "native" in
example (β : Nat → Type) (F : β 0 → Int) (G : ((n : Nat) → β n) → Int)
    (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = F (k 0)) : G c = G d := by
  crush

/-! ## Control — the non-dependent shape is unaffected

The same goal with `Int → Int` in place of `(n : Nat) → β n` is
`must_reject_ho_constant` in `Test/HigherOrder.lean`: the encoding connects the
binder to its applications, and the goal is rejected on the merits with a model
rather than refused during translation. Repeated here so the contrast is visible in
one file. -/

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example (g : (Int → Int) → Int) (h : ∀ f : Int → Int, g f = f 0) :
    g (fun x => x) = g (fun x => x + 1) := by
  crush

theorem nondependent_ho_still_works (g : (Int → Int) → Int)
    (h : ∀ f : Int → Int, g f = f 0) : g (fun x => x + 1) = 1 := by
  crush

/-! ## Dependent contexts that still work

Only *quantifying over* a dependent function type is refused. A dependent function
in the local context is a constant: its applications are keyed on the head, so the
first-order symbol it receives is faithful. -/

theorem dependent_refl (β : Nat → Type) (c : (n : Nat) → β n) : c 0 = c 0 := by
  crush

-- A dependent function applied at a fixed point, never quantified over: the proof
-- argument is dropped and `f` becomes an ordinary first-order symbol. This is
-- `dependent_proof_binder` in `Test/Theories.lean`, kept here as the boundary case
-- on the sound side.
theorem dependent_proof_argument (f : (n : Nat) → n > 0 → Nat) (h5 : (5 : Nat) > 0)
    (hf : ∀ n, ∀ hn : n > 0, f n hn = n) : f 5 h5 = 5 := by
  crush

/-! ## The completeness cost

A binder that is never applied could in principle be encoded soundly — the
disconnection is harmless when nothing applies it. Refusing by type gives that up:
the goal below is true, and it closed before the refusal was added. Pinned so the
cost is visible, and so that a later refinement which recovers such goals shows up
here as a deliberate change rather than a silent one.

A single instantiation (`h c : G c = 0`) is unaffected in practice, because the
checked finishers close it before translation runs; the cost falls on goals that
need the solver to use the hypothesis more than once. -/

/--
error: crush: cannot translate a quantifier over the dependent function type
-/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (G : ((n : Nat) → β n) → Int) (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = 0) : G c = G d := by
  crush
