import Crush

/-!
# Dependent types are refused

crush has no sound way to translate a dependent type to SMT, so it refuses one
with an error instead. A dependent type is either

* a type that depends on a value, such as `Fin n`, `Fin 5`, `BitVec k` or `β 0`, or
* a function type whose result type depends on its argument, such as
  `(n : Nat) → β n` or `(α : Type) → α → Nat`.

Before this check, crush translated these types to uninterpreted SMT sorts. That
let it prove false statements in two ways.

**One sort for many types.** An SMT sort cannot change with the value of a
variable, so under `∀ n`, every `Fin n` got the same sort. The hypothesis
`∀ n, (∀ x y : Fin n, x = y) ↔ n ≤ 1` is true in Lean. In SMT it said that a single
sort has at most one element (the case `n = 0`) and also has two different
elements (the case `n = 2`). That is a contradiction, so crush proved `False` from
a true hypothesis.

**A function cut off from its applications.** For a quantified function
`k : (n : Nat) → β n`, crush declared an application such as `k 0` as a new
constant with no link to `k`. The hypothesis `∀ k, G k = F (k 0)` then said that
`G` returns the same result for every `k`. That is much stronger than what the
hypothesis says in Lean, and crush proved the false goal `G c = G d`.
`Test/HigherOrder.lean` checks the same problem for ordinary function types, which
crush does translate correctly.

Types that crush can translate soundly, such as `BitVec 8` or `DecidableEq α`, are
not affected, because they are handled before the check runs.
-/

open Crush

/-! ## False statements that crush used to prove

Each statement below is false in Lean, but crush proved it before this check. The
comment on each one explains why it is false. -/

-- The hypothesis is true: `Fin 0` and `Fin 1` have at most one element, and
-- `Fin n` contains both `0` and `1` when `n ≥ 2`. So `False` does not follow.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (h : ∀ n : Nat, (∀ x y : Fin n, x = y) ↔ n ≤ 1) : False := by
  crush

-- The same problem with a bitvector whose width is a variable. The hypothesis is
-- true: `BitVec 0` has one element, and `BitVec k` has at least two when `k ≥ 1`.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (h : ∀ k : Nat, (∀ a b : BitVec k, a = b) ↔ k = 0) : False := by
  crush

-- The same problem with any family of types. The hypothesis holds when
-- `β := fun n => Fin (n + 1)`, so `False` does not follow.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (h : ∀ n, (∀ x y : β n, x = y) ↔ n = 0) : False := by
  crush

-- A quantified function whose result type depends on its argument. Take
-- `β := fun _ => Nat`, `F := Int.ofNat`, `G := fun k => (k 0 : Int)`,
-- `c := fun _ => 0` and `d := fun _ => 1`. Every hypothesis holds, and the goal
-- says `0 = 1`.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (F : β 0 → Int) (G : ((n : Nat) → β n) → Int)
    (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = F (k 0)) : G c = G d := by
  crush

-- The same when the result type depends on a type argument. Take `F := id`,
-- `G := fun k => k Nat 0`, `c := fun _ _ => 0` and `d := fun _ _ => 1`. Every
-- hypothesis holds, and the goal says `0 = 1`.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (G : ((α : Type) → α → Nat) → Nat) (F : Nat → Nat)
    (c d : (α : Type) → α → Nat)
    (h : ∀ k : (α : Type) → α → Nat, G k = F (k Nat 0)) : G c = G d := by
  crush

/-! ## Settings do not change the result

The check runs during translation, before any solver is called, so the trust
policy, the solver and the higher-order mode make no difference. The last two
examples need `cvc5` on `PATH`, like `Test/Cvc5.lean`. -/

/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
set_option crush.trust "reconstruct" in
example (h : ∀ n : Nat, (∀ x y : Fin n, x = y) ↔ n ≤ 1) : False := by
  crush

/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
set_option crush.backend "cvc5" in
example (β : Nat → Type) (F : β 0 → Int) (G : ((n : Nat) → β n) → Int)
    (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = F (k 0)) : G c = G d := by
  crush

/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
set_option crush.backend "cvc5" in
set_option crush.ho.mode "native" in
example (β : Nat → Type) (F : β 0 → Int) (G : ((n : Nat) → β n) → Int)
    (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = F (k 0)) : G c = G d := by
  crush

/-! ## Every occurrence is refused, not only quantifiers

These goals are false, so no checked proof can close them before translation, and
each one reaches the check. -/

-- An existential over a dependent function type.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (G : ((n : Nat) → β n) → Int) :
    ∃ k : (n : Nat) → β n, G k = 0 := by
  crush

-- A variable whose type depends on a fixed value.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (x y : Fin 5) : x = y := by
  crush

-- A dependent function from the context, applied to a value: `c 0` has type `β 0`.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (c d : (n : Nat) → β n) : c 0 = d 0 := by
  crush

/-! ## Types that are not refused

These types look dependent, but crush either has a sound translation for them or
removes the dependency first. -/

-- `DecidableEq Int` is a function type whose result depends on its arguments. A
-- sort handler translates it to a one-element sort, which is exact because there
-- is only one `DecidableEq Int` instance up to equality. This goal needs the solver.
theorem decidableEq_quantifier (G : DecidableEq Int → Int) (x : Int)
    (h : ∀ inst : DecidableEq Int, G inst = x) (hx : x + 1 = 3) (i : DecidableEq Int) :
    G i + G i = 4 := by
  crush

-- A bitvector with a literal width has its own SMT sort.
theorem literal_width_bitvec (a b : BitVec 8) : a + b = b + a := by
  crush

-- A function whose only dependency is on a proof argument. crush drops proof
-- arguments, so `f 5 h5` becomes an ordinary function applied to `5`. The goal is
-- false, so the solver finds a counterexample; what matters is that translation
-- accepts the type instead of refusing it.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example (f : (n : Nat) → n > 0 → Nat) (h5 : (5 : Nat) > 0) : f 5 h5 = 3 := by
  crush

-- An ordinary function type, for comparison with the refusals above. The true
-- goal is proved, and the false one gets a counterexample instead of a refusal.
theorem nondependent_function (g : (Int → Int) → Int)
    (h : ∀ f : Int → Int, g f = f 0) : g (fun x => x + 1) = 1 := by
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example (g : (Int → Int) → Int) (h : ∀ f : Int → Int, g f = f 0) :
    g (fun x => x) = g (fun x => x + 1) := by
  crush

/-! ## What the refusal costs

Refusing every dependent type also refuses some goals that crush used to prove
correctly. Each goal below is true, was proved before this check, and is now
refused. They are kept here so the cost is visible, and so that a later change
that accepts them again shows up here as a deliberate decision. -/

-- A type that depends on a fixed value.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (f : Fin 5 → Int) (x y : Fin 5) (h1 : f x = 1) (h2 : f y = 2) : x ≠ y := by
  crush

-- A dependent function from the context, applied to a value.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (c : (n : Nat) → β n) (F : β 0 → Int) (h : F (c 0) = 3) :
    F (c 0) + 1 = 4 := by
  crush

-- A quantified dependent function that is never applied.
/-- error: crush: cannot translate the dependent type -/
#guard_msgs(error, substring := true) in
example (β : Nat → Type) (G : ((n : Nat) → β n) → Int) (c d : (n : Nat) → β n)
    (h : ∀ k : (n : Nat) → β n, G k = 0) : G c = G d := by
  crush
