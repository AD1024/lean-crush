import Crush

/-!
Tests for the higher-order encoding: λ-abstractions, function-typed quantifiers,
function equality, and partial application.

Negative tests — goals that are *false* in Lean and must be rejected rather than
closed — are wrapped in `#guard_msgs`, which pins the rejection message, so a
regression that lets `crush` close one **fails the build**. `substring := true`
matches only the stable prefix, keeping the solver-dependent counterexample text
out of the expectation.

The negative tests here guard against a real unsoundness, not merely
incompleteness. An arrow type used to become an opaque sort with a function-typed
bound variable declared as an *unrelated* function symbol, so

```lean
h : ∀ (f : Int → Int), g f = f 0
```

was emitted as `(forall ((q Fn)) (= (g q) (q' 0)))` where `q'` is a fresh constant
unrelated to `q` — asserting that **`g` is constant**, strictly stronger than `h`.
`must_reject_ho_constant` is a goal `crush` therefore *closed*, even though its
negation is provable in Lean.
-/

open Crush

-- These higher-order goals close under the **default `reconstruct` policy** —
-- kernel-checked, not trusted. The `funext`-prefixed reconstruction finishers replay a
-- function-equality `unsat` via `funext`+`simp_all` rather than the `crushSorry` axiom
-- (`#print axioms ho_funext` below pins this). The file used to need `crush.trust
-- "trust"`; the finishers made that unnecessary.
set_option crush.trust "reconstruct"
set_option crush.timeout 10

/-! ## Applying a function-typed hypothesis to a λ

The core defunctionalization path: the λ becomes a closure constant with a defining
axiom `app(clo, x) = body`, and the quantified `f` is applied via `app`. -/

theorem ho_beta (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => x + 1) = 1 := by crush

theorem ho_id (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => x) = 0 := by crush

-- A λ whose body needs a theory operator, not just arithmetic.
theorem ho_ite (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => if x > 0 then x else 42) = 42 := by crush

/-! ## Closures with captured variables

A λ capturing an SMT-bound variable becomes a *parameterized* constructor
`clo : (captures) → Fn` with axiom `app(clo(ȳ), x) = body[x, ȳ]`. -/

theorem ho_capture (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0)
    (n : Int) : g (fun x => x + n) = n := by crush

-- Distinct captures must yield distinct closures, not a shared one.
theorem ho_capture_distinct (g : (Int → Int) → Int)
    (h : ∀ (f : Int → Int), g f = f 0) (n m : Int) (hnm : n ≠ m) :
    g (fun x => x + n) ≠ g (fun x => x + m) := by crush

/-! ## η-expansion of named functions

Passing a *named* function where a function value is expected: `f` keeps its
first-order declaration and additionally gets a closure bridged by
`app(clo, x) = f(x)`. -/

theorem ho_eta (g : (Int → Int) → Int) (f : Int → Int)
    (h : ∀ (u : Int → Int), g u = u 0) (hf : ∀ x, f x = x + 7) : g f = 7 := by crush

/-! ## Extensionality

Function equality needs the extensionality axiom, emitted on demand per arrow
sort. It is load-bearing: `∀ x, f x = g x ⊢ f = g` is `sat` (unprovable) without
it and `unsat` with it — verified directly against z3. -/

theorem ho_funext (f g : Int → Int) (h : ∀ x, f x = g x) : f = g := by crush

/-! ## Higher-order functions of several arguments -/

theorem ho_two_args (c : (Int → Int) → Int → Int) (h : ∀ f x, c f x = f x) :
    c (fun y => y) 5 = 5 := by crush

theorem ho_curried (f : Int → Int → Int) (h : ∀ x y, f x y = x + y) :
    f 1 2 = 3 := by crush

/-! ## Partial application

`app` is *n*-ary over the flattened argument list, so a partially-applied curried
function is handled by the same η-expansion as a named function: `f 1` becomes a
closure with `app(clo, x) = f(1, x)`. -/

theorem ho_partial (f : Int → Int → Int) (g : (Int → Int) → Int)
    (h : ∀ (u : Int → Int), g u = u 0) (hf : ∀ x y, f x y = x + y) :
    g (f 1) = 1 := by crush

/-! ## The higher-order proofs are kernel-checked, not trusted

`ho_funext` is the function-equality shape that needs `funext` to reconstruct. Its
axiom set is the standard-library trio, with **no `crushSorry`** — so the solver and
the encoding are outside the trusted base; the kernel re-checked the proof. -/

/-- info: 'ho_funext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ho_funext

/-! ## Negative cases — must be REJECTED

Every goal here is **false in Lean**. `must_reject_ho_constant` is the original
unsoundness: `crush` closed it, yet `g (fun x => x) ≠ g (fun x => x + 1)` is
provable from `h` (the two sides reduce to `0` and `1`). -/

/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_ho_constant (g : (Int → Int) → Int)
    (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => x) = g (fun x => x + 1) := by crush

-- Distinct closures must not be conflated even with no hypothesis to relate them.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_closure_conflate (g : (Int → Int) → Int) :
    g (fun x => x) = g (fun x => x + 1) := by crush

-- Extensionality must not be strong enough to equate arbitrary functions.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_funext_free (f g : Int → Int) : f = g := by crush

/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_lambda_eq : (fun x : Int => x) = (fun x : Int => x + 1) := by crush

-- Knowing `g` at one closure says nothing about another.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_partial_info (g : (Int → Int) → Int) (h : g (fun x => x) = 0) :
    g (fun x => x + 1) = 0 := by crush

-- Different captured values give different results.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem must_reject_capture_conflate (g : (Int → Int) → Int)
    (h : ∀ (f : Int → Int), g f = f 0) (n m : Int) :
    g (fun x => x + n) = g (fun x => x + m) := by crush
