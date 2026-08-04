import Crush

/-!
Milestone-3 tests: the higher-order encoding (`Doc/PLAN.md` §5).

This is the capability lean-auto lacks — it throws "Higher order input?" on these
goals — and the reason the project exists.

As in `Test/M2.lean`, negative cases use `first | (crush; done) | sorry`, so a
regression turns the `sorry` into a closed proof and the build's `sorry` warning
disappears — the signal we watch for.

**These are regressions for a real unsoundness, not only a feature.** Before this
milestone an arrow type became an opaque sort and a function-typed bound variable
was declared as an *unrelated* `declare-fun`. So

```lean
h : ∀ (f : Int → Int), g f = f 0
```

was emitted as `(forall ((q Fn)) (= (g q) (q' 0)))` with `q'` a fresh constant
unrelated to `q` — asserting that **`g` is constant**, strictly stronger than `h`.
`must_reject_ho_constant` below is a goal `crush` *did* close while its negation is
provable in Lean.
-/

open Crush

set_option crush.trust "trust"
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

/-! ## Negative cases — must be REJECTED

Every goal here is **false in Lean**. `must_reject_ho_constant` is the original
unsoundness: `crush` closed it, yet `g (fun x => x) ≠ g (fun x => x + 1)` is
provable from `h` (the two sides reduce to `0` and `1`). -/

theorem must_reject_ho_constant (g : (Int → Int) → Int)
    (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => x) = g (fun x => x + 1) := by
  first | (crush; done) | sorry

-- Distinct closures must not be conflated even with no hypothesis to relate them.
theorem must_reject_closure_conflate (g : (Int → Int) → Int) :
    g (fun x => x) = g (fun x => x + 1) := by
  first | (crush; done) | sorry

-- Extensionality must not be strong enough to equate arbitrary functions.
theorem must_reject_funext_free (f g : Int → Int) : f = g := by
  first | (crush; done) | sorry

theorem must_reject_lambda_eq : (fun x : Int => x) = (fun x : Int => x + 1) := by
  first | (crush; done) | sorry

-- Knowing `g` at one closure says nothing about another.
theorem must_reject_partial_info (g : (Int → Int) → Int) (h : g (fun x => x) = 0) :
    g (fun x => x + 1) = 0 := by
  first | (crush; done) | sorry

-- Different captured values give different results.
theorem must_reject_capture_conflate (g : (Int → Int) → Int)
    (h : ∀ (f : Int → Int), g f = f 0) (n m : Int) :
    g (fun x => x + n) = g (fun x => x + m) := by
  first | (crush; done) | sorry
