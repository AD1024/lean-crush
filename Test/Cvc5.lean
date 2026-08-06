import Crush

/-!
Tests that exercise the **cvc5 backend** and the **`native` higher-order mode**.

The rest of the suite runs on the default `z3` / `defunctionalize` path, so without
this file the cvc5 process integration and the native-HO encoding (`HO_ALL` logic,
`(-> σ τ)` sorts, `lambda` terms) are built but never actually run — a gap found
while adding CI. These are the tests that keep those paths honest.

**Requires `cvc5` on `PATH`.** CI installs it; a local run without it will report the
process launch failing rather than a proof failing. The goals are deliberately ones
already proved on the z3 path elsewhere in the suite, so a failure here points at the
backend or the native encoding, not at the goal being unprovable.

`native` HO mode gates on cvc5 specifically: it emits an `HO_`-prefixed logic that
only cvc5 honours (z3 warns and then chokes on the function sorts), so these two
features are naturally tested together.
-/

open Crush

set_option crush.trust "trust"
set_option crush.timeout 10
set_option crush.backend "cvc5"

/-! ## cvc5 as a first-order backend

The basic process round-trip against cvc5 rather than z3: spawn, feed the script,
read `unsat`. -/

theorem cvc5_eq_symm (x y : Int) (h : x = y) : y = x := by crush

theorem cvc5_linear (x y : Int) (h : x ≤ y) : x < y + 1 := by crush

theorem cvc5_uf (f : Int → Int) (a b : Int) (h : a = b) : f a = f b := by crush

/-! ## cvc5 with theories

Datatypes and `Nat`→`Int` guards through cvc5's datatype and arithmetic solvers. -/

theorem cvc5_datatype (a b : Int) (h : some a = some b) : a = b := by crush

theorem cvc5_nat_sub : ∀ n : Nat, n - 1 ≤ n := by crush

theorem cvc5_string_assoc (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by crush

/-! ## Native higher-order mode (`crush.ho.mode native`)

Instead of defunctionalizing, the arrow type stays a first-class `(-> Int Int)` sort
and the λ is emitted as a `lambda` term under the `HO_ALL` logic. cvc5's higher-order
solver discharges it directly. These are the *same* goals `Test/HigherOrder.lean`
proves via defunctionalization, so a difference isolates the native encoding. -/

section Native
set_option crush.ho.mode "native"

theorem cvc5_ho_beta (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => x + 1) = 1 := by crush

theorem cvc5_ho_id (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => x) = 0 := by crush

-- Function-typed quantifier applied via native application rather than an `app`
-- symbol: the shape that was historically an unsoundness on the encoded path.
theorem cvc5_ho_quant (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0)
    (k : Int → Int) (hk : k 0 = 7) : g k = 7 := by crush

-- Native mode names the arbitrary function-valued `ite` with a local SMT `let`
-- before applying it.
theorem cvc5_ho_conditional_head (p : Prop) [Decidable p] (f g : Int → Int)
    (x y : Int) (h : x = y) :
    (if p then f else g) x = (if p then f else g) y := by crush

end Native

/-! ## Native HO still rejects false goals

The native encoding must be sound as well as complete: a goal false in Lean must not
close just because it went through cvc5's HO solver. The rejection here is `unknown`,
not a counterexample.

This turns out to be a **backend** difference, not a mode one: the *same* false goal
reports `unknown` under both cvc5 modes (native and defunctionalize), but z3 with
defunctionalize returns an actual `sat` counterexample. z3's model-based quantifier
instantiation finds a finite model for a function-typed variable where cvc5 declines
to on this shape. So cvc5 is sound-by-`unknown` on false HO goals while z3 is
additionally informative — worth knowing when choosing a backend for HO work.

Either way the rejection is sound: `unknown` never closes a goal, and what matters is
that this is not `unsat`. -/

set_option crush.ho.mode "native" in
/-- error: crush: solver returned `unknown` -/
#guard_msgs(error, substring := true) in
theorem cvc5_ho_must_reject (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0)
    (k : Int → Int) (hk : k 0 = 7) : g k = 8 := by crush

/-! ## Reconstruction is backend-agnostic

An `unsat` from cvc5 is replayed into a kernel-checked proof the same way a z3 one
is — the core-directed finisher does not care which solver produced the core. Pinned
via `#print axioms`: no `crushSorry`. -/

set_option crush.backend "cvc5" in
set_option crush.trust "reconstruct" in
theorem cvc5_reconstructs (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush

/-- info: 'cvc5_reconstructs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cvc5_reconstructs
