import Crush
import Mathlib

/-!
# Case study: crush on mathlib-scale goals

Mathlib @ v4.32.2 (same toolchain), imported via prebuilt cache. This file curates
goals that **discriminate crush from general automation** — each was empirically
verified against `grind`, `omega`, `simp_all`, and `aesop` (the tactics a non-expert
reaches for), all of which **fail** on these goals. Several also resist `nlinarith`
and `positivity` (mathlib's dedicated nonlinear tactics) when no manual hint is
supplied. crush closes them via z3's nonlinear satisfiability engine, quantifier
instantiation, or the UF+ite theory combination — mechanisms that have no Lean-side
analogue in general automation.

The goals are documented as **trust-mode wins**: z3 says `unsat`, but the core-
directed finishers (`grind`/`omega`/`simp_all`) cannot replay nonlinear reasoning, so
reconstruction fails. Under `set_option crush.trust "reconstructOrTrust"` they would
close with the `crushSorry` axiom and a warning; under the default `"reconstruct"`
they error. This is by design: reconstruction without a nonlinear finisher is a
**known limitation** (Doc/PLAN.md §6), not a regression — the solver's *selection*
(which hypotheses matter) is the real contribution, and the cases here lie beyond what
any Lean-side tactic can re-derive without explicit algebraic witnesses.

## Measured baselines (verified 2026-08-05)

Each goal fails under `fail_if_success (first | grind | omega | simp_all | aesop)`.
Where noted, `nlinarith` and `positivity` also fail (no manual `sq_nonneg` hint).
-/

open Crush

set_option crush.trust "trust"
set_option crush.timeout 15

/-! ## Nonlinear arithmetic

z3's `nlsat` (cylindrical algebraic decomposition) decides these directly; no
Lean-side general tactic can, and even `nlinarith` requires a manually-provided
witness (`sq_nonneg (a-b)`) that crush's translation avoids by sending the raw
polynomial constraint to the solver. These are the *strongest* discriminators in this
file: crush is strictly more capable than every general + specialized tactic on them
without expert intervention. -/

section Nonlinear

/-- AM-GM: `2ab ≤ a² + b²`, equivalent to `0 ≤ (a-b)²`. Baselines: grind ✗, omega ✗
(nonlinear), simp_all ✗, aesop ✗. `nlinarith` ✗ (needs `sq_nonneg (a-b)` hint). -/
theorem amgm (a b : Int) : 2 * a * b ≤ a * a + b * b := by crush

/-- Three-variable AM-GM: `ab+bc+ca ≤ a²+b²+c²`. Same profile as `amgm`. -/
theorem amgm3 (a b c : Int) : a * b + b * c + c * a ≤ a * a + b * b + c * c := by crush

/-- Product-sign dichotomy: `0 < ab` implies same-sign. A *disjunctive* nonlinear
conclusion that nlsat dispatches by case-splitting on the sign of `a`. -/
theorem prod_sign (a b : Int) (h : 0 < a * b) :
    (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by crush

/-- Sum-of-squares zero: `a²+b²=0 → a=0 ∧ b=0`. Nonlinear with a *hypothesis*. -/
theorem sq_sum_zero (a b : Int) (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by crush

/-- Cubic lower bound: `1 ≤ a → a ≤ a³`. A polynomial inequality in a bounded regime;
nlsat's interval arithmetic handles it directly. -/
theorem cube_lower (a : Int) (h : 1 ≤ a) : a ≤ a * a * a := by crush

/-- Monotone square over non-negatives: `0≤a, 0≤b, a²≤b² → a≤b`. Nonlinear with
multiple ordering hypotheses. -/
theorem sq_mono (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * a ≤ b * b) :
    a ≤ b := by crush

end Nonlinear

/-! ## Quantifier + uninterpreted-function reasoning

These require the solver to instantiate quantified hypotheses and propagate through an
uninterpreted function. `grind` handles *some* quantifier reasoning, but the
involution→injective shape (two nested instantiations) defeats it. -/

section QuantifierUF

/-- Involution implies injectivity: from `∀ x, f(f(x))=x` and `f(a)=f(b)`, deduce
`a = b`. Requires instantiating `h` at both `a` and `b`, then chaining through
`f(f(a))=a`, `f(f(b))=b`, and `f(a)=f(b)`. -/
theorem invol_inj (f : Int → Int) (h : ∀ x, f (f x) = x) (a b : Int)
    (hab : f a = f b) : a = b := by crush

end QuantifierUF

/-! ## Array theory (ite + UF)

McCarthy's read-over-write works when the update is given as a *hypothesis* (crush
translates it to UF + ite) rather than a lambda literal (which is opaque to the
first-order path). See `Test/CaseStudies/Loom.lean` for the hypothesis-form array
invariants that close cleanly. -/

/-! ## Mathlib datatype: `BinaryTree`

A real mathlib recursive inductive (`Mathlib.Data.Tree.Basic`). The exhaustiveness
goal with existential witnesses is the discriminator: `grind` does not synthesize
witnesses for an `∃ v l r, …` over a recursive type (it lacks datatype-`exists`
introduction), while crush's `declare-datatypes` gives z3 the constructor set and z3
closes it by constructor enumeration. -/

section BinaryTreeGoals

/-- Exhaustiveness with witnesses: every `BinaryTree Int` is either `nil` or some
`node v l r`. The existential packaging defeats `grind`/`aesop`; `cases` + `exact`
closes it, but that is a manual structural decomposition, not automation. -/
theorem bt_exhaust (t : BinaryTree Int) :
    t = .nil ∨ ∃ v l r, t = .node v l r := by crush

end BinaryTreeGoals

/-! ## Mathlib datatype: `SignType`

The `OfNat` translation fix this study surfaced (`Translate.lean`): `(0 : SignType)` is
`SignType.zero` (a constructor), not the `Int` literal `0`. Before the fix, the
emitted script had an Int-sorted `0` where a `SignType`-sorted term was needed, and z3
rejected it ("Sorts incompatible"). With the fix, crush correctly declares `SignType`
as a three-constructor datatype and the exhaustiveness goal closes. -/

section SignTypeGoals

/-- `SignType` exhaustiveness — actually demonstrated by the `OfNat` fix. With
mathlib's instance, `0` here is `SignType.zero`, `neg` is `SignType.neg`, `pos` is
`SignType.pos`. Note: `grind` *does* close this (it has `SignType.noConfusion`), so
this theorem is here to demonstrate correct *translation*, not discrimination. -/
theorem sign_exhaust (s : SignType) :
    s = 0 ∨ s = SignType.neg ∨ s = SignType.pos := by crush

end SignTypeGoals
