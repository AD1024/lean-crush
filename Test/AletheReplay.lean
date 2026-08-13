import Crush

/-!
Tests for Alethe proof replay (`Crush/Solver/AletheReplay.lean`), whose module comment has
the design; these tests pin its two observable properties.

1. **Payoff.** The goals below were measured (2026-08-06) to be exactly the class replay is
   for: cvc5 returns a hole-free proof and the finisher ladder *fails*, so before replay
   they errored under the default policy.
2. **Declining rather than trusting.** Soundness is independent of rule coverage: a step
   replay cannot handle makes it decline, and the ladder runs instead. The negative tests
   pin that every path to a closed goal runs through the kernel.
-/

open Crush

section Payoff
set_option crush.backend "cvc5"
set_option crush.timeout 20
-- Replay only runs under a reconstructing policy, and the shipped default is `trust`
-- (which closes on the solver's word without consulting a certificate). Every section
-- below therefore asks for `reconstruct` explicitly.
set_option crush.trust "reconstruct"

/-! ## Goals the finisher ladder cannot reconstruct, but replay can

Both are kernel-checked: `#print axioms` shows the standard-library trio and no
`crushSorry`, so the solver is outside the trusted base. -/

/-- Boolean pigeonhole: four `Bool`s, so two must agree. cvc5's proof is ~62 steps across
`cong`/`resolution`/`trans`/`rare_rewrite`/…; the single-shot ladder cannot find it. -/
theorem bool_pigeonhole (p q r s : Bool) :
    p = q ∨ p = r ∨ p = s ∨ q = r ∨ q = s ∨ r = s := by crush

/-- info: 'bool_pigeonhole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bool_pigeonhole

/-- EUF conflict: `a = b` forces `f a = f b`, contradicting `f a = 1` and `f b = 2`. Needs a
congruence step plus a literal evaluation — a 22-step chain. -/
theorem euf_conflict (f : Int → Int) (a b c : Int)
    (h1 : f a = 1) (h2 : f b = 2) (h3 : f c = 3) (hab : a = b) : False := by crush

/-- info: 'euf_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms euf_conflict

end Payoff

/-! ## Harder cases, with the ladder switched off

Everything below runs under `crush.reconstruct "alethe"`, which removes the finisher-ladder
fallback. That matters for a test: under the default `auto` a goal can pass because the
ladder quietly rescued it, so these would not actually be exercising replay. Here a passing
theorem *is* a replayed certificate, and each is kernel-checked.

Scaled up along the two axes that make a certificate long — chain depth and boolean
branching — since replay's whole claim is that step count is not the obstacle. -/

section Harder
set_option crush.backend "cvc5"
set_option crush.timeout 30
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"

/-- A five-variable pigeonhole: ten disjuncts, so the case analysis is substantially wider
than `bool_pigeonhole`'s six. -/
theorem bool_pigeonhole5 (p q r s t : Bool) :
    p = q ∨ p = r ∨ p = s ∨ p = t ∨ q = r ∨ q = s ∨ q = t ∨ r = s ∨ r = t ∨ s = t := by crush

/-- info: 'bool_pigeonhole5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bool_pigeonhole5

/-- A four-step equality chain before the congruence: `a = b = c = d = e`, so `f a` and `f e`
must agree, contradicting the two literals. Deeper than `euf_conflict`'s single step. -/
theorem euf_chain4 (f : Int → Int) (a b c d e : Int)
    (h1 : a = b) (h2 : b = c) (h3 : c = d) (h4 : d = e)
    (h5 : f a = 1) (h6 : f e = 2) : False := by crush

/-- info: 'euf_chain4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms euf_chain4

/-- Congruence on a *binary* function, with both arguments rewritten at once. -/
theorem euf_binary (f : Int → Int → Int) (a b c d : Int) (h1 : a = b) (h2 : c = d) :
    f a c = f b d := by crush

/-- Disequality-driven: the conflict is `f a ≠ f c` against a transitive chain, so the
refutation has to derive the congruence and then resolve it against a negated literal. -/
theorem euf_diseq (f : Int → Int) (a b c : Int)
    (h1 : a = b) (h2 : b = c) (h3 : f a ≠ f c) : False := by crush

/-- Boolean implication chaining through a conjunction — propositional structure rather than
equality reasoning, exercising `resolution`/`and`/`implies` rules. -/
theorem bool_chain (p q r s : Bool) (h1 : p = true) (h2 : q = true)
    (h3 : (p && q) = true → r = true) (h4 : r = true → s = true) : s = true := by crush

/-- info: 'bool_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bool_chain

/-- A `Bool` disequality forced into its two concrete cases. -/
theorem bool_diseq (p q : Bool) (h : p ≠ q) :
    (p = true ∧ q = false) ∨ (p = false ∧ q = true) := by crush

/-- info: 'bool_diseq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bool_diseq

-- Three-way transitivity between *uninterpreted functions* at the same point declines
-- (measured 2026-08-06). `f a = g a`, `g a = h a`, `h a = 7 ⊢ f a = 7` is provable and the
-- ladder closes it under `auto`; what replay cannot do is map some step of cvc5's chosen
-- certificate back. Pinned so that extending term translation shows up here.
/-- error: crush: `crush.reconstruct alethe` is set and the solver's Alethe certificate -/
#guard_msgs(error, substring := true) in
example (f g h : Int → Int) (a : Int)
    (h1 : f a = g a) (h2 : g a = h a) (h3 : h a = 7) : f a = 7 := by crush

end Harder

/-! ## Replay declines rather than trusting

These cases distinguish a replay decline followed by checked core reconstruction from a
false goal. A declined certificate is never taken on faith. -/

section Declines
set_option crush.backend "cvc5"
set_option crush.timeout 20
set_option crush.trust "reconstruct"

inductive Three where | a | b | c

-- cvc5 cannot express this datatype exhaustiveness argument in Alethe, but bounded
-- finite-enum splitting reconstructs it after replay declines.
theorem enum_falls_back (w x y z : Three) :
    w = x ∨ w = y ∨ w = z ∨ x = y ∨ x = z ∨ y = z := by
  crush

-- Certificate replay declines nonlinear arithmetic, but datatype-generic constructor
-- splitting lets core reconstruction normalize the two `Int` constructors and close the
-- resulting branches. The result remains kernel-checked.
theorem nonlinear_falls_back (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by crush

/-- info: 'nonlinear_falls_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nonlinear_falls_back

-- A goal that is simply false: the solver returns `sat`, so replay never runs. Pins that the
-- machinery cannot manufacture a proof of a non-theorem.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (p q : Bool) : p = q := by crush

/-! ### Declining a `forall_inst` step still closes the goal

The pre-SMT checked pass now applies this local invariant directly, so no certificate or
core reconstruction is needed. -/
theorem forall_inst_falls_back (f : Int → Int) (h : ∀ x, f x = 0) : f 5 = 0 := by crush

/-- info: 'forall_inst_falls_back' does not depend on any axioms -/
#guard_msgs in
#print axioms forall_inst_falls_back

end Declines

/-! ## Choosing a path with `crush.reconstruct`

z3 emits no Alethe proof, so the ladder does the work there and the same goals close either
way. `crush.reconstruct core` selects the ladder explicitly, and `alethe` selects
certificate replay with no fallback — so a goal only the ladder can close *fails* under it,
which is what makes the two paths independently testable. -/

section Toggle
set_option crush.timeout 20
set_option crush.trust "reconstruct"

-- z3 (default backend): no certificate, ladder reconstructs as before.
theorem z3_unaffected (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'z3_unaffected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms z3_unaffected

-- `core`: the ladder only, certificate ignored.
set_option crush.backend "cvc5" in
set_option crush.reconstruct "core" in
theorem core_only (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'core_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms core_only

-- `alethe`: certificate only. The pigeonhole needs replay, so it still closes here — and
-- being kernel-checked under `alethe` proves replay itself did the work, with no ladder to
-- fall back on.
set_option crush.backend "cvc5" in
set_option crush.reconstruct "alethe" in
theorem alethe_only (p q r s : Bool) :
    p = q ∨ p = r ∨ p = s ∨ q = r ∨ q = s ∨ r = s := by crush
/-- info: 'alethe_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alethe_only

-- The converse: this certificate still declines, and unlike a direct quantified instance
-- the pre-SMT pass cannot close it. Under `alethe` there is no ladder to rescue it, so it
-- errors rather than silently closing.
/-- error: crush: `crush.reconstruct alethe` is set and the solver's Alethe certificate -/
#guard_msgs(error, substring := true) in
set_option crush.backend "cvc5" in
set_option crush.reconstruct "alethe" in
example (f g h : Int → Int) (a : Int)
    (h1 : f a = g a) (h2 : g a = h a) (h3 : h a = 7) : f a = 7 := by
  crush

end Toggle
