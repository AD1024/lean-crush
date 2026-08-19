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

/-- info: 'bool_diseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bool_diseq

-- Three-way transitivity between uninterpreted functions exercises congruence and
-- transitivity steps over applications rather than arithmetic terms.
theorem euf_function_chain (f g h : Int → Int) (a : Int)
    (h1 : f a = g a) (h2 : g a = h a) (h3 : h a = 7) : f a = 7 := by crush

end Harder

/-! ## String theory

cvc5 introduces variadic concatenation, signed arithmetic, and `str.substr` terms while
proving facts about Crush's string lowering. These tests run without the core fallback, so
each one checks both Alethe term conversion and the corresponding concrete rewrite steps. -/

section StringTheory
set_option crush.backend "cvc5"
set_option crush.timeout 30
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"

theorem string_append_fresh (x : String) : x ++ "'" ++ "'" ≠ x := by crush

theorem string_append_length (a b : String) :
    (a ++ b).length = a.length + b.length := by crush

theorem string_append_prefix (a b : String) :
    (a ++ b).startsWith a = true := by crush

theorem string_append_suffix (a b : String) :
    (a ++ b).endsWith b = true := by crush

theorem string_append_contains (a b : String) :
    (a ++ b).contains a = true := by crush

-- cvc5's proof contains a two-assumption block with another two-assumption block nested
-- inside it. Replay must discharge both scopes before the closing proof can escape.
theorem string_append_isEmpty (a b : String) :
    (a ++ b).isEmpty = (a.isEmpty && b.isEmpty) := by crush

end StringTheory

/-! ## Arithmetic, datatypes, and conditionals -/

section TheoryReplay
set_option crush.backend "cvc5"
set_option crush.timeout 30
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem alethe_linear_arithmetic (f : Int → Int) (a b c : Int)
    (hab : a ≤ b) (hbc : b < c) (hf : f a = 0) :
    a < c ∧ f a ≤ 1 := by
  crush

theorem alethe_nonlinear_arithmetic (x : Int)
    (h : x * x = 4) (h2 : x > 0) : x = 2 := by
  crush

theorem alethe_nat_arithmetic (x y : Nat) (h : x + 3 ≤ y) : x < y := by
  crush

theorem alethe_ite (p q r s : Bool) (x y : Int) :
    (if p then x else y) = x ∨
    (if q then x else y) = x ∨
    (if r then x else y) = x ∨
    (if s then x else y) = x ∨
    (if p then x else y) = y := by
  crush

theorem alethe_int_mod (x : Int) :
    x % 2 = 0 ∨ x % 2 = 1 := by
  crush

theorem alethe_int_div_mod (x : Int) :
    x = 2 * (x / 2) + x % 2 := by
  crush

theorem alethe_datatype_injective (x y : Int) (xs ys : List Int)
    (h : x :: xs = y :: ys) :
    x = y ∧ xs = ys := by
  crush

end TheoryReplay

/-! ## Bit-vectors -/

section BitVectorReplay
set_option crush.backend "cvc5"
set_option crush.timeout 30
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem alethe_bitvec_xor (x y : BitVec 8) :
    (x ^^^ y) ^^^ y = x := by
  crush

theorem alethe_bitvec_order (x : BitVec 8) :
    x ≤ 255 := by
  crush

end BitVectorReplay

/-! ## Quantifiers and higher-order encoding -/

section QuantifiedReplay
set_option crush.backend "cvc5"
set_option crush.timeout 30
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem alethe_quantified (f : Int → Int)
    (h : ∀ x, f (x + 1) = f x + 1) :
    f 3 = f 0 + 3 := by
  crush

theorem alethe_nat_quantified (f : Nat → Nat)
    (h : ∀ x, f (x + 1) = f x + 1) :
    f 3 = f 0 + 3 := by
  crush

theorem alethe_bool_function (f : Bool → Bool)
    (h : ∀ x, f x = x) :
    f true = true := by
  crush

theorem alethe_higher_order_defun (f g : Int → Int)
    (h : ∀ x, f x = g x) :
    f = g := by
  crush

end QuantifiedReplay

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

-- A goal that is simply false: the solver returns `sat`, so replay never runs. Pins that the
-- machinery cannot manufacture a proof of a non-theorem.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example (p q : Bool) : p = q := by crush

/-! ### A direct quantified instance closes before SMT

The checked pre-SMT pass applies this local invariant directly in automatic mode. The
`alethe_quantified` test above exercises certificate-level quantifier instantiation. -/
theorem forall_inst_falls_back (f : Int → Int) (h : ∀ x, f x = 0) : f 5 = 0 := by crush

/-- info: 'forall_inst_falls_back' does not depend on any axioms -/
#guard_msgs in
#print axioms forall_inst_falls_back

end Declines

/-! ## Cases where cvc5 emits no Alethe certificate

cvc5 1.3.4 proves each goal unsatisfiable, but its `(get-proof)` response is an error:
finite datatype and array proofs contain `DUMMY_SKOLEM`, while native higher-order proofs
contain higher-order elements. These are solver certificate-generation limitations, not
replay-rule gaps, and Alethe-only mode must fail rather than trust the verdict. -/

section NoCertificate
set_option crush.backend "cvc5"
set_option crush.timeout 30
set_option crush.trust "reconstruct"
set_option crush.reconstruct "alethe"

/-- error: crush: cvc5 did not emit an Alethe certificate -/
#guard_msgs(error, substring := true) in
example (w x y z : Three) :
    w = x ∨ w = y ∨ w = z ∨ x = y ∨ x = z ∨ y = z := by
  crush

/-- error: crush: cvc5 did not emit an Alethe certificate -/
#guard_msgs(error, substring := true) in
example (a : Array Int) (i : Nat) (v : Int) (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  crush

set_option crush.ho.mode "native" in
/-- error: crush: cvc5 did not emit an Alethe certificate -/
#guard_msgs(error, substring := true) in
example (g : (Int → Int) → Int)
    (h : ∀ f, g f = f 0) (k : Int → Int) (hk : k 0 = 7) :
    g k = 7 := by
  crush

end NoCertificate

/-! ## Choosing a path with `crush.reconstruct`

z3 emits no Alethe proof, so the ladder does the work there and the same goals close either
way. `crush.reconstruct core` selects the ladder explicitly, and `alethe` selects
certificate replay with no fallback — so a goal only the ladder can close *fails* under it,
which is what makes the two paths independently testable. -/

section Toggle
set_option crush.timeout 20
set_option crush.trust "reconstruct"

/-- error: crush: `crush.reconstruct alethe` requires the cvc5 backend -/
#guard_msgs(error, substring := true) in
set_option crush.reconstruct "alethe" in
example (x : Int) : x = x := by
  crush

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

-- A strict hint list with unselected ambient hypotheses in scope. Each step is proved as a
-- closed implication of its explicit premises, so the surrounding propositions — including
-- a contradictory one — cannot contribute, and replay still produces a checked proof.
set_option crush.backend "cvc5" in
set_option crush.reconstruct "alethe" in
theorem alethe_restricted_hints (p q r s : Bool) (n : Int)
    (unrelated1 : n = 0) (unrelated2 : n = 1) (unrelated3 : n > 5) :
    p = q ∨ p = r ∨ p = s ∨ q = r ∨ q = s ∨ r = s := by crush []
/-- info: 'alethe_restricted_hints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alethe_restricted_hints

-- This application chain is also replayable with the ladder disabled.
set_option crush.backend "cvc5" in
set_option crush.reconstruct "alethe" in
theorem alethe_only_function_chain (f g h : Int → Int) (a : Int)
    (h1 : f a = g a) (h2 : g a = h a) (h3 : h a = 7) : f a = 7 := by
  crush

end Toggle
