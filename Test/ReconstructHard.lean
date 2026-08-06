import Crush

/-!
Harder cases for **core-directed reconstruction** (`Crush/Solver/Reconstruct.lean`), the
route that works with any backend: the unsat core names the few hypotheses that mattered,
and a Lean finisher re-proves the goal from just those.

Everything here runs under `crush.reconstruct "core"`, which switches off Alethe replay. As
with `Test/AletheReplay.lean`'s `Harder` section, that is what makes the tests meaningful —
under the default `auto` a cvc5 certificate could quietly carry a goal, so the ladder would
not actually be under test. Here every passing theorem is the ladder's work, and
kernel-checked.

The cases are chosen to stress the thing core-direction is *for*: irrelevant hypotheses.
Automated tactics degrade sharply as the context grows, so a goal with 20 distractors and 2
relevant facts is where selection earns its place — `grind` on the whole context is a very
different problem from `grind` on the two facts the core named.
-/

open Crush

set_option crush.timeout 25
set_option crush.trust "reconstruct"
set_option crush.reconstruct "core"

/-! ## Selection under noise

Each goal buries a two-fact argument in unrelated hypotheses. If core selection were not
working, the finisher would be handed all of them at once. -/

section Noise

/-- Ten hypotheses, two relevant. -/
theorem noise10 (a b c d e f g h i j : Int)
    (n1 : a > 100) (n2 : b > 200) (n3 : c > 300) (n4 : d > 400) (n5 : e > 500)
    (n6 : f > 600) (n7 : g > 700) (n8 : h > 800)
    (r1 : i = j) (r2 : j = 42) : i = 42 := by crush

/-- info: 'noise10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noise10

/-- Twenty-four hypotheses, two relevant — including nonlinear distractors (`a * a ≥ 0`)
that would ordinarily push an arithmetic tactic into trouble. Since they are outside the
core, the finisher never sees them. -/
theorem noise24 (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 t u : Int)
    (p1 : a1 > 1) (p2 : a2 > 2) (p3 : a3 > 3) (p4 : a4 > 4) (p5 : a5 > 5)
    (p6 : a6 > 6) (p7 : a7 > 7) (p8 : a8 > 8) (p9 : a9 > 9) (p10 : a10 > 10)
    (q1 : a1 * a1 ≥ 0) (q2 : a2 * a2 ≥ 0) (q3 : a3 * a3 ≥ 0) (q4 : a4 * a4 ≥ 0)
    (r1 : t = u) (r2 : u = 77) : t = 77 := by crush

/-- info: 'noise24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noise24

/-- An eight-step order chain with nonlinear noise alongside. -/
theorem chain8 (x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (junk1 : x1 * x1 ≥ 0) (junk2 : x2 * x2 ≥ 0)
    (h1 : x1 ≤ x2) (h2 : x2 ≤ x3) (h3 : x3 ≤ x4) (h4 : x4 ≤ x5)
    (h5 : x5 ≤ x6) (h6 : x6 ≤ x7) (h7 : x7 ≤ x8) : x1 ≤ x8 := by crush

/-- info: 'chain8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain8

/-- A vacuous quantified hypothesis (`∀ z, f z ≥ f z`) alongside the real chain. A
quantifier in context is exactly what makes tactics loop, so keeping it out of the core is
what lets this close. -/
theorem noisy_quantifier (f g : Int → Int) (a b c : Int)
    (noise : ∀ z, f z ≥ f z) (h1 : a = b) (h2 : b = c) (h3 : f c = g c) (h4 : g c = 9) :
    f a = 9 := by crush

end Noise

/-! ## Congruence depth

Nested applications of an uninterpreted function: the argument is one equality, but it has
to be pushed through several layers. -/

section Congruence

/-- Three layers of congruence from a single premise. -/
theorem congr_depth3 (f : Int → Int) (a b : Int) (h : a = b) :
    f (f (f a)) = f (f (f b)) := by crush

/-- info: 'congr_depth3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms congr_depth3

/-- Congruence through *two different* functions and a transitive chain. -/
theorem congr_two_fns (f g : Int → Int) (a b c : Int)
    (h1 : a = b) (h2 : b = c) (h3 : f c = g c) (h4 : g c = 9) : f a = 9 := by crush

/-- A binary function, both arguments moved at once. -/
theorem congr_binary (f : Int → Int → Int) (a b c d : Int)
    (h1 : a = b) (h2 : c = d) : f a c = f b d := by crush

end Congruence

/-! ## Quantifier instantiation

The solver must pick instantiation points that are not syntactically present in the goal,
which is where premise selection stops being a matter of filtering. -/

section Instantiation

/-- One `∀` instantiated at three nested points: `0`, `f 0`, `f (f 0)`. -/
theorem inst_three_points (f : Int → Int) (h : ∀ x, f x = x + 1) :
    f (f (f 0)) = 3 := by crush

/-- info: 'inst_three_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inst_three_points

/-- Read-over-write, in the hypothesis form that translates (the pointwise-update *lambda*
does not — see `Test/CaseStudies/Loom.lean`). The `if` must be resolved by the solver, then
instantiated at `i`. -/
theorem read_over_write (arr arr' : Int → Int) (i v : Int)
    (h : ∀ k, arr' k = if k = i then v else arr k) : arr' i = v := by crush

/-- info: 'read_over_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_over_write

/-- Read-over-write at a *different* index leaves the original in place — the other half of
the array axiom, needing the `if`'s false branch. -/
theorem read_over_write_other (arr arr' : Int → Int) (i j v : Int)
    (hne : j ≠ i) (h : ∀ k, arr' k = if k = i then v else arr k) : arr' j = arr j := by crush

/-- Two unbundled order facts combined: monotonicity applied at a chain. -/
theorem mono_chain (f : Int → Int) (h : ∀ x y, x ≤ y → f x ≤ f y)
    (a b c : Int) (h1 : a ≤ b) (h2 : b ≤ c) : f a ≤ f c := by crush

end Instantiation

/-! ## Across theories

Goals whose argument crosses `Bool`, `Int`, and `String`, so reconstruction has to handle the
`Bool`-versus-`Prop` distinction and ground evaluation in the same proof. -/

section MixedTheories

/-- `String.length` on a literal: needs *computation*, which the reasoning finishers cannot
do — this is what the `subst_vars; decide` rungs of the ladder are for. -/
theorem string_len (s t : String) (h : s = "ab") (h2 : t = "cd") :
    (s ++ t).length = 4 := by crush

/-- info: 'string_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms string_len

/-- `Bool` hypothesis driving an `Int` conclusion through an implication. -/
theorem bool_drives_int (f : Int → Int) (p : Bool) (x y : Int)
    (h1 : p = true) (h2 : p = true → x = y) (h3 : f y = 3) : f x = 3 := by crush

/-- info: 'bool_drives_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bool_drives_int

/-- All three theories in one goal: a string literal's length feeds an `Int` comparison whose
result is a `Bool`. -/
theorem three_theories (s : String) (n : Int) (b : Bool)
    (h1 : s = "xy") (h2 : n = s.length) (h3 : b = (n == 2)) : b = true := by crush

/-- info: 'three_theories' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms three_theories

end MixedTheories
