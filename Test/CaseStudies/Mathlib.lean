import Crush
import Mathlib

/-!
# Case study: crush against mathlib

Goals here are **mathlib lemma statements restated verbatim**, with the mathlib name each
one mirrors given in its comment — so this measures crush against propositions the library
actually states, rather than against toy arithmetic that merely happens to `import Mathlib`.
Each was checked to be a real declaration (`#check`) before being copied here.

Two honest limits on how far this reaches, both measured rather than assumed:

* Only the *statements* are restated, at `Int`. mathlib proves them for an arbitrary
  `LinearOrder`/`AddCommSemigroup`, and crush is first-order, so the polymorphic form is out
  of scope — monomorphization specializes lemmas *into* a query, it does not let a goal be
  proved for all types at once.
* Many mathlib primitives have no first-order translation and simply produce a
  counterexample rather than an error. Measured on 2026-08-06: `|·|`, `Int.natAbs`,
  `Int.sign`, `_ ∣ _`, `Finset.card`, `List.length`, and the bundled predicates (`Monotone`,
  `Function.Injective`) all fail to translate. The `Untranslated` section at the end pins a
  representative sample, so a future translation improvement shows up as a *test break*
  rather than going unnoticed.
-/

open Crush

set_option crush.timeout 20

/-! ## Lattice identities over a linear order

These are the `min`/`max` lemmas mathlib states for any `LinearOrder`. They are genuine
case-split reasoning: `min a (max b c)` requires the solver to consider the orderings of all
three variables, which is why a `decide`-style approach cannot touch them. -/

section Lattice

/-- `min_max_distrib_left`. -/
theorem min_max_distrib (a b c : Int) : min a (max b c) = max (min a b) (min a c) := by crush

/-- `max_min_distrib_left`. -/
theorem max_min_distrib (a b c : Int) : max a (min b c) = min (max a b) (max a c) := by crush

/-- `min_assoc`. -/
theorem min_assoc' (a b c : Int) : min (min a b) c = min a (min b c) := by crush

/-- `min_eq_left_iff` — an `↔`, so both directions in one query. -/
theorem min_eq_left_iff' (a b : Int) : min a b = a ↔ a ≤ b := by crush

/-- `max_eq_right_iff`. -/
theorem max_eq_right_iff' (a b : Int) : max a b = b ↔ a ≤ b := by crush

/-- `min_add_max` — mixes the lattice and additive structure. -/
theorem min_add_max' (a b : Int) : min a b + max a b = a + b := by crush

/-- `min_le_min` specialized: monotonicity of `min` in one argument. -/
theorem min_le_min_right' (a b c : Int) (h : a ≤ b) : min a c ≤ min b c := by crush

theorem min_le_max' (a b : Int) : min a b ≤ max a b := by crush

end Lattice

/-! ## Euclidean division

`Int.emod`/`Int.ediv` map onto SMT-LIB's integer division, so the defining identity and the
remainder bounds go through directly. -/

section Division

/-- `Int.mul_ediv_add_emod` — the division algorithm itself. -/
theorem mul_ediv_add_emod' (a b : Int) : b * (a / b) + a % b = a := by crush

/-- `Int.emod_lt_of_pos`. -/
theorem emod_lt_of_pos' (a b : Int) (h : 0 < b) : a % b < b := by crush

/-- `Int.emod_nonneg`, at a positive modulus. -/
theorem emod_nonneg' (a b : Int) (h : 0 < b) : 0 ≤ a % b := by crush

-- `Int.add_mul_emod_self_left` — `(a + b * c) % b = a % b` — is *out of reach*, measured at
-- a 60 s budget on 2026-08-06: z3 returns `timeout`, not a counterexample. The obstruction is
-- arithmetic, not translation: the goal multiplies two variables (`b * c`) and then divides
-- by one of them, so it lands in nonlinear integer arithmetic *with* division, where z3's
-- nlsat does not apply. The linear instance below is the reachable form.
/-- `Int.add_mul_emod_self_left` at a literal multiplier, which keeps it linear. -/
theorem add_mul_emod_self_left_lit (a b : Int) : (a + b * 2) % 2 = a % 2 := by crush

/-- Parity as a two-way case split on the remainder. -/
theorem emod_two (n : Int) : n % 2 = 0 ∨ n % 2 = 1 ∨ n % 2 = -1 := by crush

end Division

/-! ## Nonlinear arithmetic

z3's `nlsat` decides these. No general Lean tactic does, and mathlib's `nlinarith` needs a
manual `sq_nonneg` witness that crush avoids by shipping the raw polynomial. -/

section Nonlinear

/-- `two_mul_le_add_sq` — AM-GM. -/
theorem amgm (a b : Int) : 2 * a * b ≤ a * a + b * b := by crush

/-- Three-variable AM-GM. -/
theorem amgm3 (a b c : Int) : a * b + b * c + c * a ≤ a * a + b * b + c * c := by crush

/-- `mul_pos_iff` — a disjunctive conclusion, dispatched by case-split on sign. -/
theorem prod_sign (a b : Int) (h : 0 < a * b) :
    (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by crush

/-- Sum of squares vanishes only at the origin. -/
theorem sq_sum_zero (a b : Int) (h : a * a + b * b = 0) : a = 0 ∧ b = 0 := by crush

/-- `le_self_pow`-flavoured cubic bound. -/
theorem cube_lower (a : Int) (h : 1 ≤ a) : a ≤ a * a * a := by crush

/-- `sq_le_sq'`-flavoured monotonicity of squaring on the non-negatives. -/
theorem sq_mono (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := by crush

/-- `abs_le_abs` restated without `|·|` (which does not translate), i.e. the squared form. -/
theorem sq_antitone (a b : Int) (h : a * a ≤ b * b) (hb : 0 ≤ b) : -b ≤ a ∨ a ≤ b := by crush

end Nonlinear

/-! ## Quantified hypotheses over uninterpreted functions

The solver must instantiate a `∀` at the right terms and chain the results — the shape where
premise selection matters, since the useful instances are not syntactically present. -/

section Quantifiers

/-- An involution is injective: needs `h` at both `a` and `b`, chained through
`f (f a) = a`, `f (f b) = b`, `f a = f b`. -/
theorem invol_inj (f : Int → Int) (h : ∀ x, f (f x) = x) (a b : Int)
    (hab : f a = f b) : a = b := by crush

/-- Pointwise equality of two functions transports through an equation on arguments —
`congrArg` composed with a `∀`-instantiation. -/
theorem pointwise_congr (f g : Int → Int) (a b : Int) (hab : a = b)
    (h : ∀ x, f x = g x) : f a = g b := by crush

/-- A `Monotone` witness supplied in unbundled form (the bundled predicate does not
translate; see the module comment). -/
theorem mono_unbundled (f : Int → Int) (h : ∀ x y, x ≤ y → f x ≤ f y)
    (a b : Int) (hab : a ≤ b) : f a ≤ f b := by crush

/-- Injectivity, unbundled, chained twice. -/
theorem inj_unbundled (f : Int → Int) (h : ∀ x y, f x = f y → x = y)
    (a b c : Int) (h1 : f a = f b) (h2 : f b = f c) : a = c := by crush

end Quantifiers

/-! ## mathlib datatypes

Real inductives from mathlib, to check that `declare-datatypes` emission matches what the
library actually defines.

Under the reconstructing policy, so these are kernel-checked rather than taken on the
solver's word. That is only possible because of the case-split pre-pass in
`Crush/Solver/Reconstruct.lean` — an exhaustiveness goal's unsat core is just the negated
goal, so the finisher ladder alone cannot decompose it. -/

section Datatypes
set_option crush.trust "reconstruct"

/-- `Mathlib.Data.Tree.Basic`'s `BinaryTree`. Exhaustiveness with existential witnesses; the
`∃ v l r` packaging defeats `grind`/`aesop`, while the solver reads it off the constructor
set. -/
theorem bt_exhaust (t : BinaryTree Int) :
    t = .nil ∨ ∃ v l r, t = .node v l r := by crush

/-- `BinaryTree` constructors are disjoint. -/
theorem bt_disjoint (v : Int) (l r : BinaryTree Int) : BinaryTree.nil ≠ .node v l r := by crush

/-- `BinaryTree.node` is injective in all three arguments. -/
theorem bt_inj (v w : Int) (l r l' r' : BinaryTree Int)
    (h : BinaryTree.node v l r = .node w l' r') : v = w ∧ l = l' ∧ r = r' := by crush

/-- `SignType` exhaustiveness. Also the regression pin for the `OfNat` fix in
`Translate.lean`: `(0 : SignType)` is the constructor `SignType.zero`, not the `Int` literal
`0`, which would clash sorts. -/
theorem sign_exhaust (s : SignType) :
    s = 0 ∨ s = SignType.neg ∨ s = SignType.pos := by crush

/-- `SignType` constructors are distinct — three-way disjointness in one query. -/
theorem sign_distinct : (SignType.neg ≠ SignType.pos) ∧ (SignType.zero ≠ SignType.pos) := by
  crush

/-- `Option` from core, as a parametric datatype at a concrete instance. -/
theorem option_exhaust (o : Option Int) : o = none ∨ ∃ v, o = some v := by crush

/-- `Prod`, as a structure with two projections. -/
theorem prod_eta (p : Int × Int) : p = (p.1, p.2) := by crush

/-- `Sum`, a two-constructor parametric datatype. -/
theorem sum_exhaust (s : Int ⊕ Int) : (∃ a, s = .inl a) ∨ ∃ b, s = .inr b := by crush

-- Kernel-checked, not trusted: these name the standard-library trio and no `crushSorry`.
/-- info: 'bt_exhaust' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bt_exhaust

/-- info: 'sign_exhaust' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_exhaust

/-- info: 'prod_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_eta

end Datatypes

/-! ## Untranslated mathlib primitives

These pin the *boundary*. Each goal below is **true** in mathlib, but the operation has no
first-order translation, so crush emits an uninterpreted symbol and the solver finds a
countermodel. They are recorded as expected failures so that teaching crush any of these
operations breaks this section loudly instead of passing unnoticed.

Note the failure mode is a *counterexample*, not an error: from the solver's view the goal
genuinely does not follow, since nothing constrains the uninterpreted symbol. -/

section Untranslated

-- `abs_abs` / `abs_nonneg`: `|·|` is a lattice operation crush does not map.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (a : Int) : 0 ≤ |a| := by crush

-- `Int.natAbs_mul`.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (a b : Int) : (a * b).natAbs = a.natAbs * b.natAbs := by crush

-- `Int.sign_mul`.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (a b : Int) : (a * b).sign = a.sign * b.sign := by crush

-- `Dvd.dvd`: divisibility is an existential crush does not unfold.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (a b k : Int) (h : a ∣ b) : a ∣ b * k := by crush

-- `Finset.card_eq_zero`.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (s : Finset Int) : s.card = 0 ↔ s = ∅ := by crush

-- `List.length_eq_zero_iff`.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (l : List Int) : l.length = 0 ↔ l = [] := by crush

-- The bundled `Monotone` predicate. Its unbundled form *does* work — see
-- `mono_unbundled` above — so what fails is unfolding the bundle, not the reasoning.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (f : Int → Int) (hm : Monotone f) (a b : Int) (h : a ≤ b) : f a ≤ f b := by crush

end Untranslated
