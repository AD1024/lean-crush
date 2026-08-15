import Crush

/-!
Recursive functions, recursive types, and nested data structures — the goals where a hammer
usually stops being useful, because the argument needs a definition unfolded at a specific
depth rather than a single decision procedure.

The pattern throughout: `@[crush_unfold]` puts a function's equations into every query, so
the solver gets `size (node l v r) = 1 + size l + size r` as an axiom and can chain it.
crush does not do induction, so anything needing a hypothesis about *all* smaller values is
driven by an explicit `induction`, with crush closing each case.

Everything here runs under the *reconstructing* policy, so each theorem is a kernel-checked
Lean proof rather than the solver's word — the `#print axioms` pins at the end of each
section make that observable. That matters more here than in the arithmetic suites: these
goals lean on the datatype and unfolding machinery, where a translation bug would be easiest
to hide.
-/

open Crush

set_option crush.timeout 25
set_option crush.trust "reconstruct"

/-! ## An expression language: 5 constructors, mutual structure

`Expr` is the shape that shows up in every compiler proof. Five constructors means
exhaustiveness and disjointness are real case splits, not two-way ones. -/

namespace ExprLang

inductive Expr where
  | lit (n : Int)
  | var (s : String)
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  deriving Repr

@[crush_unfold]
def Expr.size : Expr → Int
  | .lit _ => 1
  | .var _ => 1
  | .add a b => 1 + a.size + b.size
  | .mul a b => 1 + a.size + b.size
  | .neg a => 1 + a.size

@[crush_unfold]
def Expr.depth : Expr → Int
  | .lit _ => 1
  | .var _ => 1
  | .add a b => 1 + max a.depth b.depth
  | .mul a b => 1 + max a.depth b.depth
  | .neg a => 1 + a.depth

/-- One unfolding step, in the solver rather than by `rfl`. -/
theorem size_add (a b : Expr) : (Expr.add a b).size = 1 + a.size + b.size := by crush

/-- Two nested unfoldings composed. -/
theorem size_neg_neg (a : Expr) : (Expr.neg (Expr.neg a)).size = 2 + a.size := by crush

/-- Three levels deep: the solver must chain the equation at three different arguments. -/
theorem size_nested (a b c : Expr) :
    (Expr.add (Expr.mul a b) (Expr.neg c)).size = 3 + a.size + b.size + c.size := by crush

/-- A lower bound on every expression. This *does* need induction, despite every equation's
right side being visibly ≥ 1: the recursive cases mention `a.size` as an opaque term, so
without a hypothesis about it the solver cannot conclude anything (measured — the bare
`crush` times out rather than failing fast). -/
theorem size_pos (e : Expr) : 1 ≤ e.size := by
  induction e with
  | lit n => crush
  | var s => crush
  | add a b iha ihb => crush [iha, ihb]
  | mul a b iha ihb => crush [iha, ihb]
  | neg a iha => crush [iha]

/-- Injectivity of a two-argument constructor, both components at once. -/
theorem add_inj (a b c d : Expr) (h : Expr.add a b = Expr.add c d) : a = c ∧ b = d := by crush

/-- Constructors of different shapes are disjoint. -/
theorem lit_ne_add (n : Int) (a b : Expr) : Expr.lit n ≠ Expr.add a b := by crush

/-- Disjointness *derived through a function*: `size = 1` rules out the compound
constructors. Each compound case is a crush query that needs the subterms' positivity
supplied as a hint — the interesting part, since the solver must combine two supplied facts
with the unfolded equation to derive a contradiction. -/
theorem size_one_is_atom (e : Expr) (h : e.size = 1) :
    (∃ n, e = .lit n) ∨ (∃ s, e = .var s) := by
  cases e with
  | lit n => exact Or.inl ⟨n, rfl⟩
  | var s => exact Or.inr ⟨s, rfl⟩
  | add a b => exact absurd h (by crush [size_pos a, size_pos b])
  | mul a b => exact absurd h (by crush [size_pos a, size_pos b])
  | neg a => exact absurd h (by crush [size_pos a])

/-- `depth` mixes recursion with the `max` lattice operation. -/
theorem depth_add (a b : Expr) : (Expr.add a b).depth = 1 + max a.depth b.depth := by crush

/-- Depth is bounded by size — for expressions of bounded shape. The general statement needs
induction (below); this instance is pure equation-chaining. -/
theorem depth_le_size_lit (n : Int) : (Expr.lit n).depth ≤ (Expr.lit n).size := by crush

/-- info: 'ExprLang.size_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms size_nested

/-- Five-way exhaustiveness with existential witnesses. The `∃` packaging puts this out of
`grind`/`aesop`'s single-shot reach, and the solver gets it from the `declare-datatypes`
constructor set.

Reconstruction needs the case-split pre-pass in `Crush/Solver/Reconstruct.lean`: the unsat
core here is just the negated goal, so the ladder is handed the whole problem, and no *fixed*
tactic string can supply the missing step, which is `cases e` on a variable whose name the
string cannot know. Splitting first and then running the ladder per branch closes it. -/
theorem exhaust (e : Expr) :
    (∃ n, e = .lit n) ∨ (∃ s, e = .var s) ∨ (∃ a b, e = .add a b)
      ∨ (∃ a b, e = .mul a b) ∨ (∃ a, e = .neg a) := by crush

/-- info: 'ExprLang.exhaust' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exhaust

/-! ### Evaluation: a recursive function into a second recursive argument

`eval` takes an environment, so its equations are quantified over *two* things. This is
where a first-order encoding usually starts to strain. -/

@[crush_unfold]
def Expr.eval (env : String → Int) : Expr → Int
  | .lit n => n
  | .var s => env s
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => -(a.eval env)

theorem eval_lit (env : String → Int) (n : Int) : (Expr.lit n).eval env = n := by crush

theorem eval_add (env : String → Int) (a b : Expr) :
    (Expr.add a b).eval env = a.eval env + b.eval env := by crush

/-- Double negation is the identity on values — an algebraic fact about the interpreter. -/
theorem eval_neg_neg (env : String → Int) (a : Expr) :
    (Expr.neg (Expr.neg a)).eval env = a.eval env := by crush

/-- Adding a literal zero does not change the value: the optimizer's soundness obligation,
one rewrite deep. -/
theorem eval_add_zero (env : String → Int) (a : Expr) :
    (Expr.add a (Expr.lit 0)).eval env = a.eval env := by crush

/-- Multiplying by a literal one, likewise. -/
theorem eval_mul_one (env : String → Int) (a : Expr) :
    (Expr.mul a (Expr.lit 1)).eval env = a.eval env := by crush

/-- Commutativity of `add` under evaluation, at a fixed environment. -/
theorem eval_add_comm (env : String → Int) (a b : Expr) :
    (Expr.add a b).eval env = (Expr.add b a).eval env := by crush

/-- Associativity, three levels of unfolding on both sides. -/
theorem eval_add_assoc (env : String → Int) (a b c : Expr) :
    (Expr.add (Expr.add a b) c).eval env = (Expr.add a (Expr.add b c)).eval env := by crush

/-- Distribution: `a * (b + c) = a * b + a * c` under evaluation. Nonlinear, and the two
sides unfold to structurally different terms. -/
theorem eval_distrib (env : String → Int) (a b c : Expr) :
    (Expr.mul a (Expr.add b c)).eval env
      = (Expr.add (Expr.mul a b) (Expr.mul a c)).eval env := by crush

/-- info: 'ExprLang.eval_distrib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_distrib

end ExprLang

/-! ## Binary trees: structural induction with crush closing the cases

These need a hypothesis about subtrees, so `induction` supplies it and crush does the
algebra. The interesting part is that the inductive hypotheses go in as *hints*, and the
solver has to combine them with the unfolded equations. -/

namespace Trees

inductive Tree where
  | leaf
  | node (l : Tree) (v : Int) (r : Tree)

@[crush_unfold]
def Tree.size : Tree → Int
  | .leaf => 0
  | .node l _ r => 1 + l.size + r.size

@[crush_unfold]
def Tree.sum : Tree → Int
  | .leaf => 0
  | .node l v r => l.sum + v + r.sum

@[crush_unfold]
def Tree.mirror : Tree → Tree
  | .leaf => .leaf
  | .node l v r => .node r.mirror v l.mirror

@[crush_unfold]
def Tree.height : Tree → Int
  | .leaf => 0
  | .node l _ r => 1 + max l.height r.height

/-- Mirroring preserves size. Both inductive hypotheses are needed, and the solver must see
that `mirror` swaps the two subtree sizes. -/
theorem size_mirror (t : Tree) : t.mirror.size = t.size := by
  induction t with
  | leaf => crush
  | node l v r ihl ihr => crush [ihl, ihr]

/-- Mirroring preserves the sum, likewise. -/
theorem sum_mirror (t : Tree) : t.mirror.sum = t.sum := by
  induction t with
  | leaf => crush
  | node l v r ihl ihr => crush [ihl, ihr]

/-- Mirroring is an involution — an equation between *trees*, not numbers, so the solver
works in the datatype rather than in arithmetic. -/
theorem mirror_mirror (t : Tree) : t.mirror.mirror = t := by
  induction t with
  | leaf => crush
  | node l v r ihl ihr => crush [ihl, ihr]

/-- Size is non-negative. -/
theorem size_nonneg (t : Tree) : 0 ≤ t.size := by
  induction t with
  | leaf => crush
  | node l v r ihl ihr => crush [ihl, ihr]

/-- Mirroring preserves height, which mixes induction with `max`. -/
theorem height_mirror (t : Tree) : t.mirror.height = t.height := by
  induction t with
  | leaf => crush
  | node l v r ihl ihr => crush [ihl, ihr]

/-- Height bounds size. The inductive hypotheses alone are **not enough**, and the reason is
worth stating because the symptom is misleading: the step would be `1 + max hl hr ≤
1 + sl + sr` from `hl ≤ sl` and `hr ≤ sr`, which is simply false (`hl = sl = 0`, `hr = -10`,
`sr = -5` satisfies both premises and refutes the conclusion). The solver was searching for a
proof that does not exist, and reported a *timeout* — indistinguishable from a goal that is
merely hard.

Supplying the missing premise, `0 ≤ size`, is all it takes. -/
theorem height_le_size (t : Tree) : t.height ≤ t.size := by
  induction t with
  | leaf => crush
  | node l v r ihl ihr => crush [ihl, ihr, size_nonneg l, size_nonneg r]

/-- info: 'Trees.height_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms height_le_size

/-- A non-empty tree has positive size — the case split alone, no induction. -/
theorem node_size_pos (l : Tree) (v : Int) (r : Tree) : 1 ≤ (Tree.node l v r).size := by
  have hl : 0 ≤ l.size := size_nonneg l
  have hr : 0 ≤ r.size := size_nonneg r
  crush [hl, hr]

/-- Size zero characterizes the leaf. Uses the non-negativity lemma as a premise, so the
solver must combine a supplied fact with the equations. -/
theorem size_zero_iff (l : Tree) (v : Int) (r : Tree) : (Tree.node l v r).size ≠ 0 := by
  have hl : 0 ≤ l.size := size_nonneg l
  have hr : 0 ≤ r.size := size_nonneg r
  crush [hl, hr]

/-- Constructor injectivity across three fields. -/
theorem node_inj (l r l' r' : Tree) (v w : Int)
    (h : Tree.node l v r = Tree.node l' w r') : l = l' ∧ v = w ∧ r = r' := by crush

/-- Exhaustiveness with witnesses, reconstructed via the case-split pre-pass (see
`ExprLang.exhaust`). Note the split is on a *recursive* datatype, so `cases` exposes two more
`Tree` fields — which is why the pre-pass bounds itself by rounds rather than splitting until
nothing is left. -/
theorem exhaust (t : Tree) : t = .leaf ∨ ∃ l v r, t = .node l v r := by crush

/-- info: 'Trees.exhaust' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exhaust

/-- info: 'Trees.mirror_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mirror_mirror

/-- info: 'Trees.size_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms size_mirror

end Trees

/-! ## Nested data: a datatype whose field is a `List` of itself

`Rose` recurses *indirectly* — through `List Rose` rather than through `Rose` — and this is
the boundary of the datatype encoding. SMT-LIB requires mutually recursive datatypes to
share one `declare-datatypes` block, but `Rose` and `List` are not a Lean mutual block, so
crush would emit `List_1` (whose field mentions `Rose_0`) as its own earlier block and the
solver would reject the entire script: `unknown sort 'Rose_0'`.

Finding this cost two bug fixes, both in `Crush/Translation/Translate.lean`:

* `needsWFGuard` cycled forever on this shape. Its cycle check only skipped *direct*
  self-reference, and an indirect cycle never repeats two heads in a row, so
  `Rose → List Rose → Rose → …` recursed until the elaborator's stack overflowed (`Stack
  overflow detected. Aborting.`, no source position). It now carries a visited set.
* `isSupportedDatatypeApp` now *rejects* indirect recursion, so such a type stays an opaque
  uninterpreted sort. Less precise, but a valid query beats a script the solver refuses.

`Rose` remains opaque in SMT, but constructor-equality preprocessing now discovers
Lean's generated injectivity theorem and simplifies same-constructor hypotheses before
translation. This recovers direct injectivity without requiring mutually recursive SMT
datatype declarations. Constructor discrimination nested inside an injected field
remains unavailable.
-/

namespace Nested

inductive Rose where
  | node (v : Int) (kids : List Rose)

-- Injectivity through the nested field is discharged during preprocessing.
example (v w : Int) (ks ls : List Rose) (h : Rose.node v ks = Rose.node w ls) :
    v = w ∧ ks = ls := by crush

-- Nested `List.nil ≠ List.cons` discrimination is still hidden behind opacity.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
example (v : Int) (k : Rose) : Rose.node v [] ≠ Rose.node v [k] := by crush

/-- What *does* hold: an uninterpreted function is still a function, so congruence works —
equal arguments give equal results. This is the reasoning that survives opacity, and it
confirms the sort is being emitted rather than the query failing outright. -/
theorem rose_congr (v w : Int) (ks : List Rose) (h : v = w) :
    Rose.node v ks = Rose.node w ks := by crush

/-- info: 'Nested.rose_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rose_congr

/-! ### A structure nested inside a datatype nested inside a structure -/

structure Point where
  x : Int
  y : Int
  deriving DecidableEq

inductive Shape where
  | circle (center : Point) (r : Int)
  | rect (lo hi : Point)

@[crush_unfold]
def Shape.area2 : Shape → Int
  | .circle _ r => 3 * r * r
  | .rect lo hi => (hi.x - lo.x) * (hi.y - lo.y)

/-- Projections through two layers of nesting. -/
theorem shape_circle_inj (c d : Point) (r s : Int)
    (h : Shape.circle c r = Shape.circle d s) : c = d ∧ r = s := by crush

/-- A structure equality reduces to its fields. -/
theorem point_eta (p : Point) : p = ⟨p.x, p.y⟩ := by crush

/-- Field-wise characterization of structure equality. Going from field equalities *back* to
a structure equality is eta for structures, which no finisher performs directly; the
case-split pre-pass gets it by splitting both `p` and `q` into their constructor forms, after
which the fields are syntactically equal. This is the case needing *two* split rounds — one
per variable. -/
theorem point_eq_iff (p q : Point) : p = q ↔ p.x = q.x ∧ p.y = q.y := by crush

/-- info: 'Nested.point_eq_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms point_eq_iff

/-- One direction alone, with the fields as hypotheses. -/
theorem point_eq_of_fields (p q : Point) (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by crush

/-- info: 'Nested.point_eq_of_fields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms point_eq_of_fields

/-- Area of a unit square, computed through the nested projections. -/
theorem rect_unit_area : (Shape.rect ⟨0, 0⟩ ⟨1, 1⟩).area2 = 1 := by crush

/-- A degenerate rectangle has zero area — projection plus arithmetic. -/
theorem rect_degenerate (lo hi : Point) (h : lo.x = hi.x) :
    (Shape.rect lo hi).area2 = 0 := by crush

/-- Shape constructors are disjoint even with matching numeric content. -/
theorem shape_disjoint (p q : Point) (r : Int) : Shape.circle p r ≠ Shape.rect p q := by crush

/-- info: 'Nested.rect_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rect_degenerate

end Nested

/-! ## Recursion over `Nat` with an accumulator

Two functions computing the same thing by different recursions — the classic
"tail-recursive version is correct" obligation. The generalized inductive step is what makes
this hard, and it is supplied as a hint. -/

namespace Accum

@[crush_unfold]
def sumTo : Nat → Int
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- Base case and one step, from the equations. -/
theorem sumTo_zero : sumTo 0 = 0 := by crush

theorem sumTo_step (n : Nat) : sumTo (n + 1) = sumTo n + (n + 1) := by crush

/-- Two steps composed. -/
theorem sumTo_two_steps (n : Nat) : sumTo (n + 2) = sumTo n + (2 * n + 3) := by crush

/-- The closed form, by induction with crush doing the algebra in each case. This is the
payoff shape: the inductive step is a nonlinear identity
(`2 * sumTo n = n * (n+1)` ⟹ `2 * sumTo (n+1) = (n+1) * (n+2)`) that the solver verifies
after the hypothesis is supplied. -/
theorem sumTo_closed (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => crush
  | succ k ih => crush [ih]

/-- Monotonicity, by the same route. -/
theorem sumTo_nonneg (n : Nat) : 0 ≤ sumTo n := by
  induction n with
  | zero => crush
  | succ k ih => crush [ih]

/-- info: 'Accum.sumTo_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sumTo_closed

end Accum
