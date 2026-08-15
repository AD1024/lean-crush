import Crush

/-!
Rigorous stress tests for datatype monomorphization: recursive parametric `Tree`, a
finite-set `FSet`, and an association `Map` (parametric in *two* type arguments),
then the same types combined with higher-order functions.

These go well beyond `Test/Monomorphize.lean`'s `Option`/`Prod`/`List` by using
user-defined recursive parametric types, two-parameter types, and HO arguments over
them — the combination most likely to expose a gap.
-/

open Crush

set_option crush.trust "trust"

/-! ## A recursive parametric `Tree` -/

inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (v : α) (r : Tree α)

-- Injectivity of `node` in all three fields at a concrete instantiation.
theorem tree_node_inj (l₁ l₂ r₁ r₂ : Tree Int) (a b : Int)
    (h : Tree.node l₁ a r₁ = Tree.node l₂ b r₂) : l₁ = l₂ ∧ a = b ∧ r₁ = r₂ := by
  crush

-- Distinctness: a `node` is never a `leaf`.
theorem tree_distinct (l r : Tree Int) (a : Int) : Tree.node l a r ≠ Tree.leaf := by
  crush

-- Distinct instantiations coexist: `Tree Int` and `Tree Bool` in one query.
theorem tree_two_inst (a b : Int) (p q : Bool)
    (h1 : (Tree.node .leaf a .leaf : Tree Int) = Tree.node .leaf b .leaf)
    (h2 : (Tree.node .leaf p .leaf : Tree Bool) = Tree.node .leaf q .leaf) :
    a = b ∧ p = q := by crush

/-! ## A two-parameter association `Map` (list of key/value pairs) -/

inductive Map (κ : Type) (ν : Type) where
  | empty
  | cons (k : κ) (v : ν) (rest : Map κ ν)

theorem map_cons_inj (k₁ k₂ : Int) (v₁ v₂ : Bool) (r₁ r₂ : Map Int Bool)
    (h : Map.cons k₁ v₁ r₁ = Map.cons k₂ v₂ r₂) :
    k₁ = k₂ ∧ v₁ = v₂ ∧ r₁ = r₂ := by crush

theorem map_distinct (k : Int) (v : Bool) (r : Map Int Bool) :
    Map.cons k v r ≠ Map.empty := by crush

/-! ## A finite `FSet` built on `List`, mixing two parametric datatypes -/

-- `FSet α` wraps a `List α`; nesting a parametric type inside another.
structure FSet (α : Type) where
  elems : List α

theorem fset_eq (xs ys : List Int) (h : xs = ys) :
    FSet.mk xs = FSet.mk ys := by crush

theorem fset_proj (xs : List Int) : (FSet.mk xs).elems = xs := by crush

/-! ## Nat through a parameter still guarded (soundness)

`Tree Nat` freely generated over `Int` (the `Nat` encoding) would admit negative node
values with no Lean counterpart. The monomorphizer composes the `≥0` guard through the
type parameter, so the phantom values are excluded — the point being that a *true*
hypothesis about the field must not collapse to `False`.

`Tree` is **recursive** *and* has a guarded `Nat` field. Its `wf_Tree` predicate is
emitted with `define-fun-rec`, not as a quantified defining axiom, so z3 can now find
the expected countermodel without an instantiation loop. -/

set_option crush.timeout 3 in
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem tree_nat_recursive_wf_rejects_false
    (h : ∀ t : Tree Nat, ∀ l r n, t = Tree.node l n r → n ≥ 0) : False := by crush

/-- A **non-recursive** parametric type with a `Nat` field guards cleanly and without
divergence, so a genuinely false goal is *refuted with a countermodel*. `Pair Nat` has
no recursive `wf` axiom. The goal `∀ p, p.fst = 0` is false (a `Pair` with `fst = 1`
witnesses it), so it must be rejected — and the reason it *can* be rejected here but
not for `Tree Nat` above isolates the divergence to recursion, confirming the guard
itself is sound and effective. -/
structure Pair (α : Type) where
  fst : α
  snd : α

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_pair_nat : ∀ p : Pair Nat, p.fst = 0 := by crush

/-- And a *true* guarded fact through the non-recursive parametric type goes through:
`p.fst`, being `Nat`, is non-negative. -/
theorem pair_nat_field_nonneg : ∀ p : Pair Nat, p.fst ≥ 0 := by crush

/-! ## Monomorphized datatypes meet higher-order functions

The interesting combination: function-typed arguments and quantifiers whose domain or
codomain is a monomorphized parametric datatype. These route through the
defunctionalization layer (`Fn` sorts + `app`) *and* the datatype machinery at once. -/

-- A function *from* a monomorphized datatype: congruence of an uninterpreted
-- `f : Tree Int → Int` applied to equal trees.
theorem ho_fn_from_tree (f : Tree Int → Int) (t₁ t₂ : Tree Int) (h : t₁ = t₂) :
    f t₁ = f t₂ := by crush

-- A function *to* a monomorphized datatype: `g : Int → Tree Int`, congruence.
theorem ho_fn_to_tree (g : Int → Tree Int) (a b : Int) (h : a = b) :
    g a = g b := by crush

-- A λ-argument applied to a datatype value: the closure's defining axiom fires, and
-- the result is a `Tree Int` compared for equality.
theorem ho_lambda_over_tree (apply : (Tree Int → Tree Int) → Tree Int → Tree Int)
    (t : Tree Int) (h : ∀ f x, apply f x = f x) :
    apply (fun z => z) t = t := by crush

-- A higher-order hypothesis quantifying over a function into a datatype, instantiated
-- at a concrete closure — the shape that was the original HO unsoundness, now over a
-- parametric type.
theorem ho_forall_fn_datatype
    (G : (Int → Tree Int) → Tree Int) (h : ∀ f : Int → Tree Int, G f = f 0) :
    G (fun _ => Tree.leaf) = Tree.leaf := by crush

-- Map with a function-typed value column: `Map Int (Int → Int)`. The value field is a
-- function, so this type is *not* a supported datatype (function-typed field) and must
-- degrade gracefully to an opaque encoding rather than crash — congruence still holds.
theorem ho_map_fn_value (k : Int) (f g : Int → Int) (r : Map Int (Int → Int))
    (h : f = g) : Map.cons k f r = Map.cons k g r := by crush

-- A function returning a two-parameter datatype, mixing HO with the `Map` sort.
theorem ho_fn_to_map (mk : Int → Map Int Bool) (a b : Int) (h : a = b) :
    mk a = mk b := by crush
