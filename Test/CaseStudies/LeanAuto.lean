import Crush

/-!
# Case study: lean-auto's harder test corpus, ported to `crush`

`Test/LeanAutoPort.lean` ports lean-auto's `SmtTranslation/{BoolNatInt,BitVec,String}`
and the easy `Inductive` cases. This file is the **case study for the harder
material** — the goals that were *not* already covered: the mutually-recursive and
single-constructor datatypes from `SmtTranslation/Inductive.lean`, the higher-order
Church-numeral and polymorphic goals from `Test_Regression.lean`, and the Paxos
consensus goal from `SmtTranslation/Names.lean`.

The point of a case study is an honest coverage map, so each goal is filed under
one of three headings and the reason is stated:

* **Handled** — a real `theorem`/`example` that `crush` discharges. These are the
  positive coverage claims.
* **Sound refusal** — a goal that is *true in Lean* but that `crush` declines
  (reports a counterexample or `unknown`) rather than close, because its faithful
  SMT image is out of reach of the first-order defunctionalized encoding. Pinned
  with `#guard_msgs` so a regression that starts *closing* one (which would only be
  possible via an unsound encoding) fails the build. Declining is the correct
  behaviour under the `reconstruct`/`trust` contract; a hammer is allowed to be
  incomplete, never unsound.
* **Known gap** — a goal `crush` cannot yet handle, with the emitted-SMT diagnosis
  in a comment. These drive the roadmap; see `Doc/PLAN.md` §10.

Ports run under `crush.trust "trust"` to measure *translation + solving* coverage
in isolation (matching `LeanAutoPort.lean`), not reconstruction — that is
`Test/Reconstruct.lean`'s job. `auto`'s `d[f]` maps to `crush`'s `u[f]`; lean-auto's
`autoImplicit on` becomes explicit `{α : Type}` binders here.
-/

open Crush

set_option crush.trust "trust"
set_option crush.timeout 15

/-! ## Handled: mutually-recursive datatypes (`Inductive.lean` `tree`/`treelist`)

lean-auto's `Inductive.lean` includes a mutual `tree`/`treelist` block; its comment
notes "**Nat** in inductive datatype constructors not properly treated". `crush`
emits the whole mutual block as one grouped `declare-datatypes` — both sorts in
scope at once, and every `wf_T` predicate declared before any axiom references a
sibling's — so these discharge. (This was itself a `crush` bug the case study
surfaced: each member used to be emitted as its own `declare-datatypes`, so
`tree`'s selector referenced `treelist` before it was declared and z3 rejected the
script. Fixed in `Crush/Translation/Translate.lean`, `declareDatatype`.) -/

mutual
  inductive Tree where
    | leaf : Nat → Tree
    | node : TreeList → Tree
  inductive TreeList where
    | nil : TreeList
    | cons : Tree → TreeList → TreeList
end

example (x : Tree) : (∃ (y : TreeList), x = .node y) ∨ (∃ y, x = .leaf y) := by crush

-- The `TreeList` view of the same block, to exercise the sibling-`wf` ordering
-- from the other entry point.
example (l : TreeList) : l = .nil ∨ ∃ t r, l = .cons t r := by crush

/-! ## Handled: single-constructor non-`structure` inductive (`Inductive.lean` `IndCtor₁`)

`Inductive.lean` flags this "**TODO:** Inductive types with one constructor and not
declared as `structure`". `crush` treats any supported inductive uniformly (one SMT
constructor per Lean constructor), so the single-ctor case needs no special path. -/

inductive IndCtor₁ where
  | ctor : Nat → Bool → IndCtor₁

example (f : Nat → Nat → Bool → IndCtor₁)
    (h₁ : IndCtor₁.ctor = f 1) (h₂ : IndCtor₁.ctor = f 2) : f 1 = f 2 := by
  crush [h₁, h₂]

/-! ## Handled: non-recursive datatypes (`Inductive.lean` `NonRecursive`) -/

example {α : Type} (x y : α) (_ : Option.some x = Option.some y) : x = y := by crush
example {α β : Type} (x : α × β) : x = (Prod.fst x, Prod.snd x) := by crush
example {α β : Type} (f : α × β → α) (h : f = Prod.fst) (a : α) (b : β) :
    f (a, b) = a := by crush

/-! ## Handled: higher-order with a *ground* function space (`Test_Regression.lean`)

The Church-numeral goals over an abstract `{α : Sort u}` are a known gap (below), but
the surrounding HO goals over a concrete function type go through the
defunctionalization path: λ-equalities, and quantified facts about an uninterpreted
higher-order `add`. -/

example (H : (fun x : Nat => x) = (fun x => x)) : True := by crush [H]
example (H : (fun (x y z t : Nat) => x) = (fun x y z t => x)) : True := by crush [H]

example
    (add : ((Int → Int) → (Int → Int)) → ((Int → Int) → (Int → Int)) →
           ((Int → Int) → (Int → Int)))
    (hadd : ∀ x y f n, add x y f n = (x f) ((y f) n))
    (w₁ w₂ : ((Int → Int) → (Int → Int)) → ((Int → Int) → (Int → Int)) →
             ((Int → Int) → (Int → Int)))
    (Hw : (w₁ = w₂) = (w₂ = w₁)) : True := by crush [hadd, Hw]

/-! ## Handled: leading propositional ∀-quantifiers (`Test_Regression.lean`)

"Matching with leading propositional ∀ quantifiers" and "One LemmaInst match
multiple ConstInst": the hypotheses quantify over a *type* and a `List` of it, and
the goal instantiates them. Monomorphization specializes each `p α`/`q β` at the
types in play; the residual is first-order UF. -/

example {A : Type} {x : List A} {q : Prop}
    (p : ∀ (α : Type), List α → Prop)
    (h1 : ∀ α x, p α x → q)
    (h2 : p A x) : q := by crush [h1, h2]

example {A B : Type} {x : List A} {y : List B} {r : Prop}
    (p q : ∀ (α : Type), List α → Prop)
    (h1 : ∀ α β x y, p α x → q β y → r)
    (h2 : p A x)
    (h3 : q B y) : r := by crush [h1, h2, h3]

example {A B : Type} {x : List A} {y : List B}
    (p1 p2 : ∀ (α : Type), List α → Prop)
    (h1 : ∀ α β x y, p1 α x → p2 β y)
    (h2 : p1 A x) : p2 B y := by crush [h1, h2]

/-! ## Handled: polymorphic `List.append` associativity with a ground element type

`Test_Regression.lean`'s "Polymorphic Constant" section. Lemma-instantiation
monomorphization specializes `List.append_assoc`/`map_append` at the element type. -/

example {β : Type} (as bs cs ds : List β) :
    (as ++ bs) ++ (cs ++ ds) = as ++ (bs ++ (cs ++ ds)) := by
  crush [List.append_assoc]

example {α β : Type} (as bs cs : List α) (f : α → β) :
    ((as ++ bs) ++ cs).map f = as.map f ++ (bs.map f ++ cs.map f) := by
  crush [List.append_assoc, List.map_append]

/-! ## Handled: polymorphic *free-variable* `ap`, element type fixed by the goal

`Test_Regression.lean`'s "Polymorphic free variable". When the element type is a
goal parameter (`{α : Type}`, so a single opaque sort), the uninterpreted `ap` and
its associativity axiom are first-order and the goal closes. Contrast the *type-
binding-in-the-hypothesis* form in the Known Gaps section, which does not. -/

example {α : Type} (as bs cs ds : List α)
    (ap : List α → List α → List α)
    (ap_assoc : ∀ (as bs cs : List α), ap (ap as bs) cs = ap as (ap bs cs)) :
    ap (ap as bs) (ap cs ds) = ap as (ap bs (ap cs ds)) := by
  crush [ap_assoc]

/-! ## Handled: function composition via `Function.comp_def` (`Test_Regression.lean`)

`P ((g ∘ h) ∘ f) = P (fun x => g (h (f x)))`. `(g ∘ h) ∘ f` *is* `fun x => g (h (f
x))`, so `P` of defeq arguments is equal; `Function.comp_def` supplies the rewrite.
This exercises the whole hint→monomorphize→defunctionalize path: the polymorphic
`comp_def` is specialized at the goal's element types, and the composed λs become
closures the solver equates through their defining `app` axioms. It closes under the
default `reconstruct` policy, so the composition equality is a kernel-checked proof.

Note it needs the two monomorphization refinements this case study drove (see the
Coverage-Gaps section below): elaborated polymorphic hints are re-abstracted so
their leading type binder survives, and monomorphization candidates are restricted
to genuine data sorts so `comp_def`'s `Sort` binders are not instantiated at the
`Prop` its predicate returns. -/

example {α β γ : Type}
    (P : (α → γ) → Prop) (f : α → β) (g : β → γ) (h : β → β) :
    P ((g ∘ h) ∘ f) = P (fun x => g (h (f x))) := by
  crush [Function.comp_def]

/-! ## Sound refusal: `Option.orElse` with a λ (`Inductive.lean`)

`Inductive.lean` flags this "**TODO**: Requires higher-order to first-order
translation". `Option.orElse x (fun _ => none) = x` is *true* in Lean, but the
encoding leaves `orElse` an uninterpreted function over the closure `fun _ => none`,
with no axiom relating `orElse a (const none)` to `a` — that identity is `orElse`'s
*definition*, which is not unfolded here. The solver finds a model where they
differ and `crush` reports a counterexample rather than close. Declining is sound;
lean-auto's own comment marks this a translation gap too. (Unfolding `Option.orElse`
via `u[Option.orElse]` would supply the missing equation — this pins the *bare*
behaviour, matching lean-auto's `auto` with no `d[…]`.) -/

/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example {α : Type} (x : Option α) :
    Option.orElse x (fun _ => Option.none) = x := by crush

/-! ## Known gap: the Paxos consensus goal (`SmtTranslation/Names.lean`)

lean-auto's largest single SMT goal — a Paxos safety obligation with `TotalOrder`
and `Quorum` typeclasses, six-level quantifier nesting, and higher-order state
updates encoded as function equalities (`st'_one_b = fun x x_1 => …`). It
*translates* cleanly (the state functions are uninterpreted, the class methods are
uninterpreted predicates, and the `fun`-valued equalities defunctionalize), but the
resulting query has ≈60 universal and 14 existential quantifiers in deep
alternation, and neither backend closes it: z3 spins past 60 s, cvc5 returns
`unknown` in 60 ms (it will not certify a model over the quantifiers). lean-auto
discharges it because its pipeline emits SMT `trigger` annotations that steer
E-matching (`SmtTranslation/Trigger.lean`); `crush` has no trigger or
premise-selection support yet, so a query this quantifier-heavy is out of reach.
Tracked in `Doc/PLAN.md` §10. The full statement is preserved (commented) so it can
be re-run once triggers land; `set_option crush.timeout` higher to try z3 directly.

```lean
theorem extracted_paxos_goal {node : Type} [DecidableEq node] {value : Type}
    [DecidableEq value] {quorum : Type} [Quorum node quorum]
    {round : Type} [DecidableEq round] [TotalOrder round] … :
    ∃ n r3 rmax v, Quorum.member n q = true ∧ … := by
  crush [hnext, hinv, h]   -- z3: > 60 s; cvc5: unknown
```
-/

/-! ## Known gap: higher-order over an abstract function space (`Test_Regression.lean`)

The full Church-numeral goal — `mul three (add two (add three three)) = …` over an
abstract `{α : Sort u}`. The defunctionalized `app` symbol is flattened over the
*fully applied* argument list of an arrow sort, e.g. `((α→α)→(α→α))` gets an
arity-3 `app_Fn (Fn (α→α) α) → α`. But a Church numeral applies such a value to a
*single* argument and leaves a function-typed result — a partial application of
`app`, which SMT-LIB (first-order) forbids: z3 rejects the script with
`unknown constant app_Fn_… (Fn Fn)`. Handling this needs either a per-arrow-level
unary `app` (the combinator encoding, `crush.ho.mode combinators`, not yet built)
or `native` HO. Tracked in `Doc/PLAN.md` §10. Left commented so the suite stays
green; uncomment under `crush.ho.mode combinators` once that lands.

```lean
example
    {A : Sort u}
    (add : ∀ {α}, ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
    (hadd : ∀ {α} x y f n, @add α x y f n = (x f) ((y f) n))
    (mul : ∀ {α}, ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
    (hmul : ∀ {α} x y f, @mul α x y f = x (y f))
    (two : (A → A) → (A → A)) (htwo : ∀ f x, two f x = f (f x))
    (three : (A → A) → (A → A)) (hthree : ∀ f x, three f x = f (f (f x))) :
    mul three (add two (add three three)) = mul three (mul two (add two two)) := by
  crush [hadd, hmul, htwo, hthree]
```
-/
