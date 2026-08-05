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
  positive coverage claims. Several started as gaps this study surfaced and were
  closed here (see `Doc/PLAN.md` §11b): the mutually-recursive datatypes, the Church
  numerals (a partial-application translation fix), and Paxos (the right cvc5 flag).
* **Sound refusal** — a goal that is *true in Lean* but that `crush` declines
  (reports a counterexample or `unknown`) rather than close, because its faithful
  SMT image is out of reach of the first-order defunctionalized encoding. Pinned
  with `#guard_msgs` so a regression that starts *closing* one (which would only be
  possible via an unsound encoding) fails the build. Declining is the correct
  behaviour under the `reconstruct`/`trust` contract; a hammer is allowed to be
  incomplete, never unsound.
* **Known gap** — a goal `crush` cannot yet handle, with the diagnosis in a comment.
  These drive the roadmap; see `Doc/PLAN.md` §10. Only one remains here: the Church
  tower over an *abstract universe* (the ground-type version is handled).

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

/-! ## `Option.orElse` with a λ (`Inductive.lean`): refused bare, closed with unfold

`Inductive.lean` flags this "**TODO**: Requires higher-order to first-order
translation". `Option.orElse x (fun _ => none) = x` is *true* in Lean, and the
outcome depends on whether `orElse`'s defining equation is available:

* **Bare** (`crush`, no unfold) — the encoding leaves `orElse` an uninterpreted
  function over the closure `fun _ => none`, with no axiom relating `orElse a (const
  none)` to `a` (that identity *is* `orElse`'s definition). The solver finds a model
  where they differ and `crush` reports a counterexample rather than close. Declining
  is sound; lean-auto's own comment marks the bare case a translation gap too.
* **With `u[Option.orElse]`** — the unfold hint supplies the missing equation and the
  goal closes. This is the intended way to discharge a definitional identity, and the
  `crush` analogue of lean-auto's `d[Option.orElse]`. -/

-- Bare: sound refusal, pinned so a regression that starts closing it (only possible
-- unsoundly) fails the build.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example {α : Type} (x : Option α) :
    Option.orElse x (fun _ => Option.none) = x := by crush

-- With the definitional equation, it closes.
example {α : Type} (x : Option α) :
    Option.orElse x (fun _ => Option.none) = x := by crush u[Option.orElse]

/-! ## Handled — and *reconstructed* — higher-order Church numerals (`Test_Regression.lean`)

The full Church-numeral tower — `mul three (add two (add three three)) = mul three
(mul two (add two two))` — over a ground function space. This was a translation gap
until this case study surfaced it: the defunctionalized `app` symbol is n-ary over an
arrow's *fully flattened* argument list, so a Church numeral applying such a value to
a *single* argument (`x (y f)`, leaving a function result) emitted `app`
under-applied — an ill-sorted term z3 rejected with `unknown constant app_Fn (Fn
Fn)`. Fixed in `hoTerm?` (`Crush/Translation/Translate.lean`): a partially-applied
function-typed bound variable is now η-expanded to a closure of the residual arrow
sort, so `x (y f)` becomes a proper `Fn` value. The script is then well-formed and z3
discharges the whole equation in ~40 ms.

It closes under the **default `reconstruct` policy** — a *kernel-checked* proof, not a
trusted verdict — so this example overrides the file's `trust` back to `reconstruct`
and `#print axioms` witnesses that `crushSorry` is absent. The verdict is a function
equality, and the reconstruction finishers now include `funext`-prefixed variants
(`Crush/Solver/Reconstruct.lean`): `funext` reduces `f = g` to the pointwise body, and
`simp_all` closes it using the core hypotheses. Higher-order equational obligations no
longer force the trust axiom. -/

theorem church_tower
    {A : Type}
    (add : ((A → A) → (A → A)) → ((A → A) → (A → A)) → ((A → A) → (A → A)))
    (hadd : ∀ x y f n, add x y f n = (x f) ((y f) n))
    (mul : ((A → A) → (A → A)) → ((A → A) → (A → A)) → ((A → A) → (A → A)))
    (hmul : ∀ x y f, mul x y f = x (y f))
    (two : (A → A) → (A → A)) (htwo : ∀ f x, two f x = f (f x))
    (three : (A → A) → (A → A)) (hthree : ∀ f x, three f x = f (f (f x))) :
    mul three (add two (add three three)) = mul three (mul two (add two two)) := by
  set_option crush.trust "reconstruct" in
  crush [hadd, hmul, htwo, hthree]

/-- info: 'church_tower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms church_tower

/-! ## Handled: the Paxos consensus goal (`SmtTranslation/Names.lean`)

lean-auto's largest single SMT goal — a Paxos safety obligation with `TotalOrder` and
`Quorum` typeclasses, six-level quantifier nesting, and higher-order state updates
encoded as function equalities (`st'_one_b = fun x x_1 => …`). It translates cleanly
(state functions uninterpreted, class methods uninterpreted predicates, `fun`-valued
equalities defunctionalized), but the query has ≈60 universal and 14 existential
quantifiers in deep alternation — z3's default E-matching spins on it, and so does
cvc5's. The key is the *solver configuration*: cvc5 with `--full-saturate-quant`
(instantiation-based quantifier handling, exposed via `crush.additionalArgs`) closes
it in ~0.2 s. That the goal was reachable at all with the right flag — not an
unfixable trigger gap — was the finding here; lean-auto reaches it via its own
`trigger` annotations (`SmtTranslation/Trigger.lean`), a different route to the same
end.

Under `crush.trust "trust"`: like the Church tower, the verdict is a heavy
quantified UF proof no core-directed finisher replays. -/

section Paxos
set_option crush.backend "cvc5"
set_option crush.additionalArgs "--full-saturate-quant"
set_option crush.timeout 30

class TotalOrder (t : Type) where
  le (x y : t) : Bool
  none : t
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

class Quorum (node : Type) (quorum : outParam Type) where
  member (a : node) (q : quorum) : Bool
  quorum_intersection :
    ∀ (q1 q2 : quorum), ∃ (a : node), member a q1 ∧ member a q2

theorem extracted_paxos_goal {node : Type} [inst : DecidableEq node] {value : Type}
    [inst_1 : DecidableEq value] {quorum : Type} [inst_2 : Quorum node quorum]
    {round : Type} [inst_3 : DecidableEq round] [inst_4 : TotalOrder round]
    (st_one_a : round → Bool) (st_one_b_max_vote : node → round → round → value → Bool)
    (st_one_b st_leftRound : node → round → Bool) (st_proposal : round → value → Bool)
    (st_vote st_decision : node → round → value → Bool)
    (hinv :
      (∀ (n1 n2 : node) (r1 r2 : round) (v1 v2 : value),
          st_decision n1 r1 v1 = true ∧ st_decision n2 r2 v2 = true → r1 = r2 ∧ v1 = v2) ∧
        (∀ (r : round) (v1 v2 : value), st_proposal r v1 = true ∧ st_proposal r v2 = true → v1 = v2) ∧
          (∀ (n : node) (r : round) (v : value), st_vote n r v = true → st_proposal r v = true) ∧
            (∀ (r : round) (v : value),
                (∃ n, st_decision n r v = true) → ∃ q, ∀ (n : node), Quorum.member n q = true → st_vote n r v = true) ∧
              (∀ (n : node) (v : value), ¬st_vote n TotalOrder.none v = true) ∧
                (∀ (r1 r2 : round) (v1 v2 : value) (q : quorum),
                    ¬TotalOrder.le r2 r1 = true ∧ st_proposal r2 v2 = true ∧ v1 ≠ v2 →
                      ∃ n r3 rmax v,
                        Quorum.member n q = true ∧
                          ¬TotalOrder.le r3 r1 = true ∧ st_one_b_max_vote n r3 rmax v = true ∧ ¬st_vote n r1 v1 = true) ∧
                  ∀ (n : node) (r1 r2 : round),
                    st_one_b n r2 = true ∧ ¬TotalOrder.le r2 r1 = true → st_leftRound n r1 = true)
    (st'_one_a : round → Bool) (st'_one_b_max_vote : node → round → round → value → Bool)
    (st'_one_b st'_leftRound : node → round → Bool) (st'_proposal : round → value → Bool)
    (st'_vote st'_decision : node → round → value → Bool)
    (hnext :
      ∃ n r max_round max_val,
        r ≠ TotalOrder.none ∧
          st_one_a r = true ∧
            ¬st_leftRound n r = true ∧
              ((max_round = TotalOrder.none ∧
                    ∀ (MAXR : round) (V : value), ¬(¬TotalOrder.le r MAXR = true ∧ st_vote n MAXR V = true)) ∨
                  max_round ≠ TotalOrder.none ∧
                    ¬TotalOrder.le r max_round = true ∧
                      st_vote n max_round max_val = true ∧
                        ∀ (MAXR : round) (V : value),
                          ¬TotalOrder.le r MAXR = true ∧ st_vote n MAXR V = true → TotalOrder.le MAXR max_round = true) ∧
                st'_one_a = st_one_a ∧
                  (st'_one_b_max_vote = fun x x_1 x_2 x_3 =>
                      if (x, x_1, x_2, x_3, ()) = (n, r, max_round, max_val, ()) then true
                      else st_one_b_max_vote x x_1 x_2 x_3) ∧
                    (st'_one_b = fun x x_1 => if (x, x_1, ()) = (n, r, ()) then true else st_one_b x x_1) ∧
                      (st'_leftRound = fun N R => decide (st_leftRound N R = true ∨ N = n ∧ ¬TotalOrder.le r R = true)) ∧
                        st'_proposal = st_proposal ∧ st'_vote = st_vote ∧ st'_decision = st_decision)
    (r1 r2 : round) (v1 v2 : value) (q : quorum)
    (h : ¬TotalOrder.le r2 r1 = true ∧ st'_proposal r2 v2 = true ∧ v1 ≠ v2) :
    ∃ n r3 rmax v,
      Quorum.member n q = true ∧
        ¬TotalOrder.le r3 r1 = true ∧ st'_one_b_max_vote n r3 rmax v = true ∧ ¬st'_vote n r1 v1 = true := by
  crush [hnext, hinv, h]
end Paxos

/-! ## Remaining known gap: higher-order over an *abstract* universe (`Test_Regression.lean`)

The Church tower above is over a concrete `{A : Type}`. lean-auto's original states it
over an abstract `{α : Sort u}` with the operations *universe-polymorphic in the
hypotheses* (`add : ∀ {α}, …`, `hadd : ∀ {α} x y f n, …`). That form still does not go
through: monomorphization would have to instantiate the `{α}` bound *inside* each
hypothesis at the goal's function types, which are themselves arrows the encoding
handles at use rather than as monomorphization candidates — the nested-binder boundary
documented in `Crush/Translation/Monomorphize.lean`. The ground-`A` version (handled
above) is the payload case; the abstract-universe form is tracked in `Doc/PLAN.md` §10.

```lean
example
    {A : Sort u}
    (add : ∀ {α}, ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
    (hadd : ∀ {α} x y f n, @add α x y f n = (x f) ((y f) n)) … : … := by
  crush [hadd, hmul, htwo, hthree]
```
-/
