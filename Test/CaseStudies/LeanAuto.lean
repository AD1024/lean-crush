import Crush

/-!
# Case study: lean-auto's harder test corpus, ported to `crush`

`Test/LeanAutoPort.lean` ports lean-auto's `SmtTranslation/{BoolNatInt,BitVec,String}`
and the easy `Inductive` cases. This file is the **case study for the harder
material** — the goals that were *not* already covered: the mutually-recursive and
single-constructor datatypes from `SmtTranslation/Inductive.lean`, the higher-order
Church-numeral and polymorphic goals from `Test_Regression.lean`, and the Paxos
consensus goal from `SmtTranslation/Names.lean`.

Each goal is filed as **handled** (a closed `theorem`/`example`), **sound refusal**
(true in Lean but declined rather than closed unsoundly — pinned with `#guard_msgs`),
or **known gap** (diagnosis in a comment). Several started as gaps this study surfaced
and were closed here; see `Doc/PLAN.md` §11b for the full account. Only one gap
remains: the Church tower over an *abstract universe*.

Ports run under `crush.trust "trust"` by default (measuring translation + solving, as
`LeanAutoPort.lean` does), except where a section shows reconstruction. `auto`'s `d[f]`
maps to `crush`'s `u[f]`; lean-auto's `autoImplicit on` becomes explicit binders here.
-/

open Crush

set_option crush.trust "trust"
set_option crush.timeout 15

/-! ## Handled: mutually-recursive datatypes (`Inductive.lean` `tree`/`treelist`)

Emitted as one grouped `declare-datatypes` with every sort and `wf` predicate in scope
before any axiom references a sibling's. This was a `crush` bug the study surfaced
(each member emitted separately, so `tree`'s selector referenced `treelist` before it
existed); fixed in `Translate.lean`, `declareDatatype`. -/

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

A lean-auto TODO; `crush` treats every inductive uniformly (one SMT constructor per
Lean constructor), so the single-ctor case needs no special path. -/

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

/-! ## Handled: higher-order over a *ground* function space (`Test_Regression.lean`)

λ-equalities and quantified facts about an uninterpreted higher-order `add`, all via
the defunctionalization path. -/

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

Hypotheses quantify over a *type* and a `List` of it; the goal instantiates them.
Monomorphization specializes each `p α`/`q β` at the types in play, leaving a
first-order UF residual. -/

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

`Test_Regression.lean`'s "Polymorphic free variable". With the element type a goal
parameter (`{α : Type}`, one opaque sort), `ap` and its associativity axiom are
first-order. Contrast the type-binding-in-the-hypothesis form (remaining gap), which
does not. -/

example {α : Type} (as bs cs ds : List α)
    (ap : List α → List α → List α)
    (ap_assoc : ∀ (as bs cs : List α), ap (ap as bs) cs = ap as (ap bs cs)) :
    ap (ap as bs) (ap cs ds) = ap as (ap bs (ap cs ds)) := by
  crush [ap_assoc]

/-! ## Handled: function composition via `Function.comp_def` (`Test_Regression.lean`)

`(g ∘ h) ∘ f` *is* `fun x => g (h (f x))`, so `P` of defeq arguments is equal;
`comp_def` supplies the rewrite. Exercises the whole hint→monomorphize→defunctionalize
path, and relies on the two monomorphization refinements this study drove (PLAN §11b):
polymorphic hints keep their leading type binder, and candidates are restricted to
data sorts so `comp_def`'s `Sort` binders are not instantiated at `Prop`. -/

example {α β γ : Type}
    (P : (α → γ) → Prop) (f : α → β) (g : β → γ) (h : β → β) :
    P ((g ∘ h) ∘ f) = P (fun x => g (h (f x))) := by
  crush [Function.comp_def]

/-! ## `Option.orElse` with a λ (`Inductive.lean`): refused bare, closed with unfold

`Option.orElse x (fun _ => none) = x` is true, but the identity *is* `orElse`'s
definition. Bare, `orElse` is uninterpreted with no defining axiom, so `crush` finds a
model where the sides differ and declines (sound — lean-auto flags this too); `u[…]`
supplies the equation and it closes (the analogue of lean-auto's `d[Option.orElse]`). -/

-- Bare: sound refusal, pinned so a (only-possible-unsoundly) regression fails the build.
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example {α : Type} (x : Option α) :
    Option.orElse x (fun _ => Option.none) = x := by crush

example {α : Type} (x : Option α) :
    Option.orElse x (fun _ => Option.none) = x := by crush u[Option.orElse]

/-! ## Handled and *reconstructed*: higher-order Church numerals (`Test_Regression.lean`)

The Church tower over a ground function space. A translation gap this study surfaced:
applying a function-valued variable to fewer than the flattened `app` arity (`x (y f)`,
result still a function) emitted `app` under-applied, which z3 rejected. Fixed in
`hoTerm?` by η-expanding to a closure of the residual arrow sort; z3 then solves it in
~40 ms. It closes under the **default `reconstruct` policy** — the `funext` finishers
replay the function equality — so this example overrides the file's `trust`, and
`#print axioms` witnesses no `crushSorry`. -/

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

lean-auto's largest SMT goal: a Paxos safety obligation with typeclasses, six-level
quantifier nesting, and `fun`-valued state updates. It translates cleanly, but the
≈60 ∀ / 14 ∃ alternation defeats both solvers' default E-matching. cvc5 with
`--full-saturate-quant` (via `crush.additionalArgs`) closes it in ~0.2 s — reachable
with the right flag, not blocked on the `trigger` support lean-auto uses. Under
`trust`: like the Church tower, the verdict is a heavy quantified UF proof no
core-directed finisher replays.

The proof is plain modus ponens — `h` discharges the premise of `hinv`'s 6th conjunct,
whose conclusion is the goal — so it uses `TotalOrder`/`Quorum` only as uninterpreted
symbols and depends on *none* of their class laws (`le_total` etc. never reach the
query). Weakening a law therefore leaves it provable, correctly. -/

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

/-! ## Remaining gap: Church numerals over an *abstract* universe (`Test_Regression.lean`)

lean-auto's original binds `{α : Sort u}` *inside* each hypothesis (`add : ∀ {α}, …`).
Monomorphization would have to instantiate that inner `{α}` at the goal's function
types — arrows the encoding handles at use, not as monomorphization candidates (the
nested-binder boundary in `Monomorphize.lean`). The ground-`A` version above is the
payload case; this is tracked in `Doc/PLAN.md` §10.

```lean
example {A : Sort u}
    (add : ∀ {α}, ((α → α) → (α → α)) → ((α → α) → (α → α)) → ((α → α) → (α → α)))
    (hadd : ∀ {α} x y f n, @add α x y f n = (x f) ((y f) n)) … := by crush […]
```
-/
