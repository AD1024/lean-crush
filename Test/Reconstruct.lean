import Crush

/-!
Tests for proof reconstruction: turning an `unsat` verdict into a *checked* Lean
proof rather than closing the goal with an axiom.

The mechanism is solver-as-oracle. The solver's real contribution is not a proof
object but a **selection**: the unsat core names which two or three of the ambient
hypotheses actually matter. That is precisely what a Lean automated tactic cannot
work out for itself, and irrelevant hypotheses are what make such tactics time out.
So we rebuild the goal with only the core hypotheses in scope and hand it to a ladder
of finishers (`grind`/`omega`/`simp_all`, `funext`-prefixed for function equalities,
and `subst_vars; decide`/`rfl` for goals that turn on ground evaluation).

When that succeeds the solver leaves the trusted computing base entirely — it was a
search heuristic, and the resulting term is kernel-checked. The assertions below are
therefore about `#print axioms`: a reconstructed theorem must **not** mention
`Crush.crushSorry`.

`propext`, `Classical.choice`, and `Quot.sound` do appear; those are Lean's own
axioms, used by `grind` and by the standard library, and are not a trust
assumption specific to this tool.
-/

open Crush

set_option crush.timeout 10

-- Reconstruction may abstract data/type variables needed to state the target,
-- but it must not inherit proposition hypotheses omitted from the SMT core.
run_meta do
  let finishers ← finisherTactics
  Lean.Meta.withLocalDeclD `p (Lean.mkSort .zero) fun p =>
    Lean.Meta.withLocalDeclD `hp p fun _ => do
      let goal ← Lean.Meta.mkFreshExprMVar p
      let reconstructed ← IO.mkRef false
      discard <| Lean.Elab.Term.TermElabM.run' <| Lean.Elab.Tactic.run goal.mvarId! do
        reconstructed.set (← tryReconstruct goal.mvarId! #[] finishers)
      if ← reconstructed.get then
        throwError "reconstruction used an ambient hypothesis outside the SMT core"
      if ← goal.mvarId!.isAssigned then
        throwError "failed isolated reconstruction assigned the original goal"

-- Explicitly selected backward rules run before SMT, but their generated premises
-- may use only other selected facts. An omitted ambient proposition must remain
-- unavailable even though the original metavariable was created in that context.
run_meta do
  Lean.Meta.withLocalDeclD `p (Lean.mkSort .zero) fun p =>
    Lean.Meta.withLocalDeclD `q (Lean.mkSort .zero) fun q =>
      Lean.Meta.withLocalDeclD `hp p fun hp => do
        let ruleType ← Lean.mkArrow p q
        Lean.Meta.withLocalDeclD `rule ruleType fun rule => do
          let ruleFact : Fact := {
            prop := ruleType
            proof := some rule
            descr := "selected rule"
            instantiateTerms := true
          }
          let omittedGoal ← Lean.Meta.mkFreshExprMVar q
          let omittedClosed ← IO.mkRef false
          discard <| Lean.Elab.Term.TermElabM.run' <|
            Lean.Elab.Tactic.run omittedGoal.mvarId! do
              omittedClosed.set (← tryPreReconstruct omittedGoal.mvarId! #[ruleFact])
          if ← omittedClosed.get then
            throwError "pre-SMT selected-rule reconstruction used an omitted ambient fact"
          if ← omittedGoal.mvarId!.isAssigned then
            throwError "failed selected-rule reconstruction assigned the original goal"

          let premiseFact : Fact := {
            prop := p
            proof := some hp
            descr := "selected premise"
          }
          let selectedGoal ← Lean.Meta.mkFreshExprMVar q
          let selectedClosed ← IO.mkRef false
          discard <| Lean.Elab.Term.TermElabM.run' <|
            Lean.Elab.Tactic.run selectedGoal.mvarId! do
              selectedClosed.set
                (← tryPreReconstruct selectedGoal.mvarId! #[ruleFact, premiseFact])
          unless ← selectedClosed.get do
            throwError "pre-SMT selected-rule reconstruction did not apply a direct helper"
          let proof ← Lean.instantiateMVars (Lean.mkMVar selectedGoal.mvarId!)
          if proof.hasSorry || proof.hasMVar then
            throwError "pre-SMT selected-rule reconstruction produced an incomplete proof"
          Lean.Meta.check proof

/-! ## Policy-independent constructor witnesses

Witness synthesis runs before SMT even under `trust`: it produces a checked Lean proof,
not a solver axiom. These predicates intentionally hide constructor existence from SMT,
whose uninterpreted fallback otherwise admits a model where no list/tree satisfies them. -/

@[reducible]
def firstIs {α : Type} (value : α) : List α → Prop
  | [] => False
  | head :: _ => head = value

set_option crush.trust "trust" in
theorem pre_smt_list_witness {α : Type} (value : α) :
    ∃ values : List α, firstIs value values := by
  crush

/-- info: 'pre_smt_list_witness' does not depend on any axioms -/
#guard_msgs in
#print axioms pre_smt_list_witness

inductive WitnessTree (α : Type) where
  | empty
  | node (value : α) (rest : WitnessTree α)

@[reducible]
def rootIs {α : Type} (value : α) : WitnessTree α → Prop
  | .empty => False
  | .node root _ => root = value

set_option crush.trust "trust" in
theorem pre_smt_downstream_witness {α : Type} (value : α) :
    ∃ tree : WitnessTree α, rootIs value tree := by
  crush

/-- info: 'pre_smt_downstream_witness' does not depend on any axioms -/
#guard_msgs in
#print axioms pre_smt_downstream_witness

@[reducible]
def pathLike {α : Type} (next : α → α) (start : α) : List α → α → Prop
  | [], finish => start = finish
  | head :: tail, finish =>
      start = head ∧ pathLike next (next head) tail finish

@[reducible]
def validPathLike {α : Type} (next : α → α) (start : α)
    (values : List α) (finish : α) : Prop :=
  pathLike next start values finish ∧
    match values with
    | [] => True
    | _ :: tail => tail = []

set_option crush.trust "trust" in
theorem pre_smt_nested_reducible_witness {α : Type} (next : α → α) (start : α) :
    ∃ values : List α, validPathLike next start values (next start) := by
  crush

/-- info: 'pre_smt_nested_reducible_witness' does not depend on any axioms -/
#guard_msgs in
#print axioms pre_smt_nested_reducible_witness

@[reducible]
def nonzeroPath (next : Int → Int) (start : Int) : List Int → Int → Prop
  | [], finish => start = finish
  | head :: tail, finish =>
      head ≠ 0 ∧ start = head ∧ nonzeroPath next (next head) tail finish

@[reducible]
def listDistinct : List Int → Prop
  | [] => True
  | head :: tail => (∀ value, value ∈ tail → value ≠ head) ∧ listDistinct tail

@[reducible]
def distinctNonzeroPath (next : Int → Int) (start : Int)
    (values : List Int) (finish : Int) : Prop :=
  nonzeroPath next start values finish ∧ listDistinct values

set_option crush.trust "trust" in
theorem pre_smt_singleton_witness (weight : Int → Nat) (next : Int → Int)
    (start : Int) (bound : Nat) (hstart : start ≠ 0)
    (hweight : ¬ weight start ≥ bound) :
    ∃ values : List Int,
      (nonzeroPath next start values (next start) ∧ listDistinct values) ∧
        ∀ value ∈ values, weight value < bound := by
  crush

/-- info: 'pre_smt_singleton_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pre_smt_singleton_witness

set_option crush.trust "trust" in
theorem pre_smt_split_impossible_find (next : Int → Int) (values : List Int)
    (found : Int) (hpath : nonzeroPath next 0 values 0)
    (hfind : values.find? (fun _ => true) = some found) :
    found = 0 ∧ nonzeroPath next 0 (values.erase found) 0 := by
  crush

/-- info: 'pre_smt_split_impossible_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre_smt_split_impossible_find

set_option crush.trust "trust" in
theorem pre_smt_split_find_and_erase (weight : Int → Nat) (next : Int → Int)
    (start found : Int) (bound : Nat) (values : List Int)
    (hpath : nonzeroPath next start values 0) (hdistinct : listDistinct values)
    (hstart : start ≠ 0)
    (hweight : weight start ≥ bound)
    (hfind : values.find? (fun value => decide (weight value ≥ bound)) = some found) :
    start = found ∧
      distinctNonzeroPath next (next start) (values.erase found) 0 := by
  crush

/-- info: 'pre_smt_split_find_and_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pre_smt_split_find_and_erase

@[reducible]
def nilRequires (p : Prop) : List Nat → Prop
  | [] => p
  | _ :: _ => False

set_option crush.trust "trust" in
/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
theorem pre_smt_witness_respects_restriction (p : Prop) (hp : p) :
    ∃ values : List Nat, nilRequires p values := by
  crush []

set_option crush.trust "trust" in
theorem pre_smt_witness_uses_selected (p : Prop) (hp : p) :
    ∃ values : List Nat, nilRequires p values := by
  crush [hp]

/-- info: 'pre_smt_witness_uses_selected' does not depend on any axioms -/
#guard_msgs in
#print axioms pre_smt_witness_uses_selected

/-! ## Policy-independent local invariant reuse

VC generators commonly introduce a universally quantified invariant and then ask for one
of its instances. The pre-SMT pass should apply that local rule directly rather than send a
trivial but potentially nonlinear quantified identity to the solver. -/

set_option crush.trust "trust" in
theorem pre_smt_local_invariant {α : Type} (p : α → Prop)
    (invariant : ∀ value, p value) (value : α) : p value := by
  crush

/-- info: 'pre_smt_local_invariant' does not depend on any axioms -/
#guard_msgs in
#print axioms pre_smt_local_invariant

/-! ## Reconstruction succeeds — no trust axiom

Each of these is closed by a real Lean proof term. The `#guard_msgs` blocks pin the
axiom set, so a regression that silently fell back to the axiom would fail the
build rather than pass quietly. -/

section Succeeds
set_option crush.trust "reconstruct"

theorem eq_chain (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'eq_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_chain

theorem linear_arith (x y : Int) (h : x ≤ y) : x < y + 1 := by crush
/-- info: 'linear_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linear_arith

theorem propositional (p q : Prop) (hp : p) (hpq : p → q) : q := by crush
/-- info: 'propositional' does not depend on any axioms -/
#guard_msgs in
#print axioms propositional

theorem uf_congruence (f : Int → Int) (a b : Int) (h : a = b) : f a = f b := by crush
/-- info: 'uf_congruence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms uf_congruence

theorem nat_truncated_sub : ∀ n : Nat, n - 1 ≤ n := by crush
/-- info: 'nat_truncated_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nat_truncated_sub

theorem quantified_uf (f : Int → Int) (h : ∀ x, f x = x + 1) : f (f 0) = 2 := by crush
/-- info: 'quantified_uf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quantified_uf

-- Core-directed selection earning its keep: six hypotheses, only two relevant.
-- Handing the whole context to `grind` is what core selection avoids.
theorem ignores_irrelevant (a b c d e f g : Int) (h1 : a = b) (h2 : b = c)
    (junk1 : d > 0) (junk2 : e > 1) (junk3 : f > 2) (junk4 : g > 3) : a = c := by crush
/-- info: 'ignores_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ignores_irrelevant

-- Theory goals also replay: the finishers know these theories natively.
theorem bitvec_add_zero (x : BitVec 8) : x + 0 = x := by crush
/-- info: 'bitvec_add_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitvec_add_zero

theorem string_assoc (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by crush
/-- info: 'string_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms string_assoc

-- Higher-order: the encoding is only used to *find* the proof; `grind` replays it
-- against the original higher-order statement.
theorem higher_order (g : (Int → Int) → Int) (h : ∀ (f : Int → Int), g f = f 0) :
    g (fun x => x + 1) = 1 := by crush
/-- info: 'higher_order' does not depend on any axioms -/
#guard_msgs in
#print axioms higher_order

theorem funext_arity3 (f g : Int → Int → Int → Int)
    (h : ∀ x y z, f x y z = g x y z) : f = g := by crush
/-- info: 'funext_arity3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms funext_arity3

-- The `funext` rung must be arity-general on its own, not merely covered by `grind`
-- happening to reach the same goal. `repeat' funext _ <;> simp_all` parses as
-- `repeat' (funext _ <;> simp_all)` and closes only arity 1, so a regression there
-- would leave `funext_arity3` passing via an earlier rung and go unnoticed.
run_meta do
  let finishers ← finisherTactics
  let funextRung := finishers[3]!
  let intType := Lean.mkConst ``Int
  for arity in [1, 2, 3] do
    let mut fnType := intType
    for _ in [0:arity] do
      fnType := .forallE `x intType fnType .default
    Lean.Meta.withLocalDeclD `f fnType fun f =>
      Lean.Meta.withLocalDeclD `g fnType fun g => do
        -- `h : ∀ x̄, f x̄ = g x̄`, the pointwise premise a `funext` rung must consume.
        let pointwise ← Lean.Meta.forallTelescope fnType fun args _ => do
          Lean.Meta.mkForallFVars args
            (← Lean.Meta.mkEq (Lean.mkAppN f args) (Lean.mkAppN g args))
        Lean.Meta.withLocalDeclD `h pointwise fun h => do
          let goal ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq f g)
          let closed ← IO.mkRef false
          discard <| Lean.Elab.Term.TermElabM.run' <|
            Lean.Elab.Tactic.run goal.mvarId! do
              closed.set (← tryReconstruct goal.mvarId! #[h] #[funextRung])
          unless ← closed.get do
            throwError "the funext finisher rung failed at arity {arity}; it must strip \
              every arrow, not just the first"

-- Ground evaluation: after substituting `s = "ab"` the goal is a closed computation
-- (`String.length "ab" = 2`) that the reasoning finishers never evaluate; the
-- `subst_vars; decide`/`rfl` rungs close it, kernel-checked.
theorem eval_string_len (s : String) (h : s = "ab") : s.length = 2 := by crush
/-- info: 'eval_string_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_string_len

theorem eval_string_append (s t : String) (h : s ++ t = "abc") :
    (s ++ t).length = 3 := by crush
/-- info: 'eval_string_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_string_append

end Succeeds

/-! ## Datatype-guided nonlinear reconstruction

The solver selects the relevant nonlinear facts. Generic constructor splitting then exposes
the two `Int` constructors, after which the branch-local Lean finishers replay the result. -/

section Nonlinear
set_option crush.trust "reconstruct"

theorem nonlinear_replayed (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by
  crush
/-- info: 'nonlinear_replayed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nonlinear_replayed

end Nonlinear

/-! ## Solver skolemization and finite datatype replay -/

section Structured
set_option crush.trust "reconstruct"

theorem dependentChoiceReplayed {α β : Type} (p : α → β → Prop)
    (h : ∀ x, ∃ y, p x y) : ∃ f : α → β, ∀ x, p x (f x) := by
  crush

inductive ReplayColor where
  | red
  | green
  | ultraviolet

theorem enumPigeonholeReplayed (a b c d : ReplayColor) :
    a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
  crush

theorem emptyEliminated (x y : Empty) : x = y := by
  crush

end Structured

/-! ## Reconstruction fails — the boundary

Constructor splitting and linear finishers still cannot replay every nonlinear integer
fact. Under `reconstruct` this is an *error*, not a silent fallback — the whole point of
that policy is that the axiom is never used. -/

section Fails
set_option crush.trust "reconstruct"

/-- error: crush: solver reported `unsat`, but reconstruction failed -/
#guard_msgs(error, substring := true) in
theorem nonlinear_impossibility_not_replayed (x : Int) (h : x * x = 2) : False := by
  crush

end Fails

/-! ## `reconstructOrTrust` — the default policy

Try to reconstruct; fall back to the axiom with a warning if that fails. This gives
axiom-free proofs where possible without turning a solvable goal into an error, and
the warning makes the fallback visible rather than silent. -/

section Fallback
set_option crush.trust "reconstructOrTrust"

theorem fallback_not_needed (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'fallback_not_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fallback_not_needed

-- Not reconstructable, so the axiom is used — and the warning says so, rather than
-- the fallback being silent.
/-- warning: crush: solver reported `unsat`, but no finishing tactic could replay it -/
#guard_msgs(warning, substring := true) in
theorem fallback_used (x : Int) (h : x * x = 2) : False := by
  crush

/-- info: 'fallback_used' depends on axioms: [crushSorry] -/
#guard_msgs in
#print axioms fallback_used

end Fallback

/-! ## `trust` — the axiom is used unconditionally

The fast path: no reconstruction attempt, so every goal costs the axiom. Kept as a
policy because reconstruction is not free and some workloads want the speed. -/

section Trust
set_option crush.trust "trust"

theorem trusted (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'trusted' depends on axioms: [crushSorry] -/
#guard_msgs in
#print axioms trusted

end Trust

/-! ## The default policy is `trust`

No `set_option crush.trust` in scope here: `crush` runs under its shipped default, which
is `trust`. The goal closes on the solver's word, and `#print axioms` names `crushSorry` —
the point of routing trust through an auditable axiom rather than `sorry` is that this is
always visible. Reconstruction is opt-in, per the sections above.

Pinned both ways: a goal the finishers *could* have reconstructed still closes via the
axiom under the default (no reconstruction is attempted), and so does one they could
not. -/

section DefaultPolicy

-- Reconstructable, but not reconstructed: the default does not try.
theorem default_trusts (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush
/-- info: 'default_trusts' depends on axioms: [crushSorry] -/
#guard_msgs in
#print axioms default_trusts

-- Even a reconstructable nonlinear goal uses the axiom under the default policy.
theorem default_trusts_nonlinear (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by
  crush
/-- info: 'default_trusts_nonlinear' depends on axioms: [crushSorry] -/
#guard_msgs in
#print axioms default_trusts_nonlinear

-- A nonlinear goal outside the bounded reconstruction search errors rather than falling
-- back, so the stricter policy remains strict.
/-- error: crush: solver reported `unsat`, but reconstruction failed -/
#guard_msgs(error, substring := true) in
set_option crush.trust "reconstruct" in
theorem reconstruct_errors_not_trusts (x : Int) (h : x * x = 2) : False := by
  crush

end DefaultPolicy
