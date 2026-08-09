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
/-- info: 'propositional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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
/-- info: 'higher_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-! ## Reconstruction fails — the boundary

The finishers cannot replay everything the solver can prove. Nonlinear arithmetic
and finite-domain exhaustiveness (enumeration pigeonhole) are the two shapes found
so far. Under `reconstruct` this is an *error*, not a silent fallback — the whole
point of that policy is that the axiom is never used. -/

section Fails
set_option crush.trust "reconstruct"

-- Nonlinear: the solver decides `x * x = 4 ∧ x > 0 → x = 2`, `omega` is linear-only
-- and `grind` does not find it.
/-- error: crush: solver reported `unsat`, but reconstruction failed -/
#guard_msgs(error, substring := true) in
theorem nonlinear_not_replayed (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by
  crush

inductive Three where | a | b | c

-- Pigeonhole over a three-constructor enumeration. The solver gets this from
-- datatype exhaustiveness + distinctness; the finishers would need a case split the
-- core does not hand them (note the core here is *just* the negated goal).
/-- error: crush: solver reported `unsat`, but reconstruction failed -/
#guard_msgs(error, substring := true) in
theorem pigeonhole_not_replayed (w x y z : Three) :
    w = x ∨ w = y ∨ w = z ∨ x = y ∨ x = z ∨ y = z := by crush

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
theorem fallback_used (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by crush

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

-- The nonlinear goal no finisher can replay: under `reconstruct` this is an error, under
-- the default it closes on trust.
theorem default_trusts_nonlinear (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by
  crush
/-- info: 'default_trusts_nonlinear' depends on axioms: [crushSorry] -/
#guard_msgs in
#print axioms default_trusts_nonlinear

-- Asking for `reconstruct` on that same goal errors rather than falling back, so the
-- stricter policy is still available and still strict.
/-- error: crush: solver reported `unsat`, but reconstruction failed -/
#guard_msgs(error, substring := true) in
set_option crush.trust "reconstruct" in
theorem reconstruct_errors_not_trusts (x : Int) (h : x * x = 4) (h2 : x > 0) : x = 2 := by
  crush

end DefaultPolicy
