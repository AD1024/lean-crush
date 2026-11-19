import Crush

/-!
Tests for the hint grammar:

```
crush [h₁, …, *] u[f₁, …] d[g₁, …]
```

These exercise the capability that the argumentless tactic lacked entirely:
pointing `crush` at a lemma that is *not* a local hypothesis, restricting to an
explicit fact list, and pulling in a definition's equation lemmas.
-/

open Crush

set_option crush.trust "trust"

/-! ## Explicit lemma hints — the headline new capability

`extra_fact` is a top-level lemma, not a hypothesis of the goal. Bare `crush` cannot
see it; `crush [extra_fact]` asserts it and the goal closes. -/

axiom P : Int → Prop
axiom extra_fact : ∀ x : Int, P x

theorem uses_named_lemma (a : Int) : P a := by
  crush [extra_fact]

-- Combining an explicit lemma with the local context via `*`.
theorem lemma_plus_star (a b : Int) (h : a = b) : P a ∧ b = a := by
  crush [extra_fact, *]

/-! ## A list adds hints and never removes the local context

Hint lists follow `grind`: `crush [h1]` still sees the unlisted `h2`, and `crush []`
uses the goal's own antecedents, which `crush` introduces. `clear h` hides a
hypothesis. -/

theorem explicit_list_adds (a b c : Int) (h1 : a = b) (h2 : b = c) : a = c := by
  crush [h1]

opaque IntroT : Type

theorem empty_list_intro_prop (p : Prop) : p → p := by crush []
theorem empty_list_intro_eq (a b : Int) : a = b → b = a := by crush []
theorem empty_list_intro_nonempty (f : IntroT → IntroT) :
    Nonempty IntroT → ∃ x : IntroT, f x = f x := by crush []

set_option crush.trust "reconstruct" in
theorem empty_list_intro_eq_checked (a b : Int) : a = b → b = a := by crush []

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem cleared_hypothesis_unused (a b c : Int) (h1 : a = b) (h2 : b = c) : a = c := by
  clear h2
  crush [h1]

/-! ## Bare `crush` still sweeps the whole context (regression) -/

theorem bare_still_uses_all (a b c : Int) (h1 : a = b) (h2 : b = c) : a = c := by
  crush

/-! ## `u[…]` unfolds a definition via its equation lemmas

`crush` treats `double` as an uninterpreted symbol without help, so it cannot see
`double 3 = 6`. `u[double]` adds `double`'s defining equation, after which the goal
is linear arithmetic. -/

def double (n : Int) : Int := n + n

theorem unfold_definition : double 3 = 6 := by
  crush u[double]

-- `u[…]` also lets a fact *about* the unfolded symbol go through.
theorem unfold_with_hyp (x : Int) (h : x = 5) : double x = 10 := by
  crush [h] u[double]

/-! ## `d[…]` uses the single unfold equation

For a plain (non-recursive) definition, `d[f]` and `u[f]` coincide; the grammar is
accepted and the definition unfolds. -/

def triple (n : Int) : Int := n + n + n

theorem defeq_unfold : triple 2 = 6 := by
  crush d[triple]

/-! ## Diagnostics for malformed hints

A non-`Prop` term hint is rejected with a message naming the offending hint, rather
than silently producing a bad script. -/

/-- error: crush: hint (37 : Int) has type `Int`, which is not a `Prop` -/
#guard_msgs(error, substring := true) in
theorem rejects_non_prop_hint (a : Int) : a = a := by
  crush [(37 : Int)]

-- Unfolding something with no equational lemmas (an `axiom`) is a clear error.
/-- error: crush: `P` has no unfold equation. -/
#guard_msgs(error, substring := true) in
theorem rejects_unfoldable (a : Int) : a = a := by
  crush d[P]

/-! ## Definition names, `only`, and `-name`

A definition named in the list stands for its equations, as in `u[f]`. `only` drops
the automatically collected lemmas, here `@[crush_unfold]` equations. `-name` removes
one global constant from them. -/

def quad (n : Int) : Int := n + n + n + n

theorem list_definition_unfolds : quad 2 = 8 := by
  crush [quad]

theorem list_definition_with_fact (x : Int) (h : x = 1) : quad x = 4 := by
  crush [quad]

@[crush_unfold] def autoDouble (n : Int) : Int := n + n

theorem auto_unfold_applies : autoDouble 3 = 6 := by
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem only_drops_auto_unfold : autoDouble 3 = 6 := by
  crush only []

theorem only_keeps_listed_definition : autoDouble 3 = 6 := by
  crush only [autoDouble]

theorem only_keeps_hypotheses (x : Int) (h : autoDouble x = 2 * x) :
    autoDouble x = x + x := by
  crush only []

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem excluded_definition_not_unfolded : autoDouble 3 = 6 := by
  crush [-autoDouble]

theorem auto_double_spec (n : Int) : autoDouble n = 2 * n := by
  unfold autoDouble; omega

/-- error: crush: `-h` names a local hypothesis -/
#guard_msgs(error, substring := true) in
theorem rejects_local_exclusion (h : autoDouble 3 = 6) : autoDouble 3 = 6 := by
  crush [-h]

/-- error: crush: `auto_double_spec` is excluded by `-auto_double_spec` but also requested -/
#guard_msgs(error, substring := true) in
theorem rejects_excluded_and_listed : autoDouble 3 = 6 := by
  crush [auto_double_spec, -auto_double_spec]

/-- error: crush: `autoDouble` is excluded by `-autoDouble` but also requested -/
#guard_msgs(error, substring := true) in
theorem rejects_excluded_and_unfolded : autoDouble 3 = 6 := by
  crush [-autoDouble] u[autoDouble]

/-! ## The warning for an excluded constant that a proof still uses

crush cannot hide `-name` from Lean code it runs without assembling, such as instance
synthesis. After the goal closes, it reports a proof that still uses the constant. -/

namespace ExcludedWarning

open Lean Meta Crush

theorem cleanFact : (1 : Nat) + 1 = 2 := rfl
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem sorryFact : (2 : Nat) + 2 = 5 := sorry
axiom axiomFact : (3 : Nat) = 3
theorem trustedFact (a b : Int) (h : a = b) : b = a := by crush

private def excludedEntry (name : Name) : ExcludedHint := { name, constants := #[name] }

/--
warning: crush: the proof uses `ExcludedWarning.cleanFact`, which the hint list excludes.
  closed by: core reconstruction (kernel-checked)
  `ExcludedWarning.cleanFact`: a theorem; depends on no axioms
-/
#guard_msgs in
run_meta do
  warnExcludedUses (mkConst ``cleanFact) #[excludedEntry ``cleanFact]
    "core reconstruction (kernel-checked)"

/--
warning: crush: the proof uses `ExcludedWarning.sorryFact`, which the hint list excludes.
  closed by: core reconstruction (kernel-checked)
  `ExcludedWarning.sorryFact`: a theorem; depends on `sorryAx`
-/
#guard_msgs in
run_meta do
  warnExcludedUses (mkConst ``sorryFact) #[excludedEntry ``sorryFact]
    "core reconstruction (kernel-checked)"

/--
warning: crush: the proof uses `ExcludedWarning.axiomFact`, which the hint list excludes.
  closed by: trusted (`Crush.crushSorry`)
  `ExcludedWarning.axiomFact`: an axiom
-/
#guard_msgs in
run_meta do
  warnExcludedUses (mkConst ``axiomFact) #[excludedEntry ``axiomFact]
    "trusted (`Crush.crushSorry`)"

/--
warning: crush: the proof uses `ExcludedWarning.trustedFact`, which the hint list excludes.
  closed by: trusted (`Crush.crushSorry`)
  `ExcludedWarning.trustedFact`: a theorem; depends on `Crush.crushSorry`
-/
#guard_msgs in
run_meta do
  warnExcludedUses (mkConst ``trustedFact) #[excludedEntry ``trustedFact]
    "trusted (`Crush.crushSorry`)"

-- No exclusion, or an exclusion the proof does not use: no warning.
#guard_msgs in
run_meta do
  warnExcludedUses (mkConst ``cleanFact) #[] "core reconstruction (kernel-checked)"

#guard_msgs in
run_meta do
  warnExcludedUses (mkConst ``cleanFact) #[excludedEntry ``axiomFact]
    "core reconstruction (kernel-checked)"

-- End to end: inhabitation evidence comes from instance synthesis, which crush runs
-- but does not assemble, so the excluded instance still reaches the trusted proof.
axiom WarnCarrier : Type
axiom warnCarrierNonempty : Nonempty WarnCarrier
attribute [instance] warnCarrierNonempty

/--
warning: crush: the proof uses `ExcludedWarning.warnCarrierNonempty`, which the hint list excludes.
  closed by: trusted (`Crush.crushSorry`)
  `ExcludedWarning.warnCarrierNonempty`: an axiom
-/
#guard_msgs in
example (f : WarnCarrier → Int) (h : ∀ x, f x = 0) : ∃ x : WarnCarrier, f x = 0 := by
  crush [-warnCarrierNonempty]

end ExcludedWarning
