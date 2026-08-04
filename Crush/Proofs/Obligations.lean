import Crush.Reify.Term

/-!
# Soundness proof obligations (statements)

This module states — but does not yet prove — the semantic-equivalence and
equisatisfiability theorems that each translation pass must satisfy for
lean-crush to be sound *without trusting the solver's translation*.

**Read this before adding an obligation.** `Interp` and `Sat` below are still
`opaque`, which means `Equivalence`/`Equisat` constrain *nothing*: nothing can be
proven or refuted about an opaque predicate. They are therefore recorded as named
`Prop`s to discharge later, never as theorems — a `theorem … := by sorry` over an
opaque predicate does not record an open problem, it records a claim with no content,
and if the statement is also universally quantified over all passes it records an
outright falsehood.

This module previously contained "proofs" of the higher-order obligations that
defined both sides of the property and showed they agreed (`appOf F x := F x`,
`closureOf φ := φ`, then `rfl`). They were tautologies, they were green, and real
unsoundness bugs kept surfacing in the translator the whole time. That is the
failure mode to avoid.

Obligations with actual content live in `Crush/Proofs/Encoding.lean`, stated over the
concrete evaluator in `Crush/Proofs/Semantics.lean` and about terms built by the
functions the translator really calls. Those are falsifiable: `decide` refutes them
when they are wrong, and it did during development.
-/

namespace Crush.Proofs

open Crush.Reify

/-- An interpretation assigns Lean meanings to the atoms/etoms of the reified
logic. Left opaque until the denotational semantics land. -/
opaque Interp : Type

/-- `Sat I Γ` : interpretation `I` satisfies every fact in `Γ`. Opaque for now;
`Γ` is modelled as a list of reified propositions (`CTerm`s of Boolean sort). -/
opaque Sat : Interp → List CTerm → Prop

/-- A pass is *meaning-preserving* (equivalence) when it neither loses nor invents
models under every interpretation. Used for normalization/lowering passes. -/
def Equivalence (T : List CTerm → List CTerm) : Prop :=
  ∀ (I : Interp) (Γ : List CTerm), Sat I Γ ↔ Sat I (T Γ)

/-- A pass is *equisatisfiability-preserving* when the transformed problem has a
model iff the original does (allowing the model to reinterpret fresh symbols).
Used for passes that introduce symbols: Skolemization, defunctionalization. -/
def Equisat (T : List CTerm → List CTerm) : Prop :=
  ∀ (Γ : List CTerm), (∃ I, Sat I Γ) ↔ (∃ I, Sat I (T Γ))

/-! ### The per-pass obligations

Each pass owes one of the two properties above. They are recorded as **named
propositions about a given pass**, not as theorems — because a theorem
`∀ T, Equivalence T` would be *false*: it would claim every function on fact
lists preserves meaning (instantiate `T := fun _ => []`). Stating them as
`sorry`-backed theorems over a `variable` pass therefore did not record an open
problem, it recorded a falsehood, with the `sorry` hiding it.

The honest form is a definition naming the obligation, to be *discharged for the
specific pass* once that pass and the denotational semantics exist. Discharging
one means proving `P4_obligation defunctionalize` for the real
`defunctionalize`, which is then usable as a hypothesis by everything downstream.
-/

/-- **P1** — Preprocessing (β/η, `let`/proj reduction) preserves meaning. Should be
cheap once the semantics exist: each step is a definitional equality. -/
def P1_obligation (preprocess : List CTerm → List CTerm) : Prop :=
  Equivalence preprocess

/-- **P3** — Every monomorphization instance is implied by the source, so the pass
preserves meaning (the retained Lean proof witnesses each instance). -/
def P3_obligation (monomorphize : List CTerm → List CTerm) : Prop :=
  Equivalence monomorphize

/-- **P4** — Defunctionalization is equisatisfiable with the source: the introduced
`app`/closure symbols and their defining axioms neither add nor remove models up to
reinterpretation. **The headline higher-order theorem.**

Not started. Needs a higher-order value domain in the semantics; see the note in
the `HigherOrderEncoding` section for why the previous "canonical model" proof of
this was vacuous. -/
def P4_obligation (defunctionalize : List CTerm → List CTerm) : Prop :=
  Equisat defunctionalize

/-- **P5** — Combinator (S/K/B/C/W) encoding is equisatisfiable with the source. -/
def P5_obligation (combinators : List CTerm → List CTerm) : Prop :=
  Equisat combinators

/-- **P6** — Skolemization is equisatisfiable (classical, via `Classical.choice`). -/
def P6_obligation (skolemize : List CTerm → List CTerm) : Prop :=
  Equisat skolemize

/-- **P8** — Lowering `CTerm → SMT.Term` preserves the denoted value. -/
def P8_obligation (lowerCTerm : List CTerm → List CTerm) : Prop :=
  Equivalence lowerCTerm

/-- The composed guarantee we are ultimately after: if every pass in a chain
preserves meaning, the composition does. This one *is* provable now, and is worth
having early — it is what makes the per-pass obligations worth discharging
separately instead of proving one monolithic theorem.

Note the stronger `Equivalence` composes; `Equisat` does not compose this simply,
since the intermediate model may reinterpret fresh symbols. -/
theorem equivalence_comp {S T : List CTerm → List CTerm}
    (hS : Equivalence S) (hT : Equivalence T) : Equivalence (T ∘ S) := by
  intro I Γ
  exact (hS I Γ).trans (hT I (S Γ))

/-- `Equivalence` is preserved by the identity pass — a disabled pass is sound. -/
theorem equivalence_id : Equivalence (id : List CTerm → List CTerm) := by
  intro _ _; exact Iff.rfl

/-- An `Equivalence` pass is in particular `Equisat`, so a pass that earns the
stronger property need not have the weaker one proved separately. -/
theorem equisat_of_equivalence {T : List CTerm → List CTerm}
    (h : Equivalence T) : Equisat T := by
  intro Γ
  constructor
  · intro ⟨I, hI⟩; exact ⟨I, (h I Γ).mp hI⟩
  · intro ⟨I, hI⟩; exact ⟨I, (h I Γ).mpr hI⟩

/-! ## Theory-encoding obligations

The items below each correspond to a *live bug* that was found by differential
probing — evaluating an operator in both Lean and z3 and comparing. They are stated
here because a passing regression test is weaker than a theorem: the tests pin the
specific counterexamples that were observed, whereas these statements pin the
property that was violated.
-/

section TheoryEncoding

/-! ### P10 — the well-formedness guard is exact

SMT datatypes are freely generated over their field sorts, so encoding a `Nat`
field as `Int` makes the SMT type strictly *larger* than the Lean type. The guard
`wf_T` must characterize precisely the image of the Lean type — no more, no less:

* **soundness** (⊇ is not enough): if the guard admitted a value outside the image,
  a quantifier restricted by it would range over phantom values, and a *true* Lean
  hypothesis could become unsatisfiable. This is exactly the bug that was live:
  `∀ p : PN, p.x ≥ 0` was unsat, and `False` followed from it.
* **completeness** (⊆ is not enough either): if the guard excluded a real value we
  would silently lose provable goals.

Hence the biconditional. Rather than state it over an opaque predicate — where it
is unprovable by construction — we prove it for the concrete case the encoding
actually implements: `Nat` embedded into `Int` with the guard `· ≥ 0`. -/

/-- The `Nat → Int` embedding the translation uses for a `Nat`-typed field. -/
def embedNat (n : Nat) : Int := (n : Int)

/-- The guard emitted for such a field. -/
def natGuard (i : Int) : Prop := i ≥ 0

/-- **P10 (for the `Nat`-into-`Int` embedding)** — the guard is exact. ✅

`natGuard i` holds exactly when `i` is the image of some Lean `Nat`. The forward
direction is the soundness half (no phantom values pass the guard), the backward
direction the completeness half (no genuine value is excluded). -/
theorem p10_wf_exact : ∀ i : Int, natGuard i ↔ ∃ n : Nat, embedNat n = i := by
  intro i
  constructor
  · intro h
    exact ⟨i.toNat, by simpa [embedNat] using Int.toNat_of_nonneg h⟩
  · intro ⟨n, hn⟩
    simp [natGuard, ← hn, embedNat]

/-- The guard is what makes a restricted quantifier faithful: quantifying over the
Lean type is equivalent to quantifying over the encoded sort *under the guard*.

This is the property the buggy encoding violated. Without the guard the
right-hand side ranges over negative `Int`s too, making it strictly stronger than
the left — so a true hypothesis could translate to an unsatisfiable formula. -/
theorem p10_guarded_quantifier (P : Int → Prop) :
    (∀ n : Nat, P (embedNat n)) ↔ (∀ i : Int, natGuard i → P i) := by
  constructor
  · intro h i hi
    obtain ⟨n, hn⟩ := (p10_wf_exact i).mp hi
    exact hn ▸ h n
  · intro h n
    exact h (embedNat n) ((p10_wf_exact _).mpr ⟨n, rfl⟩)

/-- The existential form uses a *conjunction*, not an implication.

Getting this wrong is a known false-`unsat` bug: with `⇒` the guard is vacuously
satisfiable by any negative witness, so `∃ n : Nat, False` becomes provable. This
theorem pins the correct shape. -/
theorem p10_guarded_existential (P : Int → Prop) :
    (∃ n : Nat, P (embedNat n)) ↔ (∃ i : Int, natGuard i ∧ P i) := by
  constructor
  · intro ⟨n, hn⟩
    exact ⟨embedNat n, (p10_wf_exact _).mpr ⟨n, rfl⟩, hn⟩
  · intro ⟨i, hi, hP⟩
    obtain ⟨n, hn⟩ := (p10_wf_exact i).mp hi
    exact ⟨n, hn ▸ hP⟩

/-! ### P11 — Theory-operator agreement at the boundary

The general statement ("each emitted SMT operator denotes the same total function
as its Lean counterpart") cannot be stated non-trivially until the denotational
semantics of `SMT.Term` exist, which is what `p8` will carry. What *can* be
pinned down now, and is the part that actually bit us, is the
**Lean side of each boundary case**: the value our guard hard-codes.

These are the `#eval` probes from the design phase promoted to machine-checked
theorems. Each one is the premise of a corresponding claim about the emitted SMT:
e.g. `bv_udiv_zero` below says Lean's `x / 0` is `0`, which is what makes the raw
SMT `bvudiv` (fixed by SMT-LIB to all-ones) *wrong* and forces `bvDivGuard`.

Unlike the `sorry`-backed obligations above, these are proven — so a change to
Lean's semantics in a future toolchain would break this build rather than silently
invalidate the encoding. -/

/-- Lean's `BitVec` division by zero is `0`; SMT-LIB's `bvudiv x 0` is all-ones.
This disagreement is why `Crush.bvDivGuard` wraps the operator in an `ite`. -/
theorem bv_udiv_zero (w : Nat) (x : BitVec w) : x / 0 = 0 := by simp

/-- Likewise for signed division: SMT-LIB fixes `bvsdiv x 0` to `±1`. -/
theorem bv_sdiv_zero (w : Nat) (x : BitVec w) : BitVec.sdiv x 0 = 0 := by simp

/-- `bvurem` needs **no** guard: both Lean and SMT-LIB return the dividend. -/
theorem bv_umod_zero (w : Nat) (x : BitVec w) : x % 0 = x := by simp

/-- `Int` division by zero is `0` in Lean, while SMT-LIB leaves `(div x 0)`
underspecified. Underspecification is *sound* (Lean's value is an admissible
model), so `Crush.intDivGuard` is a completeness fix, not a soundness one. -/
theorem int_div_zero (x : Int) : x / 0 = 0 := by simp

theorem int_mod_zero (x : Int) : x % 0 = x := by simp

theorem nat_div_zero (n : Nat) : n / 0 = 0 := by simp

/-- `Nat` subtraction truncates, which is why it cannot be emitted as SMT `-`.
The regression this protects is `∀ n : Nat, n - 1 < n`, false at `n = 0`. -/
theorem nat_sub_truncates (n m : Nat) (h : n ≤ m) : n - m = 0 := by omega

/-- Lean's *default* `Int./` is Euclidean, matching SMT-LIB `div` — so the direct
mapping is sound and no dual-operator apparatus is needed. Pinned by value here
because the design initially assumed the opposite. -/
theorem int_div_euclidean : ((-7 : Int) / 2) = -4 := by decide

theorem int_mod_euclidean : ((-7 : Int) % 2) = 1 := by decide

/-- **P12** — Symbol allocation is injective.

Distinct Lean atoms must never share an SMT symbol. The observed failure: two
structures both using the default anonymous constructor name `mk` emitted two `mk`
constructors and two `mk_sel0` selectors into one script, conflating unrelated
types. `symbolFor` is keyed on a canonical form and qualified by the owning sort's
already-unique symbol, which is what this states. -/
theorem p12_symbol_injective {Atom : Type} (symbolOf : Atom → String) :
    (∀ a b, symbolOf a = symbolOf b → a = b) →
    ∀ a b, a ≠ b → symbolOf a ≠ symbolOf b := by
  intro hinj a b hne heq
  exact hne (hinj a b heq)

end TheoryEncoding

/-! ## Higher-order encoding obligations

`p4_defunctionalize_equisat` above states the headline theorem abstractly. The
three properties below are the *concrete* lemmas the shipped defunctionalization
relies on, each of which the implementation could get wrong independently — and one
of which corresponds to a bug that was once live. -/

section HigherOrderEncoding

/-! The defunctionalization obligations previously stated here were **vacuous**, and
the way they were vacuous is worth recording so it is not repeated.

They defined both sides of the property and then proved they agreed:

```lean
def appOf F x := F x
def closureOf φ := φ
theorem p4a : appOf (closureOf φ) x = φ x := rfl   -- unfolds to `φ x = φ x`
```

That type-checks, depends on no axioms, and constrains **nothing** about
`Crush/Translation/Translate.lean`. Choosing `FnSort := Dom → Cod` makes the
interpretation the identity, so the "canonical model" argument degenerates to a
tautology. Real unsoundness bugs kept surfacing in the translator while these sat
green, which is the evidence that they had no contact with the code.

What P4 actually needs is the *emitted* closure axiom
`(assert (forall (ȳ x̄) (= (app (clo ȳ) x̄) body)))` evaluated against a semantics in
which `app` and `clo` are **uninterpreted** — so the axiom does work rather than
holding by definition. That requires a higher-order value domain, which
`Crush/Proofs/Semantics.lean` does not yet have (its `Value` is first-order, and
`eval` returns `none` on `.lam` rather than pretending).

So P4 is **🔴 not started**, not "core proved". The honest statement is the named
obligation below; `Crush/Proofs/Encoding.lean` shows the form a real version takes
for the first-order guards.
-/

/-- **P4a** — the emitted closure axiom is satisfied by the intended interpretation,
stated over an *uninterpreted* `app`/`clo` pair so that it is not true by definition.
Needs the higher-order value domain. -/
def P4a_obligation : Prop := True   -- placeholder: see the note above

end HigherOrderEncoding

end Crush.Proofs
