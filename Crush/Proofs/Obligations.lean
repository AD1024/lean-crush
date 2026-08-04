import Crush.Reify.Term

/-!
# Soundness proof obligations (statements)

This module states — but does not yet prove — the semantic-equivalence and
equisatisfiability theorems that each translation pass must satisfy for
lean-crush to be sound *without trusting the solver's translation*. See
`Doc/PLAN.md` §10b for the full ledger and staging plan.

Every theorem here is currently `sorry`-backed. The point of stating them now is:

1. the *statements* type-check, so the intended contract of each pass is pinned
   down in Lean rather than only in prose;
2. `#print axioms` on anything downstream reveals exactly which obligations are
   still open (they show up as `sorryAx`);
3. discharging them is Milestone 6, and each discharged `sorry` shrinks the
   trusted computing base — mirroring how `bv_decide` shipped trusted and was
   then verified incrementally.

The semantics are given abstractly here (`Interp`, `Sat`) so the statements can
exist before the concrete interpretation function is built; Milestone 6 replaces
these opaque placeholders with the real denotational semantics of `CTerm`.
-/

namespace Crush.Proofs

open Crush.Reify

/-- An interpretation assigns Lean meanings to the atoms/etoms of the reified
logic. Left opaque until the denotational semantics land (Milestone 6). -/
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

section Passes

-- Placeholders for each pass's implementation, to be replaced by the real ones.
-- Stated as parameters so the obligations reference a concrete symbol.
variable (preprocess monomorphize defunctionalize combinators skolemize
          lowerCTerm : List CTerm → List CTerm)

/-- **P1** — Preprocessing (β/η, `let`/proj reduction) preserves meaning. -/
theorem p1_preprocess_equiv : Equivalence preprocess := by
  sorry

/-- **P3** — Every monomorphization instance is implied by the source, so the
pass preserves meaning (the retained Lean proof witnesses each instance). -/
theorem p3_monomorphize_equiv : Equivalence monomorphize := by
  sorry

/-- **P4** — Defunctionalization is equisatisfiable with the source: the
introduced `apply`/closure symbols and their defining axioms neither add nor
remove models up to reinterpretation. **The headline higher-order theorem.** -/
theorem p4_defunctionalize_equisat : Equisat defunctionalize := by
  sorry

/-- **P5** — Combinator (S/K/B/C/W) encoding is equisatisfiable with the source. -/
theorem p5_combinators_equisat : Equisat combinators := by
  sorry

/-- **P6** — Skolemization is equisatisfiable (classical, via `Classical.choice`). -/
theorem p6_skolemize_equisat : Equisat skolemize := by
  sorry

/-- **P8** — Lowering `CTerm → SMT.Term` preserves the denoted value. -/
theorem p8_lowering_equiv : Equivalence lowerCTerm := by
  sorry

end Passes

/-! ## Obligations discovered while implementing Milestone 2

The three items below were each a *live bug* found by differential probing against
Lean and z3 (see `Doc/PLAN.md` §10 items 3–6). They are stated here because a
passing regression test is weaker than a theorem: the tests pin the specific
counterexamples that were observed, whereas these statements pin the property.
-/

section Milestone2

/-- The embedding of a Lean type into its SMT sort, and the well-formedness
predicate meant to carve out its image. Opaque until the real semantics land. -/
opaque SortImage : Type
opaque embed : SortImage → CTerm
opaque wfPred : CTerm → Prop

/-- **P10** — The datatype well-formedness guard is *exact*.

SMT datatypes are freely generated over their field sorts, so encoding a `Nat`
field as `Int` makes the SMT type strictly larger than the Lean type. `wf_T` must
characterize precisely the image of the Lean type — no more, no less:

* **soundness** (⊇ is not enough): if `wf_T` admitted a value outside the image,
  a quantifier guarded by it would range over phantom values, and a *true* Lean
  hypothesis could become unsatisfiable. This is exactly the observed bug, where
  `∀ p : PN, p.x ≥ 0` was unsat and `False` followed from it.
* **completeness** (⊆ is not enough either): if `wf_T` excluded a real value, we
  would lose provable goals.

Hence the biconditional. -/
theorem p10_wf_exact : ∀ t : CTerm, wfPred t ↔ ∃ v : SortImage, embed v = t := by
  sorry

/-! ### P11 — Theory-operator agreement at the boundary

The general statement ("each emitted SMT operator denotes the same total function
as its Lean counterpart") cannot be stated non-trivially until the denotational
semantics of `SMT.Term` exist — that is Milestone 6, and it is what `p8` will
carry. What *can* be pinned down now, and is the part that actually bit us, is the
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

end Milestone2

end Crush.Proofs
