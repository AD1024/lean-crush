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

end Crush.Proofs
