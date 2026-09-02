# Higher-order to first-order metatheory

This directory contains the standalone semantic core of Crush's flattened
defunctionalization pass. It does not depend on the production translator,
SMT-LIB command representation, a solver, or proof reconstruction.

The development has three layers:

1. `HO/` defines an intrinsically typed higher-order language with Booleans,
   opaque base sorts, constants, nondependent functions, lambdas,
   applications, equality, connectives, and quantifiers. `HO/Semantics.lean`
   interprets arrows as Lean function spaces.
2. `FO/` defines the intrinsically typed first-order target. Source arrow types
   are erased to opaque function-value sorts; application and closure creation
   are represented by ordinary typed first-order symbols. Terms are indexed by
   an abstract *symbol family* (`FO/Family.lean`), not by positions in a finite
   signature: forming `Symbol.application arrow` immediately proves its
   declaration, so the translation carries no "the signature still contains this
   declaration" invariant and needs no weakening lemmas as a signature grows.
3. `Defunctionalization/` defines total flattened translation, constructs the
   canonical first-order extension of every higher-order model, and proves that
   it satisfies all generated closure equations, extensionality formulas, and
   translated source formulas.

The public reflection results are in `Soundness.lean`:

- `target_unsat_implies_source_unsat` handles one closed formula.
- `target_theories_unsat_implies_source_unsat` handles a finite theory.

Both are contrapositive model-extension arguments: any higher-order model of
the source gives a first-order model of the complete generated theory.

## What the theorems do not cover

Their hypothesis is `FO.FamilyTheoryUnsatisfiable`: no model of the abstract
symbol family satisfies the generated theory. Two boundaries separate that from
a Lean goal discharged by a solver, and neither is mechanized here.

**Lean expressions to the higher-order core.** Nothing connects a `Lean.Expr`
goal to a `Sentence signature`. The source language is a closed, monomorphic,
non-dependent core, with no polymorphism, dependent types, `let`, `if`,
literals, pattern matching, datatypes, or user translation handlers.

**The symbol family to a concrete SMT script.** A solver refutes a script over a
finite signature, whereas `FamilyTheoryUnsatisfiable` quantifies over models
interpreting the entire family. Transferring the former to the latter needs a
resolver defined on the symbols a theory actually uses, plus a proof that the
allocation is injective on them — without injectivity a resolver that collapsed
two closures would make an unsatisfiable script out of a satisfiable theory.
`AuxiliaryTheory.declarations` holds the data and nothing relates it to the
symbols the generated formulas contain. A resolver total over the whole family
cannot exist, since the family is inhabited at infinitely many declarations (one
`appDecl` per source arrow) while a signature is a list.

Two further limits hold against the implementation rather than the mathematics:

- This models `crush.ho.mode defunctionalize`, the default. `native` mode emits
  solver-level function sorts and lambdas and is not modeled.
- Every source base sort gets its own carrier, so no well-formedness guard can
  arise. The translator instead embeds some Lean types into larger SMT sorts
  (`Nat` into `Int`, guarded datatypes, finite arrays), and then emits guarded
  closure equations, a guarded `app`-result axiom, and *guarded* extensionality.
  The last is strictly stronger than `extensionality_valid`, because its guard
  sits inside the premise, so it is not justified by this development.

## Why custom datatypes are not part of this layer

The theorem only needs nonempty opaque base carriers. A custom datatype may be
treated abstractly as one such base sort, with fully applied operations treated
as constants. No constructor freeness, disjointness, injectivity, selector,
tester, exhaustiveness, or recursive datatype semantics is used by the
defunctionalization proof.

Those properties become necessary when connecting this abstract first-order
theory to concrete SMT `declare-datatypes` commands and when claiming that a
source model has free-datatype semantics. They should therefore be factored as
a later refinement, separate from the HO-to-FO result.
