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
   are represented by ordinary typed first-order symbols.
3. `Defunctionalization/` defines total flattened translation, constructs the
   canonical first-order extension of every higher-order model, and proves that
   it satisfies all generated closure equations, extensionality formulas, and
   translated source formulas.

The public reflection results are in `Soundness.lean`:

- `target_unsat_implies_source_unsat` handles one closed formula.
- `target_theories_unsat_implies_source_unsat` handles a finite theory.

Both are contrapositive model-extension arguments: any higher-order model of
the source gives a first-order model of the complete generated theory.

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
