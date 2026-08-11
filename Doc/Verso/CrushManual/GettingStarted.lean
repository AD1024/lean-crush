import VersoManual
import Crush

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Getting Started" =>
%%%
tag := "getting-started"
%%%

# Requirements

lean-crush uses the Lean version pinned by its `lean-toolchain` file and has no
third-party Lean dependencies.
It does require an SMT solver executable on `PATH`:

* Z3 4.12.2 or newer is the default and is sufficient for ordinary use.
* cvc5 1.3 or newer additionally supports native higher-order solving and Alethe
  certificate replay.
* Bitwuzla can be selected for supported first-order queries.

The solver is a runtime dependency.
Importing or compiling the library does not start a solver; each `crush` tactic
invocation starts one query under a wall-clock timeout.

# Installation

Add lean-crush to the consuming project's `lakefile.lean`:

```
require crush from git
  "https://github.com/AD1024/lean-crush" @ "main"
```

Then update dependencies and import the root module:

```
lake update
```

```
import Crush
```

The root import exposes the tactic, configuration options, unfolding attributes,
SMT quotation syntax, and translation extension APIs.

# First Proofs

A bare `crush` introduces leading binders and reads every local proposition.
It is particularly effective for arithmetic constraints and equality
congruence:

```lean
example (x y : Int)
    (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  crush

example (f : Int → Int) (a b : Int)
    (h : a = b) : f a = f b := by
  crush
```

Quantified facts and higher-order values are supported:

```lean
example (g : Int → Int) (x : Int)
    (step : ∀ z, g z = z + 1) :
    g (g x) = x + 2 := by
  crush

example (applyAtOne : (Int → Int) → Int)
    (h : ∀ f, applyAtOne f = f 1) :
    applyAtOne (fun x => x + 1) = 2 := by
  crush
```

The default higher-order strategy translates these examples to first-order SMT
by monomorphizing, lambda-lifting, and defunctionalizing function values.

# Results and Trust

The solver can return three kinds of result:

* `unsat` means the hypotheses together with the negated goal are inconsistent,
  so the goal follows.
* `sat` means the solver found a model. lean-crush reports that model as a
  counterexample and leaves the goal open.
* `unknown`, including a timeout, leaves the goal open and reports the solver's
  reason.

By default, an `unsat` result closes the goal with the auditable
`Crush.crushSorry` axiom.
This is the fast hammer workflow, but it trusts both the translation and solver.
Use reconstruction when a kernel-checked proof is required:

```lean
set_option crush.trust "reconstruct" in
example (x y : Int) (hxy : x = y) (hy : y = 3) : x = 3 := by
  crush
```

The distinction is visible with `#print axioms`.
A theorem closed under the default policy lists `Crush.crushSorry`; a
successfully reconstructed theorem does not.

# A Practical Starting Point

Start with bare `crush`.
If it does not close the goal:

1. Check that the proposition really follows from the available hypotheses.
2. Add a relevant lemma with `crush [*, lemmaName]`.
3. Expose a hidden definition with `u[definition]` or `@[crush_unfold]`.
4. Inspect the generated query with `crush.trace.script`, `crush.save`, or
   `crush.backend "none"`.
5. Increase bounds only after identifying the phase that exhausted its budget.
