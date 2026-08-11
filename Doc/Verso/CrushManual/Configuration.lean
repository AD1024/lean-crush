import VersoManual
import Crush

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Configuration Reference" =>
%%%
tag := "configuration"
%%%

Every public setting is a registered Lean option.
Options can be scoped to a section, namespace, command, or individual theorem:

```lean
set_option crush.timeout 30 in
example (x y : Int) (h₁ : x ≤ y) (h₂ : y ≤ x) : x = y := by
  crush
```

Command-line `-D` settings are useful in CI or when testing a whole module:

```
lake env lean -Dcrush.backend=cvc5 MyProofs.lean
```

# Solver Process

{optionDocs crush.backend}

The available values are `"z3"`, `"cvc5"`, `"bitwuzla"`, and `"none"`.
The `"none"` backend performs collection, normalization, monomorphization,
instantiation, and translation, but does not start a solver or close the goal.
It is intended for inspecting or exporting the generated SMT-LIB.

For example, `crush` can emit a query while an ordinary Lean proof closes the
goal afterward:

```lean
set_option crush.backend "none" in
example (p : Prop) (h : p) : p := by
  crush
  exact h
```

{optionDocs crush.timeout}

The timeout applies independently to each solver query.
A ground-first query followed by a quantified fallback can therefore use the
budget twice.

{optionDocs crush.save}

If a quantified fallback is needed, the saved file contains the final query.
With backend `"none"`, it contains the complete translated fact set because no
solver verdict is available to justify omitting quantified fallbacks.

{optionDocs crush.additionalArgs}

The string is split on ASCII whitespace.
There is no shell-style quoting layer, so use this option for simple individual
flags rather than arguments containing spaces.

{optionDocs crush.logic}

Leave this empty unless a solver requires a narrower logic or a generated query
is being debugged.
The automatic logic is `ALL`, or `HO_ALL` for native higher-order cvc5.

# Trust and Reconstruction

{optionDocs crush.trust}

The values are:

* `"trust"` closes with `Crush.crushSorry`.
* `"reconstruct"` requires a kernel-checked proof and fails otherwise.
* `"reconstructOrTrust"` tries reconstruction and emits a warning before any
  trusted fallback.

{optionDocs crush.reconstruct}

The values are:

* `"auto"` tries Alethe replay, then core-directed reconstruction.
* `"alethe"` requires certificate replay and is primarily useful when developing
  or auditing the replay implementation.
* `"core"` ignores certificates and runs only the core-directed finisher ladder.

Alethe replay requires cvc5 1.3 or newer.
The core path works with any backend, but one of Lean's finishers must be able to
re-prove the result from the selected unsat-core hypotheses.

# Higher-Order Translation

{optionDocs crush.ho.mode}

The values are:

* `"defunctionalize"` is the portable default.
* `"native"` passes function sorts and higher-order application directly to
  cvc5. Other backends warn and fall back to defunctionalization.
* `"combinators"` is reserved but not implemented; it currently warns and falls
  back to defunctionalization.

Use native mode only with cvc5:

```
set_option crush.backend "cvc5"
set_option crush.ho.mode "native"
```

# Monomorphization

{optionDocs crush.mono.fuel}

{optionDocs crush.mono.rounds}

Monomorphization specializes polymorphic facts at concrete types found in the
query.
If either bound is hit, lean-crush warns because the resulting fact set may be
incomplete.
Raise the bound only when the warning names monomorphization and the missing
instance is relevant to the goal.

{optionDocs crush.mono.certify}

Certification is most useful under a trusting policy when auditing generated
specializations.
Reconstruction already asks Lean's kernel to check the final proof.

# Ground Instantiation

{optionDocs crush.inst.fuel}

{optionDocs crush.inst.rounds}

This pass uses relevant ground terms to instantiate explicit hints and selected
premises before SMT translation.
Set either option to `0` to disable it and retain the original quantified facts.
When generated instances are useful but do not completely replace a quantified
template, lean-crush first tries a ground-only query and retries with the
quantifier after `sat` or `unknown`.

# Unfolding and Premises

{optionDocs crush.autoUnfold}

This controls definitions marked with `@[crush_unfold]` or `@[crush_defeq]`.
Explicit `u[...]` and `d[...]` hints still apply when automatic unfolding is
disabled.

{optionDocs crush.premises}

{optionDocs crush.premises.max}

Premise selection applies only to bare `crush`.
Writing an explicit fact list, including `crush [*]`, disables automatic library
selection so the call remains reproducible and user-controlled.

# Diagnostics

{optionDocs crush.trace.script}

For normal development, prefer `crush.save` when the script is large.
The trace option is convenient for short queries and editor diagnostics.

{optionDocs crush.profile}

Profiling distinguishes time spent in Lean-side preprocessing and translation
from solver and reconstruction time.
It should be the first diagnostic enabled for a scalability problem.

Lean trace classes provide more focused details:

```
set_option trace.crush true
set_option trace.crush.mono true
set_option trace.crush.inst true
set_option trace.crush.script true
set_option trace.crush.result true
```

Trace classes are separate from `crush.trace.script`.
The option emits the script as an info message, while `trace.crush.script`
uses Lean's trace mechanism and can be filtered with other traces.
