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

# How the Main Options Compose

Three option families make independent decisions:

1. `crush.backend` chooses which solver receives the SMT-LIB query.
2. `crush.trust` chooses whether an `unsat` verdict may close the Lean goal
   directly or must produce a checked proof.
3. `crush.reconstruct` chooses how to build that proof when the trust policy
   requests one.

For example, this profile asks cvc5 to solve and requires either Alethe replay
or core-directed reconstruction to produce a checked Lean term:

```
set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "auto"
```

Changing between `"auto"` and `"core"` does not affect discharge under
`crush.trust "trust"`.
Conversely, changing to `crush.trust "reconstruct"` does not force Alethe:
Z3 and Bitwuzla can still use core-directed reconstruction.
Selecting `crush.reconstruct "alethe"` with an unsupported backend is an error
rather than a silent fallback, even under a trusting policy.

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

Use `"auto"` for ordinary checked proofs.
Use `"alethe"` when testing replay coverage, because a core fallback would hide
an unsupported certificate step.
Use `"core"` when comparing backends, when cvc5 emits no certificate for a
theory, or when a short Lean proof is easier than replaying the solver's
derivation.

{optionDocs crush.reconstruct.trustBvDecide}

This option preserves solver-proof reconstruction but expands its trusted base to
Lean's native code generator, which `bv_decide` uses while checking an LRAT
certificate. It does not permit arbitrary generated axioms. Accepted proofs expose
the dependency as `_native.bv_decide.ax_*` under `#print axioms`.

{optionDocs crush.reconstruct.trustNativeDecide}

This broader fallback can execute arbitrary Lean decision procedures. It therefore
trusts the native compiler and runtime, plus every executable definition reached
while deciding the proposition. Accepted proofs expose an
`_native.native_decide.ax_*` dependency under `#print axioms`.

Leave both options disabled for kernel-only reconstruction.
They differ in scope:

* `trustBvDecide` adds a specialized bitvector/SAT decision procedure and its
  native certificate-checking dependency.
* `trustNativeDecide` can execute any proposition with a synthesized
  `Decidable` instance and therefore trusts substantially more generated code.

Enable `trustBvDecide` first for bitvector-heavy goals.
Enable `trustNativeDecide` only when that broader executable trust boundary is
acceptable.
Neither option changes the SMT query or the meaning of
`crush.trust "trust"`.

For example, core reconstruction can exhaust a finite symbolic domain:

```lean
set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
set_option crush.reconstruct "core"
set_option crush.reconstruct.trustNativeDecide true

example (a b : BitVec 8) :
    (a &&& b) + (a ^^^ b) = a ||| b := by
  crush
```

# Higher-Order Translation

{optionDocs crush.ho.mode}

The values are:

* `"defunctionalize"` is the portable default.
* `"native"` passes function sorts and higher-order application directly to
  cvc5. Other backends warn and fall back to defunctionalization.

Use native mode for solving only with cvc5:

```
set_option crush.backend "cvc5"
set_option crush.ho.mode "native"
```

Backend `"none"` also preserves native higher-order syntax when exporting a
query without solving it.
Defunctionalization converts functions and partial applications to ordinary
first-order closure values and is portable across all backends.
Native mode preserves function sorts and application for cvc5.
It can avoid a large closure encoding, but cvc5 may not emit an Alethe
certificate for the resulting higher-order proof; use core reconstruction or a
trusting policy in that case.

# Monomorphization

{optionDocs crush.mono.fuel}

{optionDocs crush.mono.rounds}

Monomorphization specializes polymorphic facts at concrete types found in the
query.
`fuel` bounds the total number of generated type instances, while `rounds`
bounds how many times newly discovered types can trigger another saturation
pass.
If either bound is hit, lean-crush warns because the resulting fact set may be
incomplete.
Raise the bound only when the warning names monomorphization and the missing
instance is relevant to the goal.
Setting either bound to `0` disables monomorphization.

{optionDocs crush.mono.certify}

Certification is most useful under a trusting policy when auditing generated
specializations.
Reconstruction already asks Lean's kernel to check the final proof.

# Ground Instantiation

{optionDocs crush.inst.fuel}

{optionDocs crush.inst.rounds}

This pass uses relevant ground terms to instantiate explicit hints and selected
premises before SMT translation.
`fuel` bounds the total generated term instances; `rounds` bounds saturation
depth when one instance introduces terms that trigger another.
Set either option to `0` to disable it and retain the original quantified facts.
When generated instances are useful but do not completely replace a quantified
template, lean-crush first tries a ground-only query and retries with the
quantifier after `sat` or `unknown`.

Monomorphization and ground instantiation are not interchangeable.
The former chooses concrete Lean types for polymorphic facts; the latter chooses
concrete Lean terms for value quantifiers after types are fixed.

# Unfolding and Premises

{optionDocs crush.autoUnfold}

This controls definitions marked with `@[crush_unfold]` or `@[crush_defeq]`, as
well as preprocessing-only normalization of predicates marked with Lean's standard
`@[reducible]` attribute. Recursive reducible predicates use constructor-specific
rewrite equations, and no reducible equation is asserted as a quantified SMT fact.
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

The diagnostics answer different questions:

* `crush.profile` identifies the expensive pipeline stage.
* `crush.save` preserves the exact final query for external solver runs.
* `crush.trace.script` prints that query as an ordinary Lean info message.
* `trace.crush.*` reports internal decisions and can be filtered through Lean's
  trace system.

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
