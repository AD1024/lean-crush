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
%%%
tag := "configuration-composition"
%%%

`crush.backend` selects the solver, `crush.trust` controls discharge of
`unsat`, and `crush.reconstruct` selects the checked proof procedure.
See {ref "using-crush-proof-policy"}[Choosing a Proof Policy] for a starting
configuration.

Under `crush.trust "trust"`, `"auto"` and `"core"` do not request
reconstruction. Selecting `"alethe"` still requires cvc5, even with a trusting
policy or backend `"none"`.

# Solver Process
%%%
tag := "configuration-solver"
%%%

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
An early checked proof produces no script and does not update this file; use
`"none"` when script emission is required.

{optionDocs crush.additionalArgs}

The string is split at literal spaces, with surrounding ASCII whitespace trimmed
from each resulting argument.
There is no shell-style quoting layer, so use this option for simple individual
flags rather than arguments containing spaces.

{optionDocs crush.logic}

Leave this empty unless a solver requires a narrower logic or a generated query
is being debugged.
The automatic logic is `ALL`, or `HO_ALL` for native higher-order cvc5.
Bitwuzla maps the automatic choice to `QF_AUFBV`, its supported fragment.
An explicit `crush.logic` value is authoritative and is not rewritten for the
selected backend.

# Trust and Reconstruction
%%%
tag := "configuration-reconstruction"
%%%

{optionDocs crush.trust}

This policy applies to solver `unsat` results. It does not prevent
{ref "overview-pipeline"}[an early checked proof] from closing the goal before
SMT. Inspect `#print axioms` to audit the resulting theorem's dependencies.

{optionDocs crush.preReconstruct.ruleSearch}

With this option off, the early pass still reuses selected facts and
premise-free local universal rules, eliminates empty inductive types, searches
for existential witnesses, and tries bounded datatype splitting. Enabling it
also allows backward application of selected rules with premises to discharge.

The pass runs under every trust policy except checked Alethe-only mode, and
backend `"none"` bypasses it to ensure script emission. These exceptions apply
regardless of the rule-search setting. Successful early proofs avoid SMT;
unsuccessful searches still cost time.

{optionDocs crush.reconstruct}

Use `"auto"` for ordinary checked proofs. `"core"` uses Z3 or cvc5's unsat
core and Lean finishers; Bitwuzla supplies neither a core nor a certificate.

With a reconstructing trust policy, `"alethe"` bypasses early proofs and
requires a replayed cvc5 certificate. It fails on missing certificates or
replay errors even under `"reconstructOrTrust"`. This makes it useful for
testing replay extensions.

{optionDocs crush.reconstruct.trustBvDecide}

`bv_decide` adds a native LRAT-checking dependency, visible as
`_native.bv_decide.ax_*` in `#print axioms`.

{optionDocs crush.reconstruct.trustNativeDecide}

`native_decide` is broader: core reconstruction may execute any available
decision procedure, trusting the native compiler, runtime, and definitions it
reaches. The dependency appears as `_native.native_decide.ax_*`.

Both options are off by default. Leave them off for kernel-only proof
generation; enable `trustBvDecide` first if a native bitvector checker is
acceptable. Neither changes the SMT query or the trusting policy.

# Higher-Order Translation
%%%
tag := "configuration-higher-order"
%%%

{optionDocs crush.ho.mode}

`"defunctionalize"`, the default, translates functions, lambdas, and partial
applications to first-order closure values. The resulting query still needs
the backend's ordinary theory and quantifier support.

`"native"` preserves function sorts and application for cvc5, or for script
export with backend `"none"`. Other backends warn and fall back to
defunctionalization. Native higher-order queries may lack an Alethe certificate;
core reconstruction or a trusting policy can still be used.

# Monomorphization
%%%
tag := "configuration-monomorphization"
%%%

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
%%%
tag := "configuration-instantiation"
%%%

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
%%%
tag := "configuration-diagnostics"
%%%

{optionDocs crush.trace.script}

For normal development, prefer `crush.save` when the script is large.
The trace option is convenient for short queries and editor diagnostics.

{optionDocs crush.profile}

Profiling distinguishes time spent in Lean-side preprocessing and translation
from solver and reconstruction time.
It should be the first diagnostic enabled for a scalability problem.

{optionDocs crush.profile.machine}

`crush.profile.machine` is intended for benchmark tooling.
It has an effect only when `crush.profile` is enabled and adds one
tab-separated `CRUSH_PROFILE` record per tactic invocation.
The record includes the outcome, replay status, nanosecond phase timings, and
certificate-size metrics for successful Alethe replay.
Interactive users normally need only the human-readable `crush.profile`
report.

Lean trace classes provide more focused details:

```
set_option trace.crush true
set_option trace.crush.mono true
set_option trace.crush.inst true
set_option trace.crush.script true
set_option trace.crush.result true
set_option trace.crush.reconstruct true
set_option trace.crush.replay true
```

Trace classes are separate from `crush.trace.script`.
The option emits the script as an info message, while `trace.crush.script`
uses Lean's trace mechanism and can be filtered with other traces.
`trace.crush.replay` reports attempts, selected methods, and decode/dispatch
timings by Alethe rule. It also prints the decoded inputs for steps taking at
least 100 ms. Anchor timings are inclusive and overlap their nested steps.
