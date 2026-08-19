import VersoManual
import Crush

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Troubleshooting and Limits" =>
%%%
tag := "troubleshooting"
%%%

# The Goal Is Not Proved

A `sat` result means the emitted facts admit a model. The model satisfies the
encoding, which is weaker than the Lean statement wherever an operation stayed
uninterpreted, so it need not be a Lean counterexample.
Check these causes in order:

1. A required premise is missing.
2. An explicit `crush [...]` list accidentally omitted a local hypothesis because
   it did not contain `*`.
3. A relevant function remained uninterpreted.
4. The Lean statement is genuinely false.

If a definition is the issue, add `u[f]`, `d[f]`, an unfolding attribute, or a
custom lowering.
If the model assigns surprising values to an unsupported function, that usually
indicates missing semantics rather than a solver bug.

# Timeout or Unknown

First enable `crush.profile`.
The remedy depends on the expensive phase:

* Collection or premise selection: lower `crush.premises.max` or use an explicit
  hint list.
* Monomorphization: remove irrelevant polymorphic hints before raising
  `crush.mono.fuel` or `crush.mono.rounds`.
* Ground instantiation: reduce quantified hints, or adjust `crush.inst.fuel` and
  `crush.inst.rounds`.
* Translation: look for deeply nested terms or definitions that should be
  normalized earlier.
* Solving: inspect the SMT-LIB, reduce irrelevant quantifiers, then consider a
  larger `crush.timeout`.
* Reconstruction: try the other reconstruction mode or simplify the unsat core.

More facts are not always better.
An unrelated quantified lemma can trigger an unbounded solver matching loop.
Prefer the smallest explicit set that contains the needed argument.

# Inspecting SMT-LIB

Use `crush.save` to write the final query:

```
set_option crush.save "query.smt2"
```

Use backend `"none"` to test collection and translation without starting a
solver:

```
set_option crush.backend "none"
set_option crush.save "query.smt2"
```

Because backend `"none"` deliberately does not close the goal, follow `crush`
with another proof tactic when using it inside a successful Lean declaration.

For short queries, `crush.trace.script true` or `trace.crush.script true` prints
the generated script.
`trace.crush.mono`, `trace.crush.inst`, and `trace.crush.result` expose the main
decision points without dumping the whole query.

# Reconstruction Fails After Unsat

Solving and proof reconstruction have different capabilities.
SMT can prove datatype cardinality, finite-array, native higher-order, or long
theory combinations that the current replay and finisher set cannot reproduce.
cvc5 1.3 does not emit Alethe certificates for the first three classes, so
`crush.reconstruct "auto"` must use the core-directed path for them.
It also rejects Alethe certificates containing signed bitvector-to-`Int`
conversion.

Available choices are:

* keep `crush.trust "reconstruct"` and restructure the proof into smaller
  kernel-checkable steps;
* use cvc5 with `crush.reconstruct "auto"` to enable Alethe replay;
* use `"reconstructOrTrust"` for an explicit warning and trusted fallback;
* accept the default `"trust"` policy and audit the dependency with
  `#print axioms`.

Do not interpret reconstruction failure as evidence that the goal is false.
It means only that lean-crush could not construct a checked Lean proof for the
solver's refutation.

# Known Boundaries

lean-crush intentionally does not perform induction.
Drive induction in Lean and invoke `crush` on the resulting cases.

Not every library function has a built-in encoding.
Unsupported functions remain uninterpreted unless equation lemmas or a lowering
are supplied.
Operations such as `Finset.card` commonly need a theorem relating them to
already-supported operations.

Indirectly recursive datatypes, such as a tree containing `List Tree`, may be
represented opaquely.
Constructor equality preprocessing recovers direct same-constructor
injectivity, but nested discrimination can still require an explicit Lean lemma.

Finite arrays support local reads and updates.
Operations that transform a symbolic range, including `append`, `extract`,
`map`, and `filter`, generally need quantified lemmas or custom lowerings.

Higher-order combinator mode is not implemented.
Use the default defunctionalized mode or cvc5 native mode.

# Reporting a Minimal Failure

A useful issue report contains:

* the complete standalone theorem and imports;
* solver name and version;
* the values of non-default `crush.*` options;
* whether default trust succeeds and reconstruction fails;
* the saved SMT-LIB query when translation or solver behavior is relevant;
* the `crush.profile` phase breakdown for performance reports.

Reduce unrelated quantified hypotheses first.
This often turns an apparent solver limitation into a specific missing lowering,
unfolding lemma, or instantiation pattern.
