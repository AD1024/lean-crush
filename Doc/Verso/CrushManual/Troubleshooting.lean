import VersoManual
import Crush

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Troubleshooting and Limits" =>
%%%
tag := "troubleshooting"
%%%

# Classify the Failure First
%%%
tag := "troubleshooting-classify"
%%%

Do not increase every timeout and fuel bound at once.
The user-visible result identifies the failing pipeline stage:

* A `sat` result means the emitted SMT problem is satisfiable. Check selected
  facts, unfolding, lowering coverage, and then the Lean statement.
* An `unknown` result or timeout means translation completed but the backend did
  not decide the query. Reduce the query or change solver settings.
* An `unsat` result followed by a reconstruction error means solving succeeded.
  Change reconstruction inputs or algorithms, not the SMT encoding.
* A translation error naming a term or sort means the query could not be
  constructed. Add an equation, lowering, or sort handler.
* A `kernel-reject` during replay means a generated proof term was invalid.
  This is an implementation or extension defect, not a difficult proof.

Enable profiling before tuning performance:

```
set_option crush.profile true
```

For a capability failure, compare a local trusted run with a reconstructing run.
If `"trust"` closes the goal and `"reconstruct"` does not, the gap is strictly
in proof recovery.
Use `crush.backend "none"` only to inspect translation; it never solves or
closes the goal.

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

Use the smallest change that establishes the missing semantics:

* add a proposition with `crush [*, lemma]` when a theorem is missing;
* add `u[f]` or `d[f]` when the implementation is already solver-friendly;
* add a custom lowering when `f` has a direct SMT-theory representation.

`with [lemma]` cannot fix `sat`: reconstruction-only hints are not sent to the
solver.

# Timeout or Unknown
%%%
tag := "troubleshooting-timeout"
%%%

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
%%%
tag := "troubleshooting-smt"
%%%

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
%%%
tag := "troubleshooting-reconstruction"
%%%

Solving and proof reconstruction have different capabilities.
SMT can prove datatype cardinality, finite-array, native higher-order, or long
theory combinations that the current replay and finisher set cannot reproduce.
cvc5 1.3 does not emit Alethe certificates for the first three classes, so
`crush.reconstruct "auto"` must use the core-directed path for them.
It also rejects Alethe certificates containing signed bitvector-to-`Int`
conversion.

Available choices are:

* Add `with [lemma, h]` when core reconstruction needs a checked bridge fact
  only during this invocation.
* Add `using (tactics)` when the core facts support a short manual Lean proof.
* Register a reusable bridge theorem with `@[crush_reconstruct]`.
* Use cvc5 with `crush.reconstruct "auto"` to try Alethe before core
  reconstruction.
* Restructure the theorem into smaller kernel-checkable steps.
* Use `"reconstructOrTrust"` for an explicit warning and trusted fallback.
* Accept `"trust"` and audit the `Crush.crushSorry` dependency with
  `#print axioms`.

Choose the extension according to the reported Alethe failure.
A `term-gap` needs a term decoder, while a `rule-gap` needs an inference
registration.
If cvc5 did not emit a certificate, no replay extension can recover one; use
core reconstruction, a manual `using` finisher, or a different proof
decomposition.
Core reconstruction requires an unsat core. Z3 and cvc5 provide one; Bitwuzla
currently does not.

Do not interpret reconstruction failure as evidence that the goal is false.
It means only that lean-crush could not construct a checked Lean proof for the
solver's refutation.

To inspect core reconstruction attempts without dumping SMT-LIB:

```
set_option trace.crush.reconstruct true
set_option trace.crush.result true
```

# Known Boundaries
%%%
tag := "troubleshooting-boundaries"
%%%

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

Native higher-order solving is cvc5-only and currently lacks Alethe
certificates. Use defunctionalization for portable solving and replay.

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
