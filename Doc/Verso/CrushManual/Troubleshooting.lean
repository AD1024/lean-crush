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

* A missing-executable error means the selected backend's solver is not installed.
  Install it or select a backend that is; no query ran.
* A `sat` result means the emitted SMT problem is satisfiable. Check selected
  facts, unfolding, lowering coverage, and then the Lean statement. When the message
  also reports a refused command, the backend rejected part of the query and the
  model covers only the rest.
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
If both runs reach SMT and return `unsat`, but only `"trust"` closes the goal,
focus on proof recovery. Check the profiler or `trace.crush.result` first:
early checked proofs can bypass SMT, and requesting a certificate can change
the solver's behavior.
Use `crush.backend "none"` only to inspect translation; it never solves or
closes the goal.

# The Goal Is Not Proved

An SMT model need not be a Lean counterexample: uninterpreted operations can
admit extra models. After ruling out refused commands, check these causes:

1. A required premise is missing.
2. An explicit `crush [...]` list accidentally omitted a local hypothesis because
   it did not contain `*`.
3. A relevant function remained uninterpreted.
4. The Lean statement is false.

Add a missing premise with `crush [*, lemma]`; expose a definition with
`u[f]`, `d[f]`, or an unfolding attribute; use a lowering for a direct SMT
theory encoding. See {ref "extending-choose"}[Choosing an Extension Point].

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

If `crush` closes the goal before translation, no script is written. An existing
file at that path may therefore belong to an earlier run.

Use backend `"none"` to test collection and translation without starting a
solver or taking an early proof shortcut:

```
set_option crush.backend "none"
set_option crush.save "query.smt2"
```

Because backend `"none"` deliberately does not close the goal, follow `crush`
with another proof tactic when using it inside a successful Lean declaration.

For short queries, `crush.trace.script true` or `trace.crush.script true` prints
the generated script.
`trace.crush.mono`, `trace.crush.inst`, and `trace.crush.result` expose the main
decision points without dumping the whole query. Use `trace.crush.replay` to
identify slow Alethe rules and the replay method selected for each one.

# Reconstruction Fails After Unsat
%%%
tag := "troubleshooting-reconstruction"
%%%

Solving and proof reconstruction have different capabilities.
SMT can prove datatype cardinality, finite-array, native higher-order, or long
theory combinations that the current replay and finisher set cannot reproduce.
The tested cvc5 1.3.4 backend has certificate gaps for datatype cardinality,
finite-array encodings, native higher-order solving, and signed
bitvector-to-`Int` conversion. When it cannot emit a certificate,
`crush.reconstruct "auto"` can still try core-directed reconstruction.

For the core path, add {ref "using-crush-reconstruction"}[`with [...]` facts
or a `using` finisher], register a reusable `@[crush_reconstruct]` theorem, or
split the goal into smaller steps. Core reconstruction needs an unsat core,
available from Z3 and cvc5.

For Alethe replay, the first failure identifies the layer:

* `term-gap`: a certificate term could not be decoded. A custom operator may
  need `register_crush_replay term`; some terms also need evidence such as
  nonemptiness of a Lean type.
* `rule-gap`: the terms decoded, but Lean could not prove the inference or
  validate a source assumption. Use `register_crush_replay rule`.
* `certificate-error` or a missing-certificate message: cvc5 supplied no usable
  proof. A replay registration cannot fix this; try `"auto"` or `"core"`.
* `malformed-certificate`: the certificate's structure or premise references
  could not be replayed.
* `kernel-reject` or `replay-exception`: inspect the failing step and extension
  for an invalid proof or implementation error.

See {ref "extending-alethe"}[Extending Alethe Replay] for registration examples.
If a trusted result is acceptable, choose an explicit
{ref "using-crush-proof-policy"}[trust policy]; strict Alethe mode never takes
the `"reconstructOrTrust"` fallback.

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

Bitvector theory requires a statically known width. A symbolic `BitVec n`
uses an opaque sort even if the context proves `0 < n`.

Native higher-order solving is cvc5-only and has certificate gaps.
Defunctionalization supports more backends, but its encoded function sorts need
not contain every Lean function. Function-existence goals may therefore need a
Lean witness before invoking SMT.

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
