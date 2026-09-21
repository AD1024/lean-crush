import VersoManual

open Verso.Genre Manual

#doc (Manual) "Overview" =>
%%%
tag := "overview"
%%%

lean-crush closes Lean goals by translating selected facts and the negated goal
to SMT-LIB. It is useful for arithmetic, equality, datatypes, arrays, and
quantified constraints. Function values and lambdas are supported through
defunctionalization or cvc5's native higher-order mode.

Use it after the surrounding proof has exposed the relevant facts. Induction
and domain-specific decomposition remain in Lean.
Start with {ref "getting-started"}[Getting Started] for installation and examples.

# What Happens During `crush`
%%%
tag := "overview-pipeline"
%%%

1. *Collect.* Select local hypotheses, explicit lemmas, relevant defining
   equations, and optional library premises.
2. *Try an early proof.* Reuse selected facts or apply bounded, kernel-checked
   Lean reasoning.
3. *Normalize.* Rewrite selected definitions and expose constructor structure
   with proofs of the rewrites.
4. *Specialize.* Instantiate polymorphic facts at concrete types, then generate
   bounded ground instances of eligible quantified facts.
5. *Translate.* Produce SMT sorts, terms, declarations, and axioms. Functions
   without an encoding or defining equations remain uninterpreted.
6. *Solve.* Ask the selected backend whether the facts contradict the negated
   goal. A ground-only query may retry with retained quantifiers.
7. *Discharge.* Accept `unsat` under the trust policy, replay an Alethe
   certificate, or reconstruct from the unsat core. `sat` reports a model;
   `unknown` leaves the goal open.

An early proof skips SMT even under the default trusting policy. Backend
`"none"` and checked Alethe-only mode bypass that shortcut. The early pass is
otherwise independent of the trust policy; its optional rule search is
controlled by {ref "configuration-reconstruction"}[`crush.preReconstruct.ruleSearch`].
Requesting a certificate can also affect solver time, so the cost of checked
proofs is not confined to the final stage.

# Choosing the Next Step

* For ordinary use, start with bare `crush`, then
  {ref "using-crush-facts"}[choose facts] or
  {ref "using-crush-definitions"}[expose definitions] as needed.
* For kernel-checked proofs, select
  {ref "using-crush-proof-policy"}[a reconstruction policy].
  {ref "using-crush-reconstruction"}[Core hints and finishers] can supply a
  short Lean argument when solving succeeds but reconstruction fails.
* For custom encodings, choose an
  {ref "extending-choose"}[extension point]. Translation lowerings change the
  SMT query; replay and reconstruction rules recover Lean proofs.
* For a failure or a slow goal, follow
  {ref "troubleshooting-classify"}[the diagnostic workflow] before increasing
  timeouts or search bounds.

The {ref "configuration"}[Configuration Reference] documents every option.
The {ref "benchmarks"}[Benchmarks] chapter explains the recorded coverage,
reconstruction, and timing measurements.
