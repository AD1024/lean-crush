# lean-crush

**An SMT hammer for Lean 4.** Write `by crush` to solve goals involving arithmetic,
equalities, bitvectors, datatypes, and higher-order functions.

- **Higher-order translation:** supports function arguments, partial applications,
  and lambdas through defunctionalization or cvc5's native higher-order mode.
- **Checked proofs:** reconstructs Lean proofs from unsat cores or replays cvc5's
  Alethe certificates. Solver trust is explicit and auditable.
- **Extensible translation:** custom lowerings and replay rules use the same
  interfaces as the built-in theories.

See the [user manual](https://ad1024.github.io/lean-crush/) for the full guide,
configuration reference, and extension APIs.

## Quick start

Use the Lean version in [`lean-toolchain`](lean-toolchain) and install a solver on
`PATH`: Z3 ≥ 4.15.4 (the default), cvc5 ≥ 1.3.4, or Bitwuzla. cvc5 additionally
supports Alethe replay and native higher-order solving; Bitwuzla supports a
restricted quantifier-free fragment and does not provide proof certificates or
unsat cores. The package has no third-party Lean dependencies.

Add to your `lakefile.lean`, then run `lake update`:

```lean
require crush from git "https://github.com/AD1024/lean-crush" @ "main"
```

```lean
import Crush

example (x y : Int) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  crush

example (f : Int → Int) (a b : Int) (h : a = b) : f a = f b := by
  crush

example (g : (Int → Int) → Int) (h : ∀ f, g f = f 1) :
    g (fun x => x + 1) = 2 := by
  crush
```

By default, an SMT discharge trusts the solver using the `Crush.crushSorry`
axiom. To require a Lean proof, use the reconstruction policy below.

## Facts and unfolding

Bare `crush` introduces binders and uses all local hypotheses. Select facts or
supply extra lemmas with:

```lean
crush [h, myLemma]   -- only the listed hypotheses and lemmas
crush [*, myLemma]   -- all local hypotheses, plus a lemma
crush u[myFn]        -- unfold a definition using its equations
```

Definition equations may also be added automatically. Mark a definition with
`@[crush_unfold]`, or enable unfolding for an existing one:

```lean
attribute [local crush_unfold] List.length

example (xs : List Int) : xs.length = 0 ↔ xs = [] := by
  crush
```

Polymorphic lemmas are specialized to relevant types, and a bounded instantiation
pass supplies ground facts before solving. See
[Using the Tactic](https://ad1024.github.io/lean-crush/Using-the-Tactic/) for fact selection,
unfolding, induction examples, and premise search.

## Requiring checked proofs

```lean
set_option crush.trust "reconstruct" in
theorem checked (x y : Int) (hxy : x = y) (hy : y = 3) : x = 3 := by
  crush

#print axioms checked
```

This policy fails if reconstruction cannot produce a checked proof. The default
reconstruction portfolio can use cvc5's Alethe certificate and an unsat-core
fallback; Z3 uses core reconstruction. Some goals close with a checked proof
before SMT even under the default trust policy. Use `#print axioms` to inspect
dependencies.

Common settings include:

```lean
set_option crush.backend "cvc5"
set_option crush.trace.script true
```

See [Configuration](https://ad1024.github.io/lean-crush/Configuration-Reference/) for trust
policies, replay modes, timeouts, and debugging options.

## Custom lowerings

A lowering maps a Lean expression to an SMT term:

```lean
open Crush

def addThree (x : Int) : Int := x + 3

register_lowering term <<
  (addThree (term x)) => (smt| (+ $x 3))
>>

example (x : Int) : addThree x = x + 3 := by crush
```

`(term x)` recursively translates the captured expression; a bare `x` captures
its `Lean.Expr`. The RHS can also be a metaprogram. The same syntax supports
`register_lowering result-type` and `register_lowering sort`.

Use `register_crush_replay` for custom Alethe term decoding and inference rules,
and `@[crush_reconstruct]` for core reconstruction lemmas. See
[Extending lean-crush](https://ad1024.github.io/lean-crush/Extending-lean-crush/)
and [`Test/AletheExtension.lean`](Test/AletheExtension.lean) for complete examples.

## Limits

- **Induction is explicit.** Use Lean's `induction` tactic, then let `crush` close
  the cases using the induction hypotheses.
- **Translation is incomplete.** Unsupported operations may remain uninterpreted;
  supply lemmas, unfold definitions, or add a lowering. Native SMT bitvectors
  require concrete widths.
- **Solving can exceed reconstruction.** A solver may prove a goal whose
  certificate or core cannot yet be reconstructed in Lean.
- **Models describe the encoding.** A satisfiable SMT model is not necessarily a
  counterexample to the original Lean proposition.

See [Troubleshooting](https://ad1024.github.io/lean-crush/Troubleshooting-and-Limits/) for
unsupported cases and diagnostic options.

## Development and benchmarks

```sh
lake build              # library
lake build Test.Smoke   # quick solver integration check
lake build Test         # full dependency-free test suite
```

Runnable examples live in [`Test/`](Test/), with verification conditions in
[`Test/CaseStudies/`](Test/CaseStudies/) and optional Mathlib integration in
[`MathlibTest/`](MathlibTest/). Read the
[optimization guide](Doc/OPTIMIZATIONS.md) before changing search bounds or
reconstruction heuristics.

For recorded results, see [`BENCHMARKS.md`](BENCHMARKS.md) and the manual's
[coverage and reconstruction figures](https://ad1024.github.io/lean-crush/Benchmarks/).
To run the experiments:

```sh
bash run-experiments.sh
```

The first run provisions and builds the benchmark projects and can take hours.
Use `--suites curated` for the smallest suite; see the
[benchmark script guide](scripts/README.md) for prerequisites, resuming runs,
plotting, and individual harnesses.

## Acknowledgements

[lean-auto](https://github.com/leanprover-community/lean-auto) informed the design
and supplies test material. Verification case studies draw on
[Loom](https://github.com/verse-lab/loom),
[Velvet](https://github.com/verse-lab/velvet), Cashmere,
[Cedar](https://github.com/cedar-policy/cedar-spec), and
[Strata](https://github.com/strata-org/Strata).
[Veil](https://github.com/verse-lab/veil) informs the planned model minimization.
