import VersoManual
import Crush

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Using the Tactic" =>
%%%
tag := "using-crush"
%%%

# Tactic Syntax
%%%
tag := "using-crush-syntax"
%%%

The tactic accepts these clauses, in the order shown:

```
crush [h₁, lemma, *] u[f, g] d[h] with [r₁, r₂] using (tactic₁; tactic₂)
```

Every component after `crush` is optional.
The `u[...]` and `d[...]` groups may be repeated and mixed.
The `with [...]` and `using` clauses customize checked reconstruction and, when
both are present, must appear in that order.

These clauses act at different stages:

* `[...]` chooses propositions for the SMT query.
* `u[...]` and `d[...]` provide equations for rewriting and for SMT.
* `with [...]` supplies proof terms only to checked core reconstruction.
* `using` supplies a final Lean tactic only to checked core reconstruction.

The last two clauses are rejected under `crush.trust "trust"` because trusted
mode does not attempt reconstruction. They do not affect Alethe certificate
replay, which reconstructs individual solver steps instead of the original goal.

# Choosing Solver Facts
%%%
tag := "using-crush-facts"
%%%

## Bare, Restricted, and Extended Calls

A bare call includes every local hypothesis whose type is a proposition:

```lean
theorem orderedTrans (a b c : Int)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  crush
```

An explicit list without `*` is a strict restriction.
Unlisted local hypotheses are excluded; relevant defining equations may still
be added automatically:

```lean
theorem orderedTransRestricted (a b c : Int)
    (hab : a ≤ b) (hbc : b ≤ c)
    (_irrelevant : c < a + 100) : a ≤ c := by
  crush [hab, hbc]
```

Use `*` to combine every local proposition with named lemmas that are not
already in the context:

```lean
theorem orderedTransWithContext (a b c : Int)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  crush [*, Int.le_trans]
```

`crush []` deliberately sends no local hypotheses.
`crush [*]` and bare `crush` both include the local propositions, but they are
not identical:

* bare `crush` permits optional library premise selection and leaves quantified
  local hypotheses out of eager proof-producing ground instantiation;
* `crush [*]` disables premise selection and opts quantified local hypotheses
  into eager ground instantiation.

Prefer a bare call as the default.
Use an explicit list to make the dependency set reproducible, remove irrelevant
quantifiers, or request eager instances of a selected quantified fact.

## Supplying Lemmas

Explicit lemmas need not already be hypotheses.
lean-crush specializes polymorphic lemmas and generates bounded ground
instances before translation.
This often avoids unpredictable solver-side quantifier instantiation:

```lean
axiom successorPositive :
  ∀ x : Int, 0 ≤ x → 0 < x + 1

example (x : Int) (hx : 0 ≤ x) : 0 < x + 1 := by
  crush [successorPositive, hx]
```

Ground instantiation is bounded by `crush.inst.fuel` and
`crush.inst.rounds`.
Monomorphization has separate `crush.mono.fuel` and `crush.mono.rounds`
bounds.

## Automatic Premise Selection

Bare `crush` can ask Lean's registered `LibrarySuggestions` engine for relevant
library theorems:

```
set_option crush.premises true
set_option crush.premises.max 32
```

Premise selection is useful when the needed theorem is not obvious, but it can
make performance and dependencies less predictable.
Writing any explicit list, including `crush [*]`, disables premise selection.
Once the relevant theorems are known, prefer naming them explicitly.

# Exposing Definitions
%%%
tag := "using-crush-definitions"
%%%

An untranslated function is treated as uninterpreted.
That is sound, but its defining equations are unavailable unless they are
provided explicitly.
Use `u[...]` to add all equation lemmas of a definition.
For recursive definitions, these are usually one constructor-specific equation
per defining clause:

```lean
def addThree (x : Int) : Int := x + 3

example (x : Int) : addThree x > x := by
  crush u[addThree]
```

Use `d[...]` to add one definitional unfold equation instead.
It is best for non-recursive wrappers and definitions whose complete equation
set is unnecessary:

```lean
def nonnegative (x : Int) : Prop := 0 ≤ x

example (x : Int) (h : nonnegative x) : x + 1 > 0 := by
  crush d[nonnegative]
```

Both forms also drive proof-producing rewrites before SMT translation.
For persistent support, `@[crush_unfold]` corresponds to `u[f]` and
`@[crush_defeq]` to `d[f]`:

```lean
@[crush_unfold]
def twice (x : Int) : Int := x + x

example (x : Int) : twice (x + 1) = twice x + 2 := by
  crush
```

Both attributes are relevance-filtered, so a marked definition contributes
nothing to a query that cannot reach it.
`set_option crush.autoUnfold false` disables the attributes, but explicit
`u[...]` and `d[...]` clauses still apply.

# Helping Checked Reconstruction
%%%
tag := "using-crush-reconstruction"
%%%

The solver and Lean's core-directed reconstruction have different inputs.
A fact in `[...]` is available while solving and may also appear in the unsat
core.
A fact in `with [...]` is withheld from SMT and becomes available only after the
solver has returned `unsat`.

Use `with [...]` when the SMT encoding is already sufficient but Lean needs a
bridge theorem to recover the source-level proof:

```lean
set_option crush.trust "reconstruct" in
example (x : Int) (hx : x = 4) : x ≤ 4 := by
  crush with [Int.le_of_eq hx]
```

The hint cannot turn a `sat` query into an `unsat` query.
In this example, `hx` still reaches SMT through the bare call; only
`Int.le_of_eq hx` is reconstruction-only.

Use `using` when reconstruction needs a short, goal-specific tactic script
rather than another fact:

```lean
def reconstructionStep (x : Int) : Int :=
  x + 1

set_option crush.trust "reconstruct" in
example (x : Int) : reconstructionStep x > x := by
  crush d[reconstructionStep] using
    (simp [reconstructionStep]; omega)
```

The tactic runs on the original goal with only the isolated unsat-core facts and
the `with [...]` hints in its local context.
It cannot accidentally use unrelated hypotheses that the solver did not use.
Its result, including any auxiliary declarations it creates, is checked by
Lean's kernel before assignment.
If an early checked proof or Alethe replay already closes the goal, the core
finisher is not run.

Use these mechanisms at different scales:

* `with [...]` is a per-call collection of reconstruction facts.
* `using` is a per-call reconstruction procedure.
* `@[crush_reconstruct]` registers a reusable theorem for core reconstruction
  throughout a module or library.
* `register_crush_replay` extends step-by-step Alethe certificate replay.

Alethe replay uses only the last mechanism. See
{ref "extending-reconstruction"}[core reconstruction rules] and
{ref "extending-alethe"}[replay extensions] for the persistent APIs.

# Drive Induction in Lean
%%%
tag := "using-crush-induction"
%%%

lean-crush does not discover induction schemes.
Perform induction or case analysis in Lean and use `crush` as the case solver:

```lean
inductive Unary where
  | zero
  | succ (n : Unary)

@[crush_unfold]
def Unary.add : Unary → Unary → Unary
  | x, .zero => x
  | x, .succ y => .succ (Unary.add x y)

theorem Unary.zeroAdd (x : Unary) :
    Unary.add .zero x = x := by
  induction x with
  | zero => crush
  | succ x ih => crush [ih]
```

# Supported Data
%%%
tag := "using-crush-supported-data"
%%%

The built-in translator handles:

* propositional and equality reasoning;
* `Nat` and `Int` arithmetic, including canonical divisibility;
* bitvectors with statically known widths, Booleans, strings (length, append,
  emptiness, and String-pattern prefix/suffix/containment), and supported
  inductive datatypes;
* function values through defunctionalization, or native higher-order cvc5;
* finite Lean arrays with logical length and SMT array data.

`Nat` uses SMT integers with nonnegativity constraints and guards preserving
natural subtraction and division semantics. A symbolic width in `BitVec n`
stays opaque; `n > 0` alone does not give SMT a concrete bitvector width.

String and concrete-width bitvector operations use their SMT theories:

```lean
example (start suffix : String) :
    start.length ≤ (start ++ suffix).length := by
  crush

example (x : BitVec 16) : x ^^^ x = 0 := by
  crush
```

Finite arrays support `replicate`, `size`, bounded/defaulting/optional indexing,
`set`, `setIfInBounds`, `set!`, `push`, `pop`, `swap`,
`swapIfInBounds`, `isEmpty`, `back!`, and `back?`.
Their read-over-write behavior is handled directly by SMT array theory:

```lean
example (xs : Array Int) (i : Nat) (value : Int)
    (_hi : i < xs.size) :
    (xs.set! i value)[i]! = value := by
  crush

example (xs : Array Int) (value : Int) :
    (xs.push value).size = xs.size + 1 := by
  crush
```

Operations that copy a symbolic range, such as `append`, `extract`, `map`, and
`filter`, generally require a lemma or a custom lowering because their exact
encoding is quantified element-by-element.

# Choosing a Proof Policy
%%%
tag := "using-crush-proof-policy"
%%%

The default `crush.trust "trust"` closes solver `unsat` results with
`Crush.crushSorry`. For checked proofs, use:

```
set_option crush.backend "cvc5"
set_option crush.trust "reconstruct"
```

The default reconstruction mode, `"auto"`, tries Alethe replay and then proves
the goal from the unsat core with Lean tactics. Use `"alethe"` to require
certificate replay, or `"core"` for core reconstruction alone. Z3 supports the
core path; Bitwuzla currently supplies neither cores nor certificates.

`crush.trust "reconstructOrTrust"` allows an axiom-backed fallback with a
warning, except in strict Alethe mode. Inspect `#print axioms` to audit the
result. The {ref "configuration-reconstruction"}[configuration reference]
explains early proofs, strict Alethe behavior, and optional native decision
procedures.

# Complete Integrations

Three downstream branches show lean-crush integrated into larger verification
projects rather than isolated examples:

* [Loom's `crush-backend` branch](https://github.com/AD1024/loom/tree/crush-backend)
  uses lean-crush as a proof backend for generated verification conditions.
* [Velvet's `crush-backend` branch](https://github.com/AD1024/velvet/tree/crush-backend)
  applies the backend to Dafny-style imperative verification conditions,
  including arrays and quantified invariants.
* The [Cedar `crush-backend` branch](https://github.com/AD1024/cedar-spec/tree/crush-backend)
  includes a
  [`CedarCrushCaseStudy`](https://github.com/AD1024/cedar-spec/blob/crush-backend/cedar-lean/CedarCrushCaseStudy.lean)
  module built on `Cedar.Thm`. It uses `crush` as a kernel-reconstructed leaf
  tactic in Cedar foundation proofs.

These branches illustrate dependency setup and the lemmas connecting generated
VCs to SMT translation. Cedar builds on the
[upstream specification](https://github.com/cedar-policy/cedar-spec).

# Acknowledgements

The extracted type-matching case study in
`Test/CaseStudies/StrataUnification.lean` builds on
[Strata](https://github.com/strata-org/Strata), particularly its Lambda type
matcher and associated soundness, completeness, and occurs-check proofs.
