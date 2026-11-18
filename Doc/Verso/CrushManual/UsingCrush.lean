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
crush only [h₁, lemma, f, -other, *] u[f, g] d[h] with [r₁, r₂] using (tactic₁; tactic₂)
```

Every component after `crush` is optional.
The `u[...]` and `d[...]` groups may be repeated and mixed.
The `with [...]` and `using` clauses customize checked reconstruction and, when
both are present, must appear in that order.

These clauses act at different stages:

* `[...]` adds propositions and definition equations to the SMT query, and
  `-name` removes a global lemma from those crush collects automatically.
* `only` drops the automatically collected lemmas.
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

## Hint Lists Add Facts

Hint lists follow `grind`: every form of the call includes every local
hypothesis whose type is a proposition, and a list only adds to them.

```lean
theorem orderedTrans (a b c : Int)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  crush
```

* Bare `crush` and `crush []` use all local hypotheses.
* `crush [h]`, for a local `h`, also gives `h` eager ground instantiation.
* `crush [foo]`, for a lemma, adds `foo` with eager ground instantiation.
* `crush [f]`, for a definition, adds the equations of `f`, as `u[f]` does.
* `crush [*]` gives every local hypothesis eager ground instantiation.
* `crush only [...]` drops the automatically collected lemmas:
  `@[crush_unfold]` and `@[crush_defeq]` equations, `@[reducible]` rewrites,
  and premise selection.
* `crush [-foo]` removes the global lemma `foo` from the automatic lemmas; for a
  definition, it removes the definition's equations.
* `crush [-h]`, for a local `h`, is an error that suggests `clear h`.

A list therefore never shrinks the query.
To exclude a hypothesis, `clear` it before the call:

```lean
theorem orderedTransWithoutNoise (a b c : Int)
    (hab : a ≤ b) (hbc : b ≤ c)
    (noise : ∀ x : Int, x < x + 100) : a ≤ c := by
  clear noise
  crush
```

Use `*` to give every local proposition eager ground instantiation, together
with named lemmas that are not already in the context:

```lean
theorem orderedTransWithContext (a b c : Int)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  crush [*, Int.le_trans]
```

Naming the same constant as `-foo` and as a hint, or in `u[...]` or `d[...]`,
is an error.
crush removes `-foo` from everything it collects itself, but it cannot hide it
from Lean code it runs without assembling, such as instance synthesis, simprocs,
and the tactics used in checked reconstruction.
When the finished proof still uses `foo` (or, for a definition `-f`, one of its
equation lemmas), crush warns, says how the goal was closed, and lists the
axioms `foo` depends on.
The kernel unfolding a definition by definitional reduction leaves no constant,
so the warning cannot see that use.

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
A hint list keeps premise selection; `crush only [...]` disables it, and
`-foo` keeps one theorem out of it.
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
natural subtraction and division semantics. A `BitVec n` whose width is not a
literal is refused; `n > 0` alone does not give SMT a concrete bitvector width.

Dependent types are refused with the error `cannot translate the dependent type`.
This covers a type that depends on a value, such as `Fin n`, `Fin 5` or `BitVec k`,
and a function type whose result type depends on its argument, such as
`(n : Nat) → β n`. An SMT sort cannot change with the value of a variable, so
translating these types could produce false proofs. Types that depend only on
other types, such as `List α`, are supported. So is `DecidableEq α`, which looks
dependent but has its own sound translation.

A structure or inductive whose field has such a type is not refused: it becomes
an opaque SMT sort, guarded unless it is known to be inhabited, so equality
reasoning about it still works but its fields are uninterpreted.
`structure Wrap where val : Fin 5`, `Option (Fin 5)` and `Array (Fin 5)` are
examples. The decision is made per query by translating the field sorts, so a
`@[crush_translate_sort]` handler for the field type makes the structure a
datatype again. A structure whose field type mentions an earlier field, such as
`structure Sig where α : Type; x : α`, is always opaque, because an SMT selector
has a single sort. The fallback is local: a structure with an opaque structure
as a field remains a datatype.

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

Checked reconstruction rejects transitive dependencies on `sorryAx` and
`Crush.crushSorry`, including definitions mentioned in the goal or hypotheses
used by a proof. If an admission blocks reconstruction, the error names the
forbidden axiom and the definition that depends on it. A later proof candidate
without that dependency can still succeed.

`crush.trust "reconstructOrTrust"` allows an axiom-backed fallback with a
warning, except in strict Alethe mode. When a candidate was rejected for an
admission, the warning reports that dependency instead of a generic search
failure. Inspect `#print axioms` to audit the
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
