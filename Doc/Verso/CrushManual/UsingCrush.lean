import VersoManual
import Crush

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Using the Tactic" =>
%%%
tag := "using-crush"
%%%

# Fact Selection

The full tactic grammar is:

```
crush [h₁, lemma, *] u[f, g] d[h]
```

A bare call includes every local `Prop` hypothesis.
An explicit list without `*` is a strict restriction: only the listed facts and
the negated goal are sent to the solver.
Adding `*` includes the complete local context as well as the named lemmas.

```lean
theorem orderedTrans (a b c : Int)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  crush [hab, hbc]

theorem orderedTransWithContext (a b c : Int)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  crush [*, Int.le_trans]
```

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

# Unfolding Definitions

An untranslated function is treated as uninterpreted.
That is sound, but its defining equations are unavailable unless they are
provided explicitly.
Use `u[...]` for all equation lemmas of a definition:

```lean
def addThree (x : Int) : Int := x + 3

example (x : Int) : addThree x > x := by
  crush u[addThree]
```

Use `d[...]` for the single definitional unfold equation.
This is useful for non-recursive wrappers and definitions whose complete
equation set is unnecessarily large:

```lean
def nonnegative (x : Int) : Prop := 0 ≤ x

example (x : Int) (h : nonnegative x) : x + 1 > 0 := by
  crush d[nonnegative]
```

For definitions that should always be visible, register the equations once:

```lean
@[crush_unfold]
def twice (x : Int) : Int := x + x

example (x : Int) : twice (x + 1) = twice x + 2 := by
  crush
```

`@[crush_defeq]` is the persistent counterpart to `d[...]`.
Both attributes are relevance-filtered, so a marked definition contributes
nothing to a query that cannot reach it.
Disable all automatic unfolding with `set_option crush.autoUnfold false`.

# Drive Induction in Lean

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

theorem Unary.addSucc (x y : Unary) :
    Unary.add x (.succ y) = .succ (Unary.add x y) := by
  induction x with
  | zero => crush
  | succ x ih => crush [ih]
```

# Supported Data

The built-in translator handles:

* propositional and equality reasoning;
* `Nat` and `Int` arithmetic, including canonical divisibility;
* bitvectors, Booleans, strings, and supported inductive datatypes;
* function values through defunctionalization, or native higher-order cvc5;
* finite Lean arrays with logical length and SMT array data.

Finite arrays support `size`, bounded/defaulting/optional indexing,
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

# Premise Selection

Bare `crush` can ask Lean's registered `LibrarySuggestions` engine for relevant
library theorems:

```
set_option crush.premises true
set_option crush.premises.max 32
```

Premise selection is deliberately opt-in.
An explicit `[...]` list disables it and remains a strict user-selected fact
set.

# Choosing a Proof Policy

Use the default `crush.trust "trust"` for fast exploratory proofs and applications
that accept the solver and translator in the trusted computing base.

Use `crush.trust "reconstruct"` when every result must be represented by a Lean
term checked by the kernel.
With cvc5, automatic reconstruction first tries Alethe certificate replay and
then the core-directed finisher ladder.
With Z3 or Bitwuzla, the core-directed path is available.

Use `crush.trust "reconstructOrTrust"` when reconstruction is preferred but a
visible, axiom-backed fallback is acceptable.

# Complete Integrations

Two downstream branches show lean-crush integrated into larger verification
projects rather than isolated examples:

* [Loom's `crush-backend` branch](https://github.com/AD1024/loom/tree/crush-backend)
  uses lean-crush as a proof backend for generated verification conditions.
* [Velvet's `crush-backend` branch](https://github.com/AD1024/velvet/tree/crush-backend)
  applies the backend to Dafny-style imperative verification conditions,
  including arrays and quantified invariants.

These branches are useful references for dependency setup, tactic invocation,
and the lemmas needed at the boundary between a verification-condition
generator and SMT translation.
