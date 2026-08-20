import VersoManual
import Crush

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Overview" =>
%%%
tag := "overview"
%%%

lean-crush is a leaf-proof tactic for goals that become constraint problems
after the surrounding proof has exposed the right facts.
It translates Lean propositions to SMT-LIB, invokes an external solver, and
reports the solver outcome. An `unsat` result becomes a Lean proof according to
the selected trust policy; `sat` reports a model and `unknown` leaves the goal
open.

It is most useful for arithmetic, equality propagation, finite datatypes,
arrays, quantified facts, and combinations of these theories.
It does not replace induction, theorem selection for an entire library, or
domain-specific proof decomposition.

For installation, solver requirements, and a first proof, continue to
{ref "getting-started"}[Getting Started].

# What Happens During `crush`

A tactic invocation passes through the following stages:

1. *Collect facts.* Select local hypotheses, explicit lemmas, unfolding
   equations, and optionally library premises.
2. *Normalize.* Apply proof-producing rewrites that expose supported
   operations and constructor structure.
3. *Specialize.* Monomorphize polymorphic facts and generate bounded ground
   instances of quantified facts.
4. *Translate.* Lower Lean terms to SMT sorts, terms, declarations, and
   axioms. Unsupported functions remain uninterpreted.
5. *Solve.* Ask Z3, cvc5, or Bitwuzla whether the facts and negated goal are
   inconsistent.
6. *Discharge.* Trust the `unsat` result, replay a cvc5 Alethe certificate, or
   reconstruct a proof from the unsat core.

This separation matters when diagnosing a failure.
A missing equation is a collection or translation problem; an `unknown` result
is a solver problem; and an `unsat` result followed by failure is a
reconstruction problem.
See {ref "troubleshooting-classify"}[Classify the Failure First] for the
stage-by-stage diagnostic workflow and
{ref "configuration-diagnostics"}[Diagnostics] for profiling and traces.

# Constraint Solving

## Arithmetic and Equality

lean-crush combines arithmetic with equality and uninterpreted-function
congruence.
Use a bare call when all relevant propositions are already local:

```lean
example (f : Int → Int) (a b limit : Int)
    (hab : a = b) (hb : b ≤ limit) :
    f a = f b ∧ a ≤ limit := by
  crush
```

The solver treats an unsupported `f` as an uninterpreted function.
That is enough for congruence, such as deriving `f a = f b` from `a = b`, but
not enough to reason from the body of `f`.
Expose equations or register a lowering when the implementation matters.
The {ref "using-crush-supported-data"}[Supported Data] section lists the
built-in theory surface, while
{ref "using-crush-definitions"}[Exposing Definitions] explains how to reveal
user-defined functions.

## Inductive Datatypes and Arrays

The translator supports constructor reasoning for ordinary inductive datatypes
and a finite representation of Lean arrays.

```lean
inductive OverviewPacket where
  | packet (sequence : Int) (accepted : Bool)

example (x y : Int) (p q : Bool)
    (h : OverviewPacket.packet x p =
      OverviewPacket.packet y q) :
    x = y ∧ p = q := by
  crush
```

Array reads and local updates use SMT Array theory:

```lean
example (xs : Array Int) (i : Nat) (value : Int)
    (hi : i < xs.size) :
    (xs.set! i value)[i]! = value := by
  crush
```

Use Lean induction or case analysis for recursive proofs, then invoke `crush`
on each case.
Operations that transform an entire symbolic range, such as `Array.map` or
`Array.filter`, usually need a theorem or custom lowering rather than a larger
solver timeout.
See {ref "using-crush-induction"}[Drive Induction in Lean] for recursive proofs,
{ref "using-crush-supported-data"}[Supported Data] for built-in array
operations, and {ref "extending-arrays"}[Extending Finite Arrays] for custom
operations over the canonical array encoding.

# Controlling Knowledge

## Local and Explicit Facts

Bare `crush` sends every local proposition.
An explicit list without `*` is a strict restriction, while `*` adds all local
propositions to the named facts:

```lean
example (a b c : Int) (hab : a ≤ b) (hbc : b ≤ c)
    (_noise : a * a ≥ 0) : a ≤ c := by
  crush [hab, hbc]

example (a b c : Int) (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c := by
  crush [*, Int.le_trans]
```

Use explicit lists for reproducibility and to keep irrelevant quantifiers out
of the query.
Use `crush.premises` instead when a bare call should ask Lean's
`LibrarySuggestions` engine for likely library theorems.
Writing any explicit list disables premise selection.
See {ref "using-crush-facts"}[Choosing Solver Facts] for the exact behavior of
bare calls, restricted lists, `*`, explicit lemmas, and premise selection.

## Polymorphism and Quantifiers

lean-crush has two related specialization passes:

* *Monomorphization* replaces polymorphic theorem uses with concrete type
  instances found in the query.
* *Ground instantiation* applies quantified propositions to relevant concrete
  terms after their types are fixed.

The following theorem is polymorphic in `α` and quantified over three values:

```lean
opaque OverviewBefore {α : Type} : α → α → Prop

axiom overviewBeforeTrans {α : Type} :
  ∀ a b c : α,
    OverviewBefore a b →
    OverviewBefore b c →
    OverviewBefore a c

example (a b c : Int)
    (hab : OverviewBefore a b)
    (hbc : OverviewBefore b c) :
    OverviewBefore a c := by
  crush [overviewBeforeTrans, hab, hbc]
```

Monomorphization first specializes `overviewBeforeTrans` at `Int`.
Ground instantiation then applies that specialized proposition to `a`, `b`, and
`c`.
The passes are bounded to prevent search explosions.
Raise `crush.mono.*` only for missing type specializations, and
`crush.inst.*` only for missing term applications.
Increasing one does not compensate for exhaustion in the other.
The {ref "configuration-monomorphization"}[Monomorphization] and
{ref "configuration-instantiation"}[Ground Instantiation] sections document
their separate bounds, warnings, and fallback behavior.

# Higher-Order Terms

Function values, lambdas, and partial applications do not have to be removed
manually:

```lean
example (applyAtTwo : (Int → Int) → Int)
    (h : ∀ f, applyAtTwo f = f 2) :
    applyAtTwo (fun x => x + 3) = 5 := by
  crush
```

The default `crush.ho.mode "defunctionalize"` converts function values to
first-order closure values without requiring native higher-order solver support.
The resulting query must still fit the selected backend's ordinary theory and
quantifier support.
`crush.ho.mode "native"` preserves function sorts and application for cvc5's
higher-order engine:

```lean
set_option crush.backend "cvc5"
set_option crush.ho.mode "native"
```

Native mode can give cvc5 more direct higher-order structure, but it is
backend-specific and certificate support is narrower.
Defunctionalization is the portable default and is usually the better starting
point.
See {ref "configuration-higher-order"}[Higher-Order Translation] for mode
selection, backend restrictions, and reconstruction implications.

# Trust and Checked Proofs

`crush.trust` decides what an SMT `unsat` result is allowed to do:

* `"trust"` closes with the visible `Crush.crushSorry` axiom. It is fastest and
  makes the solver and translation part of the trusted base.
* `"reconstruct"` requires a proof checked by Lean's kernel and fails if none
  can be built.
* `"reconstructOrTrust"` reconstructs when possible, then warns before using
  the axiom as a fallback.

```lean
set_option crush.trust "reconstruct" in
example (x y : Int) (hxy : x = y) (hy : y = 4) :
    x = 4 := by
  crush
```

`crush.reconstruct` selects a reconstruction algorithm only when the trust
policy requests reconstruction:

* `"alethe"` replays cvc5's certificate step by step.
* `"core"` asks Lean tactics to re-prove the result from an SMT unsat core,
  available from Z3 and cvc5 but not currently from Bitwuzla.
* `"auto"` tries Alethe first and then core reconstruction.

These are separate choices.
Under `crush.trust "trust"`, `"auto"` and `"core"` do not change how the goal is
discharged because no checked proof is requested.
The stricter `"alethe"` setting is still validated and therefore still requires
the cvc5 backend.
See {ref "using-crush-proof-policy"}[Choosing a Proof Policy] for the user
workflow, {ref "configuration-reconstruction"}[Trust and Reconstruction] for
the complete option semantics, and
{ref "using-crush-reconstruction"}[Helping Checked Reconstruction] for
per-invocation recovery mechanisms.

# Extensibility

Different extension points affect different pipeline stages:

* Use `u[f]`, `d[f]`, `@[crush_unfold]`, or `@[crush_defeq]` when ordinary Lean
  equations are enough.
* Use `crush_map`, `@[crush_lower]`, or `@[crush_translate]` when the solver
  should see a custom SMT operation.
* Use `crush_map_sort` or `@[crush_translate_sort]` when a Lean type itself
  should use an SMT theory sort.
* Use `with [...]`, `using`, or `@[crush_reconstruct]` when solving succeeds but
  checked core reconstruction needs Lean-specific help.
* Use `register_crush_replay` when a custom encoding introduces certificate
  terms or Alethe inference rules that replay cannot decode.

The simplest extension is usually an equation:

```lean
@[crush_unfold]
def overviewOffset (x : Int) : Int :=
  x + 5

example (x : Int) : overviewOffset x > x := by
  crush
```

A lowering is preferable when unfolding is expensive, produces recursive
quantifiers, or when a Lean operation corresponds directly to an SMT theory
operator.
Reconstruction extensions do not change the SMT query, while translation
extensions do.
Start with {ref "extending-choose"}[Choosing an Extension Point].
The detailed sections cover {ref "extending-equations"}[equation-based support],
{ref "extending-mappings"}[direct symbol mappings],
{ref "extending-targeted"}[targeted],
{ref "extending-result"}[result-indexed], and
{ref "extending-general"}[general term handlers],
{ref "extending-sorts"}[sort handlers],
{ref "extending-arrays"}[finite-array extensions],
{ref "extending-reconstruction"}[core reconstruction rules], and
{ref "extending-alethe"}[Alethe replay extensions].

# Recommended Workflow

For a new proof:

1. Try bare `crush`.
2. Restrict or extend the fact set explicitly.
3. Expose only the definitions needed by the argument.
4. Run locally with `crush.trust "trust"` to separate solving capability from
   reconstruction capability.
5. Enable `crush.profile` and inspect SMT-LIB before increasing search bounds.
6. Add a translation or reconstruction extension only at the stage where the
   gap occurs.

The {ref "using-crush-syntax"}[Tactic Syntax] section provides the complete
grammar.
For failures, use {ref "troubleshooting-classify"}[the diagnostic workflow],
then inspect {ref "troubleshooting-smt"}[the generated SMT-LIB] or
{ref "troubleshooting-reconstruction"}[reconstruction failures] as appropriate.
