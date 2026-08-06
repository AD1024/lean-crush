# Cedar Evaluation

This document records an August 2026 evaluation of `lean-crush` against the
[`cedar-spec`](https://github.com/cedar-policy/cedar-spec) Lean proof corpus. It
focuses on concrete translation bugs, practical proof boundaries, and proposed
implementation work. It is an engineering report, not user-facing documentation.

## Scope

The evaluated Cedar tree contains approximately:

- 71,897 lines under `Cedar/Thm`
- 1,170 theorem and lemma declarations
- 11,521 uses of `simp`
- 2,297 uses of `cases`
- 1,881 uses of `rw`
- 175 uses of `omega`
- 140 uses of `induction`
- 33 uses of `grind`

The dominant proof shape is structural decomposition followed by a small
first-order or arithmetic obligation. This is a good fit for `crush` only after
Lean has exposed the relevant constructors, branches, and recursive hypotheses.

All successful experiments below used:

```lean
set_option crush.trust "reconstruct"
```

except the solver-timeout retry, which also timed out under trusted mode. This
distinguishes practical proof support from cases that only close through
`Crush.crushSorry`.

The evaluation used Cedar at Lean 4.31.0 and `lean-crush` at Lean 4.32.2. A
scratch Cedar copy was advanced to 4.32.2; neither source repository was changed
by the experiments.

## Results Summary

`crush` works well as a leaf tactic after native Lean preprocessing:

- `IsSoundPolicySlice` transitivity closes after unfolding the predicate and
  rewriting list subset to its pointwise definition.
- Cedar's `evaluatePolicy_ok_implies_env_some` and an authorization
  decision-condition lemma close after `simp only` plus one native `split`.
- A `List.Forall2` induction closes its nontrivial cons branch with `crush`.
- Several Cedar `Int64`/`BitVec` range, overflow, negation, and list-length
  obligations close with reconstruction.

It is not yet reliable as an end-to-end replacement for Cedar's structural proof
scripts. The confirmed gaps are listed below in priority order.

## 1. Generic overloaded operators emit ill-sorted SMT

**Priority:** P0

**Status:** Fixed after the evaluation. Structural arithmetic now requires a
homogeneous `Nat` or `Int` carrier after bit-vector and string dispatch. Other
canonical instances fall back to uninterpreted applications. A pre-solver SMT
sort checker validates core theory operators and declared symbols, and the generic
`LT` reproduction is pinned under reconstruction in `Test/Regression.lean`.

The structural translator maps `LT.lt` to SMT `<` whenever the typeclass argument
is canonical. Canonicality is necessary but not sufficient: the canonical
instance may be for a user-defined type whose SMT sort is uninterpreted.

Minimal reproduction:

```lean
import Crush

set_option crush.trust "reconstruct"

theorem generic_lt_substitution {alpha} [LT alpha] {x y : alpha}
    (hxy : x < y) (heq : x = y) (hirr : Not (y < y)) : False := by
  crush
```

The generated script declares `<` at `(Int, Int) -> Bool` and then applies it to
the uninterpreted sort for `alpha`:

```text
Sort mismatch at argument #1 for function
(declare-fun < (Int Int) Bool) supplied sort is s_1
```

The confirmed failure is `LT.lt`, but the same audit is required for every
overloaded structural lowering currently selected by head and canonical instance:
`LE`, `GE`, `GT`, `Neg`, `HAdd`, `HSub`, `HMul`, `HDiv`, `HMod`, `max`, and `min`.

### Proposed fix

Make theory lowering type-directed:

1. Check the carrier and result types before emitting an SMT theory operator.
2. Emit integer arithmetic only for `Nat` and `Int`.
3. Continue to let the existing bit-vector and string dispatchers claim their
   carriers first.
4. Fall back to `defaultApp` for every other carrier, preserving the typeclass
   instance as part of the uninterpreted application.

The check should be centralized rather than repeated in each pattern. For
example, `arithmeticCarrier?` can classify the application as integer,
bit-vector, string, or unsupported before `structural?` selects an operator.

Add an SMT sort-checking pass before printing or invoking a solver. `SMT.Term` is
currently structurally typed but does not carry enough static sort information to
prevent malformed applications. A lightweight checker over emitted declarations
would turn this class of bug into an internal translation error with the source
Lean expression attached.

### Regression tests

- Pin the generic `LT` reproduction in `Test/Regression.lean`.
- Add canonical instances for a small custom type for arithmetic, negation,
  comparison, `max`, and `min`; each must degrade to an uninterpreted symbol
  rather than emitting malformed SMT.
- Retain positive tests for `Nat`, `Int`, and `BitVec`.

## 2. Higher-order application can reference an invalid SMT symbol

**Priority:** P0

**Status:** Fixed after the evaluation. Non-symbol function heads now route
through the inferred arrow sort, partial applications are materialized as function
values, and fallback declarations are keyed by their complete instantiated
signature. The Cedar `Except.bind` shape now produces valid, sort-checked scripts
in defunctionalized and native modes. After the P1 monomorphization fix below, the
exact theorem also closes end-to-end on the default defunctionalized backend under
reconstruction. Because an explicit `crush [...]` list restricts premise selection,
the invocation includes the local hypotheses explicitly:

```lean
crush [Except.bind_ok, Except.bind_err, *]
```

Cedar's generic `Except.bind` workhorse is representative:

```lean
theorem bind_ne_error {alpha beta epsilon}
    {r : Except epsilon alpha}
    {f : alpha -> Except epsilon beta}
    {e : epsilon}
    (hr : r ≠ .error e)
    (hf : ∀ a, r = .ok a -> f a ≠ .error e) :
    (r >>= f) ≠ .error e := by
  crush [Except.bind_ok, Except.bind_err]
```

Translation produces invalid SMT containing an application like:

```text
unknown constant toBind_22 (Fn_40 s_52)
```

Native case analysis avoids the higher-order encoding and succeeds:

```lean
cases r <;>
  simp only [Except.bind_ok, Except.bind_err] at * <;>
  crush
```

### Proposed fix

Unify application translation around the inferred type of the function-valued
head. `hoTerm?` currently has a special path for a bound free variable, while
other function-valued heads can reach `defaultApp`. The application encoder
should instead:

1. Infer the head's arrow shape for every application.
2. Use direct first-order application only for a fully applied, first-order
   constant.
3. Route lambdas, bound variables, partial applications, projections, lets, and
   other function-valued terms through the arrow sort's `app` symbol.
4. Consume application spines consistently so partial and later full
   applications use the same instantiated arrow sort.
5. Ensure every closure and `app` symbol is declared before use.

The pre-solver sort checker proposed in issue 1 should also verify function
application arity and argument sorts. That catches this failure without relying
on backend-specific parser diagnostics.

### Regression tests

- Add Cedar's `bind_ne_error` shape to `Test/HigherOrder.lean`.
- Test a function argument returning a parametric datatype.
- Test a partially applied function that is later passed and invoked.
- Run each test in defunctionalized and cvc5 native higher-order modes.

## 3. Monomorphization recursively invents irrelevant nested types

**Priority:** P1

**Status:** Fixed after the evaluation. Monomorphization now derives substitutions
by matching each fact's structured type patterns and same-head type arguments
against the query. Bare type binders are only fallback evidence. Generated shapes
carry the lineage of facts that produced them, so cross-fact saturation remains
available but no fact can consume evidence from a dependency cycle containing
itself.

The original `Except.isOk` reproduction now completes under reconstruction in
82 ms on the evaluation machine. It generates 3 lemma instances and a 21-line,
1,220-byte SMT-LIB script containing one `Except` datatype, with no nested
`Except` types and no exhausted bound. The Cedar `Except.bind_ne_error` shape also
closes directly under reconstruction.

Unfolding small polymorphic definitions can generate hundreds of irrelevant
types. For example:

```lean
theorem except_isOk_iff_exists {x : Except epsilon alpha} :
    Except.isOk x ↔ ∃ a, x = .ok a := by
  crush u[Except.isOk, Except.toBool]
```

The generated instances include increasingly nested types such as:

```text
Except Bool Bool
Except Bool (Except Bool Bool)
Except (Except Bool Bool) (Except Bool Bool)
...
```

A similar expansion occurs when an unspecialized `List.Subset.trans` is supplied
to a goal about `List.Equiv`: `List alpha`, `List (List alpha)`, and deeper
instantiations are fed back into the candidate set.

The immediate cause is the saturating candidate loop in
`Translation/Monomorphize.lean`: every generated instance contributes all of its
ground type subterms as candidates for every polymorphic fact. A fact about a type
constructor can therefore create a larger candidate that causes another instance
of itself indefinitely, until fuel is exhausted.

### Implemented fix

Replace Cartesian candidate saturation with type-pattern matching:

1. Index polymorphic facts by the constants and type constructors in their
   proposition.
2. Match a fact's type patterns against applications already present in the
   fixed query (goal, hypotheses, and explicit monomorphic facts).
3. Derive binder substitutions by unification. For a fact mentioning
   `Except epsilon alpha`, a query occurrence of `Except String Int` should yield
   exactly `epsilon := String` and `alpha := Int`.
4. Track the producer lineage of generated type and application shapes. A fact
   cannot consume evidence whose lineage already contains that fact, preventing
   both direct recursion and mutual cycles.
5. Permit cross-fact saturation only through pattern matches; generated types are
   never fed independently into every binder.
6. Keep fuel and round limits as safety bounds, not as the primary termination
   mechanism.

### Regression tests

- `Except ε α` produces exactly one instance for a query at
  `Except String Int`.
- `List.Subset.trans` produces exactly one instance at the goal's element type.
- A fact-order-sensitive cross-fact case produces exactly two instances, proving
  that generated `List Int` evidence can activate a second fact without recursive
  nesting.
- The polymorphic list and Cedar `Except.bind` proofs close under reconstruction.

## 4. Equation-based unfolding does not reliably connect to the goal

**Priority:** P1

For Cedar's `List.Equiv`, this form can produce a countermodel even when both
subset directions are available:

```lean
crush u[List.Equiv]
```

The direct Lean transformation works:

```lean
unfold List.Equiv at *
have hac := List.Subset.trans h1.left h2.left
have hca := List.Subset.trans h2.right h1.right
crush [hac, hca]
```

`u[...]` currently adds equation lemmas as solver facts. That leaves correctness
dependent on monomorphization, symbol identity, and quantifier instantiation.
Direct unfolding instead rewrites the exact applications before translation.

### Proposed fix

Add a selected-definition normalization phase before monomorphization:

1. Rewrite collected propositions with equation lemmas requested by `u[...]` or
   `@[crush_unfold]`.
2. Preserve proof provenance by constructing proofs of rewritten hypotheses with
   `Eq.mp`/`Iff.mp` or Lean's simplifier result.
3. Rewrite the goal through an equivalent target before negating it.
4. Keep equation facts only for applications that cannot be reduced syntactically.

This makes `crush_unfold` behave like its name: expose definitions in the actual
query rather than ask the SMT solver to discover every rewrite.

### Regression tests

- `List.Equiv.trans` should close with `crush u[List.Equiv]`.
- The same test should close with a local `crush_unfold` attribute.
- Verify that recursive equations are applied only at matching calls and remain
  fuel bounded.

## 5. Match and recursor semantics are lost without native splitting

**Priority:** P1

Cedar defines:

```lean
def hasError (policy : Policy) (request : Request) (entities : Entities) : Bool :=
  match evaluate policy.toExpr request entities with
  | .ok _ => false
  | .error _ => true
```

This proof fails:

```lean
crush u[hasError]
```

The encoding leaves generated match/closure constants effectively
uninterpreted, allowing a countermodel inconsistent with Lean's match semantics.
The following succeeds with reconstruction:

```lean
intro h
unfold hasError at h
split at h <;> crush
```

### Proposed fix

Implement bounded match elimination before SMT translation. There are two viable
stages:

1. Short term: use Lean's native match splitter on residual matches over supported
   finite datatypes, then run `crush` on every generated branch.
2. Longer term: lower recursors over supported SMT datatypes to tester/selector
   `ite` expressions, preserving constructor semantics in one SMT query.

The preprocessing approach fits Cedar better because its proofs already rely on
`split` and `cases`, and it also improves reconstruction by leaving Lean with
ordinary branch goals. It must have a branch/fuel limit to avoid exponential case
explosion.

### Regression tests

- `hasError -> exists error` should close with `crush u[hasError]`.
- Add matches returning `Prop`, `Bool`, and a datatype.
- Add nested matches and pin the branch limit behavior.

## 6. Linear-looking 64-bit addition times out

**Priority:** P2

After Cedar's existing simplification, these reconstructed obligations pass:

- `BitVec.toInt` lower and upper bounds
- overflow equivalence
- in-range negation
- `List.length_removeAll_le`

The analogous in-range addition theorem does not:

```lean
simp only [BitVec.toInt_eq_toNat_cond, Nat.reducePow, Int.reduceNeg,
  BitVec.toNat_add, Int.natCast_emod, Int.natCast_add] at *
split <;> crush
```

Z3 still returns `unknown` due to timeout at 10 seconds and 30 seconds. Trusted
mode does not change the result, so reconstruction is not the bottleneck. In an
isolated retry, cvc5 closes the same theorem with reconstruction in approximately
5.5 seconds. Cedar's original `omega` proof is immediate. This is therefore both
a backend-selection and normalization issue, not a fundamental solver limitation.

The residual formula combines signed range facts, casts, and modulus by `2^64`.
Although the intended argument is linear, the emitted modulo encoding sends the
solver into a much harder search.

### Proposed fix

Use a portfolio of cheap normalization before general SMT solving:

1. Normalize casts and powers at closed widths.
2. Rewrite `x % m = x` when local bounds establish `0 <= x` and `x < m`.
3. Preserve `BitVec` operations in the bit-vector theory longer instead of
   expanding them to integer modulus where possible.
4. Add an optional backend portfolio or retry policy; this case is a concrete
   example where cvc5 succeeds and Z3 times out.
5. Try Lean's `omega` as a fast arithmetic finisher before spawning SMT for an
   arithmetic-only residual.
6. Record solver and phase profiling for timeouts so translation growth and
   backend search are distinguishable.

Add the Cedar addition theorem as a performance regression with a realistic
timeout, not merely as a correctness test.

## 7. Package dependencies block adoption

**Priority:** P2

Cedar is pinned to Lean 4.31.0 while `lean-crush` is pinned to Lean 4.32.2.
Additionally, `lean-crush` requires Mathlib only for one case-study module, but
that requirement pulls Mathlib and its Batteries revision into every downstream
project. Cedar has its own direct Batteries pin, causing a dependency conflict.

This is independent of proof capability: users cannot evaluate the tactic in the
real project until the package graph and toolchains align.

### Proposed fix

1. Move the Mathlib case study into a separate Lake package so the core
   `lean-crush` library has no Mathlib dependency.
2. Keep core tests on Lean and Batteries APIs only.
3. Add downstream fixture CI projects for supported Lean versions, including one
   project with a direct Batteries dependency.
4. Publish tags or compatibility branches for supported Lean releases when Lean
   metaprogramming API changes require source differences.
5. Document that the root project's toolchain compiles dependencies and list the
   versions covered by CI.

Removing the unconditional Mathlib dependency is the highest-value part: it
eliminates Cedar's Batteries conflict and makes cross-project testing much
lighter.

## Recommended Order

1. Fix type-directed overloaded operators and add SMT sort validation.
2. Fix general higher-order application routing.
3. Replace unrestricted monomorphization saturation with type-pattern matching.
4. Add selected-definition normalization and bounded native match splitting.
5. Add arithmetic preprocessing/portfolio behavior for the `BitVec` addition
   case.
6. Split Mathlib case studies from the core package and add downstream
   compatibility CI.

The first two items prevent malformed solver input. The next two address the
largest completeness failures seen in ordinary Cedar definitions. Arithmetic and
packaging then determine whether the tactic is fast and easy enough to adopt at
scale.
