# lean-crush

**An SMT hammer for Lean 4.** Write `by crush` and an SMT solver does the tedious part of
the proof for you.

Read the [lean-crush user manual](https://ad1024.github.io/lean-crush/) for installation,
configuration, extension APIs, and complete examples.
Maintainers should also read the
[optimization and search-heuristic guide](Doc/OPTIMIZATIONS.md) before changing
reconstruction or instantiation bounds.

Lean's own automation is strong at goals that follow by rewriting and case analysis. It is
weaker at goals that are really just *constraint solving* — chains of arithmetic
inequalities, equalities pushed through uninterpreted functions, bitvector identities,
combinations of a dozen hypotheses where only three matter. SMT solvers are very good at
exactly that. lean-crush hands them the goal and turns the answer back into a Lean proof.

Three things set it apart from existing Lean–SMT bridges:

- **Higher-order goals survive the trip.** Functions passed as arguments, partial
  applications, and lambdas are the point at which other bridges stop; lean-crush eliminates
  them on the way out (or hands them to cvc5's higher-order solver directly).
- **The solver's answer can be checked, not just trusted.** lean-crush can replay cvc5's
  proof certificate inference by inference, or reconstruct the argument from the unsat core,
  producing a proof the Lean kernel verifies. When it trusts instead, it says so in
  `#print axioms`.
- **You can teach it your own constants.** The Lean-to-SMT mapping is open: one line for
  simple cases, or a metaprogram for full control — the same API the built-in theories use.

```lean
example (f : Int → Int) (a b : Int) (h : a = b) : f a = f b := by crush

example (x y : Int) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by crush

example (g : Int → Int) (x : Int) (h : ∀ z, g z = z + 1) : g (g x) = x + 2 := by crush

-- a function taken as an argument, and a lambda passed to it
example (g : (Int → Int) → Int) (h : ∀ k, g k = k 1) : g (fun x => x + 1) = 2 := by crush
```

When the solver satisfies the encoded facts, you get the model instead of a failure:

```lean
example (x : Int) : x + 1 = x := by crush
-- crush: could not prove the goal — the solver found a model:
--   x := 0
-- The encoding is incomplete, so a model does not necessarily describe a Lean
-- counterexample.
```

## Install

Requires the Lean toolchain in [`lean-toolchain`](lean-toolchain) and at least one solver on
your `PATH` — `z3` (≥ 4.15.4), `cvc5` (≥ 1.3.4), or `bitwuzla`. CI pins z3 5.1.0 and
cvc5 1.3.4. z3 4.13 and older reject `sbv_to_int`,
which the translator emits for `BitVec.toInt`, so those goals report a refused command
there rather than a proof. z3 is the default and enough to start; cvc5 additionally enables
proof replay and native higher-order support.
Selecting a backend whose executable is not installed fails with that diagnosis and names
the backends this machine does have, rather than reporting a solver verdict.

Add to your `lakefile.lean`:

```lean
require crush from git "https://github.com/AD1024/lean-crush" @ "main"
```

Then `import Crush` and the `crush` tactic is available. The package has no third-party
Lean dependencies; Mathlib integration tests live in a separate package.

```sh
lake build              # the library
lake build Test.Smoke   # smoke tests (needs z3 for the round-trip)
```

Maintainers can run the optional Mathlib integration suite separately:

```sh
cd MathlibTest
lake exe cache get
lake build
```

## Using it

`crush` reads every hypothesis in context, so a bare call is usually what you want. To go
further:

```lean
crush [h, myLemma]   -- use exactly these facts (lemmas need not be in context)
crush [*, myLemma]   -- everything in context, plus a lemma
crush u[myFn]        -- unfold `myFn` via its equation lemmas
```

Explicit lemmas are also instantiated at relevant ground terms before SMT
translation. This lets one lemma create the term that triggers another, including
existential-witness chains that SMT E-matching cannot start on its own. The pass is
bounded by `crush.inst.fuel` and `crush.inst.rounds`. When Lean can simplify the
ground consequences to useful propositions without discarding terms needed as
witnesses, they replace the unrestricted quantifier and avoid solver instantiation
loops. Other lemmas remain quantified as fallbacks. Set either option to `0` to
disable this pass and send the original quantifiers directly.

Selected definitions are rewritten in the actual hypotheses and goal before SMT
translation; their equations also remain available as fallback solver facts. This
makes `u[...]` useful without depending entirely on SMT quantifier instantiation.

Mark a definition and its equations come along automatically, with no `u[…]` needed:

```lean
@[crush_unfold]
def myFn : Nat → Nat
  | 0 => 0
  | n + 1 => myFn n + 2
```

Predicates marked with Lean's standard `@[reducible]` attribute are also normalized
automatically, but their equations are not added as quantified SMT facts. Recursive
predicates use only constructor-specific rewrite equations; use `@[crush_unfold]`
when SMT also needs their quantified fallback.

You can also enable automatic unfolding for definitions from Lean or another library:

```lean
attribute [local crush_unfold] List.length

example (l : List Int) : l.length = 0 ↔ l = [] := by crush
```

Use `local` to keep the setting in the current section or file. Omit it when the setting
should be exported to modules that import yours. The same approach works for definitions
such as `Monotone` and `Function.Injective`.

`crush` proves goals, not inductions — so drive the induction yourself and let it close the
cases:

```lean
inductive N where | Z | S (n : N)

@[crush_unfold]
def N.add : N → N → N
  | x, .Z   => x
  | x, .S y => .S (N.add x y)

theorem zero_add (x : N) : N.add .Z x = x := by
  induction x with
  | Z => crush            -- @[crush_unfold] on N.add supplies its equations
  | S x ih => crush [ih]  -- feed the induction hypothesis as a fact
```

By default `crush` takes the solver at its word. To demand a proof the Lean kernel checks —
so the goal fails rather than closing if none can be built:

```lean
set_option crush.trust "reconstruct" in
theorem checked (x y : Int) (h1 : x = y) (h2 : y = 3) : x = 3 := by crush

#print axioms checked
-- 'checked' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A trusted SMT discharge records `Crush.crushSorry` in `#print axioms`. Some calls
close with a checked proof before reaching SMT, even under the default policy;
use `"reconstruct"` to require a checked proof when solving is needed too.

If SMT can prove a domain-specific fact but checked reconstruction needs a bridge theorem,
register that theorem for bounded reconstruction search:

```lean
inductive Phase where
  | initial
  | next (previous : Phase)

def Advances (source target : Phase) : Prop :=
  target = .next source

@[crush_reconstruct]
theorem advancesNext (phase : Phase) : Advances phase (.next phase) :=
  rfl
```

`@[crush_reconstruct]` affects only kernel-checked core reconstruction. It does not send
the theorem to SMT or participate in Alethe replay; use `crush [...]`,
`@[crush_unfold]`, or a lowering when the solver also needs the fact's semantics.
Rules are indexed by their conclusion and searched to a fixed depth, so rules for
unrelated datatypes are not added wholesale to `grind`.

Other behaviour is controlled by `set_option`s (`crush.backend`, `crush.timeout`, and
others); each carries its own documentation where it is declared.

Library premise selection is opt-in and uses Lean's registered
`LibrarySuggestions` engine:

```lean
set_option crush.premises true
set_option crush.premises.max 32
```

It applies to bare `crush` calls. An explicit `[...]` list remains a strict
restriction and disables automatic premise selection.

## How it works

The tactic collects your hypotheses together with the negation of your goal, translates that
package to SMT, and runs a solver under a strict time budget. If the package is
contradictory, your goal follows. If the solver instead finds a model, that model is your
counterexample.

Trusting that verdict is the fast path, and what hammers normally do. Building a real Lean
proof from it takes one of two routes:

- **replaying the solver's proof** — cvc5 can emit its refutation as a certificate, and
  lean-crush walks it one inference at a time, proving each in Lean. Since the solver
  already found the argument, each step is small, which reaches goals no single Lean tactic
  cracks in one shot. Replay covers propositional logic, EUF, integer and Nat arithmetic,
  strings, bitvectors, datatype injectivity, quantified formulas, and defunctionalized
  higher-order terms, including nested Alethe subproof blocks.
- **reconstructing from the unsat core** — the solver reports which few hypotheses actually
  mattered, and a Lean tactic redoes the argument from just those. This needs no
  certificate, but it does require a backend-provided unsat core. Z3 and cvc5 provide
  one; Bitwuzla currently does not.

Beyond plain logic and arithmetic, lean-crush covers bitvectors, string length,
append, emptiness, String-pattern prefix/suffix/containment, and your own
inductive types. It keeps
functions-as-arguments alive all the way to the solver — the case where Lean-to-SMT
bridges usually give up. Polymorphic lemmas are specialized to the types a goal
mentions, so a general lemma still applies to your concrete instance.

You can also teach it to translate your own constants, which is how the built-in theory
mappings are themselves written:

```lean
crush_map Nat.add => "+"
crush_map_sort Nat => "Int"
```

For pattern-based rules, use the same registration style as proof replay:

```lean
register_lowering term <<
  (Int.sign (term x)) =>
    (smt| (ite (> $x 0) 1 (ite (= $x 0) 0 (- 1))))
>>
```

The three forms share one pattern language and the existing attribute registries:

| Command | Matches | Registry | RHS value |
|---|---|---|---|
| `register_lowering term` | The Lean expression | `crush_lower` | `SMT.Term` |
| `register_lowering result-type` | Its complete inferred type | `crush_lower_result` | `SMT.Term` |
| `register_lowering sort` | The Lean type being translated | `crush_translate_sort` | `SMT.SSort` |

A bare argument `x` binds the original `Lean.Expr`. `(term x)` calls
`ctx.emitTerm` and binds an `SMT.Term`; `(sort α)` calls `ctx.emitSort` and
binds an `SMT.SSort`. `_` ignores one argument, and `(Constant patterns...)`
matches a nested constant application; `(Int)` therefore matches the exact
constant `Int`. `(term x : Int)` additionally matches the captured expression's
inferred type against the structural pattern `Int`.

Patterns match exact elaborated arities, including implicit type, instance, and
proof arguments. They do not insert implicit arguments or unfold definitions.
Capture names must be distinct. Add `with ctx` before `<<` to explicitly bind
the original `TranslationCtx` on the RHS; any binder name may be used, provided
it differs from the pattern captures. No context name is bound implicitly.
Result-type patterns inspect the complete inferred type,
without peeling dependent function binders. Use an attribute handler for more
complex matching. Each registration contains one pattern; multiple registrations
can share a head. Add `high`, `low`, or a numeric priority after the command kind.
General `crush_translate` handlers still run before these term lowerings.

The RHS may also be a pure helper call, a `TranslateM` computation, or a helper
returning `TranslateM (Option ...)` to decline with `none`:

```lean
register_lowering term with ctx <<
  (Int.sign x) => do
    let sx ← ctx.emitTerm x
    return (smt| (ite (> $sx 0) 1 (ite (= $sx 0) 0 (- 1))))
>>
```

Sort quotations use the expected `SMT.SSort` type, including inside helper
functions. For example, a parameterized map representation can use:

```lean
structure TotalMap (key value : Type) where
  get : key → value

register_lowering sort <<
  (TotalMap (sort key) (sort value)) => (smt| (Array $key $value))
>>
```

Result-type rules use a type pattern on the left and produce a *term* on the
right. With `register_lowering result-type with ctx`, the RHS can inspect
`ctx.fn` and `ctx.args` to distinguish the original
expressions sharing that type. As with attribute handlers, operation lowerings
must agree with the chosen sort representation and check overloaded dictionaries
before assigning built-in semantics. Registrations supply translations, not
proofs of their correctness. The `<< ... >>` fence reserves `>>`; put helpers
using that token in named definitions.

The original attributes remain available for full control:

```lean
@[crush_lower Int.sign]
def lowerSign : Crush.LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (ite (> $sx 0) 1 (ite (= $sx 0) 0 (- 1))))
```

Use `@[crush_lower_result T]` when the application head is unstable but the
result-family head is stable. The dispatcher first matches the immediate head of
the term's type; for a syntactic dependent function type, it peels binders and
matches the codomain head. Named aliases are separate keys, so the built-in
decision lowering registers both `Decidable` and `DecidableEq`. It represents
decision evidence with an axiomatized singleton SMT sort and lowers `decide p`
to `p`; equality decisions therefore become SMT equality without depending on a
particular procedure implementation. Pair a result lowering with a compatible
`@[crush_translate_sort]` handler whenever it changes representation.

The `(smt| ...)` quotation is a shallow embedding of SMT-LIB terms. Symbols,
applications, numerals, Booleans, and strings use SMT-LIB syntax; `$term` splices an
existing `Crush.SMT.Term`. The result is a structured term representation, not an
unchecked string; lean-crush sort-checks the final SMT script.

When a custom lowering emits an SMT operator that checked replay does not know,
register its inverse with the replay DSL:

```lean
def MultipleOfThree (x : Int) : Prop := x % 3 = 0

@[crush_lower MultipleOfThree]
def lowerMultipleOfThree : Crush.LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  return some (.app (.indexed "divisible" #[.inr 3]) #[← ctx.emitTerm x])

register_crush_replay term <<
  ((_ divisible (int divisor)) (term value : Int)) |
  (divisible (term divisor : Int) (term value : Int)) =>
    value % divisor = 0
>>
```

The two patterns accept indexed SMT-LIB and cvc5's normalized ordinary form.
`term`, `nat`, `int`, `string`, `atom`, `sexp`, `sort`, and `prop` introduce
typed Lean names for the right-hand side; `_` matches one item and a final `..`
matches the remainder. Alternatives must bind the same names.

Certificate inference rules are extensible in the same style:

```lean
register_crush_replay rule low <<
  (my_arithmetic_rule (term x : Int) (term y : Int) ..) =>
    by omega
>>
```

The tactic sees only the replayed premises, its captures, and the step target.
Every proof and generated auxiliary declaration is kernel-checked. Add `high`,
`low`, or a numeric priority after `term` or `rule` when handlers overlap.

Rule registrations can also use a typeclass-dispatched, metaprogrammed
condition:

```lean
structure RuleArgumentIs where
  expected : String

instance : Crush.ReplayCondition RuleArgumentIs where
  check condition ctx :=
    return ctx.args[0]? == some (.atom condition.expected)

def enabledRule : RuleArgumentIs where
  expected := "enabled"

register_crush_replay rule <<
  (my_conditional_rule ..) if enabledRule =>
    by exact True.intro
>>
```

The condition is not a proposition and creates no proof obligation.
It runs after pattern matching; `false` delegates to the next registration.
The `ReplayRuleContext` exposes the target, premises, raw arguments, and named
captures through `binding?`.

For dynamic matching, use `@[crush_replay "operator"]` on a
`Crush.ReplayTermHandler` or `@[crush_replay_rule "rule"]` on a
`Crush.ReplayRuleHandler`; returning `none` defers to the next handler. See
[`Test/AletheExtension.lean`](Test/AletheExtension.lean) for an Alethe-only
end-to-end example.

Array-backed operations can reuse Crush's finite Array representation instead of
reimplementing its length/data encoding:

```lean
def overwriteFirst {α : Type} (xs : Array α) (value : α) : Array α :=
  xs.setIfInBounds 0 value

@[crush_lower overwriteFirst]
def lowerOverwriteFirst : Crush.LoweringHandler := fun ctx => do
  let #[elem, xs, value] := ctx.args | return none
  let svalue ← ctx.emitTerm value
  Crush.withFiniteArray ctx elem xs fun view => do
    let data := (smt| (store $(view.data) 0 $svalue))
    let updated := view.mkValue view.length data
    return (smt| (ite (> $(view.length) 0) $updated $(view.value)))
```

`withFiniteArray` returns `none` if another sort handler has replaced Array's
representation, and inserts an SMT `let` so nested updates are not duplicated.
The built-in lowerings use this API for `replicate`, `size`, bounded/defaulting/optional
indexing, `set`/`setIfInBounds`/`set!`, `push`, `pop`, `swap`/
`swapIfInBounds`, `isEmpty`, `back!`, and `back?`.

## Limitations

- **No induction.** A goal needing an inductive hypothesis will not be solved merely by
  increasing the timeout. Drive the `induction` yourself and let `crush` close each case —
  that is the intended workflow.
- **Not every function translates.** Arithmetic, canonical divisibility, `Bool`, `String`,
  `BitVec`, and your own inductive types do; some library operations such as `Finset.card`
  do not, and an untranslated one becomes uninterpreted — so the solver reports a
  *counterexample*, not an error. Definitions such as `|·|`, `List.length`, and `Monotone`
  work after enabling `crush_unfold` as shown above. Otherwise, provide a suitable lemma,
  state the needed property directly, or add a custom lowering. Array operations that
  copy a symbolic range (`append`, `extract`, `map`, `filter`) still need lemmas or custom
  lowerings; unlike `push`/`pop`, they require quantified element-wise encodings.
  String replacement, character-pattern search, slice/position operations,
  numeric parsing, and lexicographic order are also untranslated: Lean's
  empty-pattern replacement differs from SMT `str.replace_all`, symbolic `Char`
  values do not yet have a codepoint encoding, positions are UTF-8 byte offsets,
  numeric parsers accept underscores, and SMT-LIB's string alphabet ends at
  `U+2FFFF` while Lean's does not.
- **A goal is only as strong as its premises.** A missing premise usually leaves the
  encoded negation satisfiable, and quantifiers can instead make the solver return
  `unknown` — so check the goal actually follows before blaming the solver.
- **Reconstruction is narrower than solving.** Under `crush.trust "reconstruct"`, some goals
  the solver proves cannot be replayed as a Lean proof. In particular, cvc5 1.3 does not emit
  Alethe certificates for finite-datatype exhaustiveness, finite-array reasoning, or native
  higher-order proofs, and rejects certificates containing signed bitvector-to-`Int`
  conversion; automatic mode may still reconstruct these from the unsat core.
  `"reconstructOrTrust"` falls back to the axiom with a warning when both checked paths fail.
  For bit-vector-heavy reconstruction, `crush.reconstruct.trustBvDecide true` enables
  `bv_decide` as an explicit native-code-trusting fallback. The resulting theorem names an
  auditable `_native.bv_decide.ax_*` dependency; the option is off by default, preserving
  kernel-only reconstruction.
  `crush.reconstruct.trustNativeDecide true` enables the broader `native_decide` fallback
  for finite or computational goals. It trusts Lean's native compiler, runtime, and all
  executable definitions reached by the decision procedure; accepted proofs expose an
  `_native.native_decide.ax_*` dependency. This option is also off by default.
- **Rough edges.** Indirectly recursive datatypes (`Rose` with a `List Rose` field) become an
  opaque sort; Alethe replay needs cvc5 ≥ 1.3.

## Relation to lean-auto

lean-crush is a from-scratch redesign in the spirit of
[lean-auto](https://github.com/leanprover-community/lean-auto). The three points above are
exactly where it diverges, and in each case lean-auto's limitation is visible in its source:
it reifies into a higher-order logic but then hard-fails (`"Higher order input?"`) on any
function-typed argument while emitting SMT; its Lean→SMT mapping is closed, so extending it
means forking; and its SMT backend has no proof reconstruction yet, either producing no
proof or closing the goal with the `autoSMTSorry` axiom.

## Examples and case studies

[`Test/`](Test/) has runnable examples across every supported theory, including recursive
functions and nested datatypes ([`Test/Recursive.lean`](Test/Recursive.lean)) and the harder
reconstruction cases for both routes
([`Test/AletheReplay.lean`](Test/AletheReplay.lean),
[`Test/ReconstructHard.lean`](Test/ReconstructHard.lean)).

[`Test/CaseStudies/`](Test/CaseStudies/) runs `crush` against lean-auto's test suite and
Loom/Velvet/Cashmere verification conditions. The optional
[`MathlibTest`](MathlibTest/) package checks Mathlib lemma statements restated at `Int`,
with operations that have *no* first-order translation pinned as expected failures so the
boundary is recorded rather than implied.

Complete downstream integrations are available in the
[Loom `crush-backend` branch](https://github.com/AD1024/loom/tree/crush-backend) and
[Velvet `crush-backend` branch](https://github.com/AD1024/velvet/tree/crush-backend).
They show lean-crush wired into verification-condition generation and used on
real array, arithmetic, and quantified proof obligations.

To reproduce the coverage comparison end to end -- every backend measured into
one directory, then the figures drawn from it -- run:

```sh
bash benchmark-coverage.sh --case_study all
```

That writes `BenchmarkResults/coverage-<timestamp>/`, with one subdirectory per
case study and the figures under `figures/`. Crush is measured in both lanes, so
the result carries the `Crush (SMT trusted)` and `Crush (kernel-checked)` series
together. Set `BACKENDS` to narrow it (the default is
`crush auto duper grind lean-smt`), and pass `--figures_only <directory>` to
redraw a finished run without measuring anything. Check the whole path first on
a single file, which takes minutes rather than hours:

```sh
BACKENDS=grind bash benchmark-coverage.sh --case_study Cashmere \
  --cases "CaseStudies/Cashmere/CashmereIncorrectnessLogic.lean"
```

The figures come from the same renderer that produced the published ones, so a
reproduction and the committed artifacts cannot drift apart. Timings depend on
the host and will not match ours; coverage should.

To measure one backend and case study on its own:

```sh
bash benchmark.sh \
  --case_study <all|LeanHammer|Velvet|Cashmere|PLean> \
  --with <crush|auto|duper|grind>
```

For example, run trusted Crush across all four case studies:

```sh
bash benchmark.sh --case_study all --with crush
```

[lean-smt](https://github.com/ufmg-smite/lean-smt) is a fifth backend. Only
the pinned LeanHammer tree requires it already; for the other corpora the
harness applies a recorded patch from
[`scripts/patches`](scripts/patches) that adds the dependency to the pinned
revision, then verifies that resolving it moved nothing else:

```sh
bash benchmark.sh --case_study all --with lean-smt \
  --smt_trees BenchmarkResults/trees
```

A lean-smt tree carries its corpus's Mathlib build plus lean-smt's, so
`--smt_trees` names a directory to keep them in between runs.

Run the trusted verification, Core reconstruction, Alethe reconstruction, and
portfolio comparison together with:

```sh
bash benchmark-crush-modes.sh --case_study all
```

Compare checked proof reconstruction between lean-smt, Crush's strict Alethe
replay, and Crush's reconstruction portfolio with:

```sh
bash benchmark-reconstruction.sh --case_study all \
  --smt_trees BenchmarkResults/trees
```

All three entry points fetch cached Lake artifacts when available and write
their normalized reports and figures under `BenchmarkResults/`. Regenerate
only the figures and tables from an existing result directory with:

```sh
bash benchmark.sh \
  --plot_only BenchmarkResults/reproduction-<timestamp>-<backend>

bash benchmark-crush-modes.sh \
  --plot_only BenchmarkResults/crush-modes-<timestamp>

bash benchmark-reconstruction.sh \
  --plot_only BenchmarkResults/reconstruction-<timestamp>
```

Benchmark cases are checkpointed after all of their result and profiling rows
have been written. Resume an interrupted run in place with the same case-study
and backend selection:

```sh
bash benchmark.sh \
  --case_study all \
  --with crush \
  --resume BenchmarkResults/reproduction-<timestamp>-crush

bash benchmark-crush-modes.sh \
  --case_study all \
  --resume BenchmarkResults/crush-modes-<timestamp>

bash benchmark-reconstruction.sh \
  --case_study LeanHammer \
  --resume BenchmarkResults/reconstruction-<timestamp>
```

Completed cases are skipped; interrupted and truncated cases are replaced and
rerun.

Plot closed and reconstructed VCs against time with matplotlib, from any
completed result directory:

```sh
python3 -m pip install matplotlib

python3 scripts/plot-time-coverage.py \
  BenchmarkResults/reproduction-<timestamp>-<backend>/leanhammer \
  --out-dir BenchmarkResults/figures
```

Every other script uses only the Python standard library, and no harness calls
this one.

The harnesses clone and build pinned source revisions, check them out in
temporary worktrees, and overlay the local lean-crush build. Set
`Z3_BIN`/`CVC5_BIN` when the solvers are not on `PATH`; the lean-smt lane is
the exception, since it drives cvc5 through the in-process bindings its own
Lake package links. Exact settings and
output definitions are in the [benchmark script guide](scripts/README.md). See
[`BENCHMARKS.md`](BENCHMARKS.md) for the latest recorded comparison.
The user manual also presents the
[coverage, outcome, and reconstruction figures](https://ad1024.github.io/lean-crush/Benchmarks/).

The [Cedar `crush-backend` branch](https://github.com/AD1024/cedar-spec/tree/crush-backend)
contains a
[`CedarCrushCaseStudy`](https://github.com/AD1024/cedar-spec/blob/crush-backend/cedar-lean/CedarCrushCaseStudy.lean)
module built on `Cedar.Thm`. It demonstrates `crush` as an interactive leaf tactic
for Cedar foundation proofs, using kernel reconstruction rather than
`Crush.crushSorry`.

## Acknowledgements

lean-crush builds on ideas and test material from several projects:

- [lean-auto](https://github.com/leanprover-community/lean-auto) — the tool this redesigns;
  its monomorphization approach, typed SMT IR shape, and test corpus informed the design,
  and its `SmtTranslation` suite is ported in the case studies.
- [Loom](https://github.com/verse-lab/loom) and its verifiers
  [Velvet](https://github.com/verse-lab/velvet) (Dafny-style imperative) and Cashmere
  (effectful monadic) — the source of the verification-condition case study.
- [Cedar](https://github.com/cedar-policy/cedar-spec) — the formal specification and
  Lean foundation used by the Cedar case study.
- [Strata](https://github.com/strata-org/Strata) — its Lambda type matcher and proof
  structure underpin the extracted soundness, completeness, and occurs-check case study.
- [Veil](https://github.com/verse-lab/veil) — its model-minimization approach (`z3model.py`)
  informs the planned counterexample minimization.
