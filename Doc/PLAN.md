# lean-crush — Implementation Plan

**A Lean 4 ↔ SMT bridge with first-class higher-order support and a
metaprogrammed, user-extensible translation layer.**

Status: project scaffolded, foundational layers built and tested (see
"Milestone 0" below). This document is the architecture and roadmap.

---

## 1. Motivation and what's wrong with lean-auto

lean-auto (Qian et al., the tool this replaces) is architecturally sound in its
front half but has three problems we set out to fix. All three are visible
directly in its source:

1. **Higher-order goes to die at the SMT boundary.** lean-auto reifies Lean into
   a genuinely higher-order embedded logic (`Auto/Embedding/LamBase.lean`:
   `LamTerm` has `.lam` and `.app`), but the translation to SMT,
   `Auto/Translation/LamFOL2SMT.lean`, is *first-order only*. Any function-typed
   argument or partial application hard-fails:
   - `LamFOL2SMT.lean:176` — `lamSort2SSortAux … | .func _ _ => throwError "Unexpected error. Higher order input?"`
   - `LamFOL2SMT.lean:543/548/556` — `throwError "Argument number mismatch. Higher order input?"`

   There is **no lambda-lifting, defunctionalization, or applicative-encoding
   bridge**. So HOL problems that reify fine die at the last step.

2. **Fragile solver plumbing.** `Auto/Solver/SMT.lean` spawns the solver, then
   `solver.stdout.getLine` / `readToEnd` with **no wall-clock timeout of its
   own** (it trusts the solver's `-T`/`--tlimit`), **no `try/finally` cleanup**
   (an exception mid-query leaks a zombie process), and **no `unknown`
   handling** (only `sat`/`unsat` are matched; everything else silently returns
   `none`). Backends are hardcoded (`z3`, `cvc5`; `cvc4` is `throwError "not
   supported"`).

3. **The translation table is closed.** The mapping from Lean constants to SMT
   is baked into `LamBaseTerm` + `LamFOL2SMT`. A user who wants
   "translate *my* constant to *this* SMT term/theory" cannot do it without
   forking the tool. There is no attribute, typeclass, or metaprogram hook.

Additional friction (from lean-auto's own `TODO.md`): unsound Nat-in-constructor
handling, quadratic `collectLamTermAtoms`, slow proof parsing, and a verified
checker that is "slow on large input" (their words) — 6s to typecheck one
`BinderComplexity` example.

### What we keep from lean-auto

- The **monomorphization** idea (dependent/polymorphic → HOL) — but rebuilt with
  clearer fuel/termination controls.
- The **typed SMT IR** shape (`Auto/IR/SMT.lean`) — reimplemented as
  `Crush.SMT.Syntax` with `Repr` everywhere and a `:named`-provenance slot.
- The **bijective high↔low name map** for symbol generation.
- The **reified STLC IR** `LamSort`/`LamTerm` *shape* — specifically the trick of
  storing the argument sort on each `app` node so type-checking is a single
  unification-free bottom-up pass, and the `atom`/`etom` (ordinary vs.
  existential/Skolem) split. Reimplemented as `Crush.Reify.CSort`/`CTerm`. But we
  keep only a plain `lamCheck? : CTerm → Option CSort` sanity checker — **not**
  the `LamWF` inductive family with its `interp`, since we are not proving rules
  sound in the kernel.
- The **`DTr` derivation-provenance** mechanism (cheap, checker-independent) so an
  unsat core can be reported as e.g. "from `❰h₁❱`, `defeq 0 List.map`".

### What we drop or make optional

- The **deep-embedding verified checker** (`Auto/Embedding/*`, ~12k lines) is
  **not** on the default path. Proof trust is a *policy* (`crush.trust`), and
  reconstruction is *pluggable* (see §6). Rationale: the checker is the single
  largest source of lean-auto's complexity and compile-time cost, and modern
  practice (Lean's own `bv_decide`, lean-smt's Alethe replay) shows that
  external-solver-plus-certificate is a better cost/confidence tradeoff than a
  hand-verified reflective checker for the whole logic.

---

## 1b. Positioning vs. the 2026 ecosystem

lean-crush is not being designed in a vacuum. A survey of the current field
(lean-smt, lean-auto, Lean core's `bv_decide`/`grind`/`LibrarySuggestions`,
Duper, LeanHammer, Isabelle's Sledgehammer, cvc5's HO support) sharpens exactly
where we add value and where we should copy rather than reinvent.

**We are not first at programmatic translation.** lean-smt (the cvc5 team's own
tactic) already has `@[smt_translate] : Translator := Expr → TranslationM (Option
Term)` — the same shape as our `TranslationHandler`. So the bare attribute is not
the differentiator. What is:

1. **A declarative term-level tier is the clear open gap.** lean-smt has a
   programmatic tier (`@[smt_translate]`) and a Lean→Lean simp tier
   (`@[smt_normalize]`), but *no* declarative "this constant ↦ this SMT term"
   surface. Our `crush_map` / `crush_map_sort` sugar (desugaring to a handler) is
   precisely that missing tier — most users want `Nat.succ ↦ (+ _ 1)`, not a
   `MetaM` function.
2. **Handler dispatch indexed by head symbol.** lean-smt tries every translator on
   every subterm in arbitrary order — its source literally carries
   `-- TODO: Use DiscrTree ... instead of naively looping`. We index handlers by
   head constant in a `DiscrTree` with explicit priorities, so dispatch is
   `O(matching)` and override semantics are predictable. (Our current skeleton
   uses a priority-sorted linear scan; the `DiscrTree` index is a planned
   refinement — see §4.4.)
3. **Higher-order actually survives.** lean-smt throws
   `"SMT-LIB does not support lambdas"` — its only HO answer is monomorphization.
   We add the encoding layer (§5). Notably even Isabelle's Sledgehammer, after
   15 years of tuning, uses plain **λ-lifting for all SMT solvers**, which
   validates our default; and cvc5 *does* support HO natively (below), which
   lean-smt leaves switched off.

**Things to copy, not reinvent:**

- **Subprocess management from `bv_decide`'s `External.lean`**: `runInterruptible`
  with a ~50 ms poll loop that checks the elaborator's **cancellation token** (so
  editor cancellation actually kills the solver), Windows-safe self-implemented
  timeouts, and a 3-tier solver-path fallback (explicit option → bundled binary →
  `PATH`). Our `Crush/Solver/Process.lean` already does the hard-timeout race and
  guaranteed cleanup; adding cancellation-token checking is a tracked refinement.
- **Premise selection from Lean core `Lean.LibrarySuggestions`**: MePo, SineQuaNon,
  and the MeSh-style `combine`/`intersperse` combinators are now *in core*. We
  build the premise hook on `Selector := MVarId → Config → MetaM (Array
  Suggestion)` with `Config.caller := "crush"`, rather than porting MePo.
- **lean-auto's `@[rebind]` typed-hole pattern** for pluggable solver/native
  backends (type-checked at attribute time via `isDefEq`), rather than an untyped
  name registry.
- **lean-smt's `skippedGoals`/`addTrust`**: when reconstruction can't close a
  step, emit it as a residual Lean goal (well-scoped via `mkForallFVars`) instead
  of hard-failing.
- **Config ergonomics**: a bare non-Prop identifier in the hint list expands to
  its equation lemmas via `getEqnsFor?` (i.e. `crush [myFn]` means "unfold
  `myFn`"); a Verus-style `@[crush_opaque]` + explicit `reveal` for
  user-controlled definition visibility to keep queries tractable.

## 2. Design goals

1. **Higher-order first.** Lambdas, partial application, and function-valued
   arguments must translate, via a chosen strategy (defunctionalization,
   combinators, or a HO-native backend), not crash.
2. **User-extensible translation as a first-class metaprogramming API.** A user
   writes a Lean metaprogram — evaluated at elaboration time — that says how a
   matched `Expr` becomes SMT. The built-in theory mappings are themselves
   written against this same API (dogfooding).
3. **Configurable backends and resource limits**, enforced *by us*: solver
   choice, timeout (hard wall-clock kill), extra flags, logic override, trust
   mode.
4. **Honest results.** `sat`/`unsat`/`unknown`/`timeout` are distinct and
   reported as such. Errors are actionable and point at the offending Lean term.
5. **Incremental, testable layering.** Each layer builds and is tested in
   isolation before the next depends on it.

---

## 3. Architecture overview

```
        Lean goal + hints
              │
   ┌──────────▼───────────┐
   │ 1. Collection         │  gather hypotheses, unfold/defeq hints, user facts
   │    (Frontend)         │
   └──────────┬───────────┘
              │  Array Fact  (proof, type, provenance)
   ┌──────────▼───────────┐
   │ 2. Preprocessing      │  β/η, let/proj reduction, skolemization prep
   └──────────┬───────────┘
              │
   ┌──────────▼───────────┐
   │ 3. Monomorphization   │  poly/dependent → HOL, fuel-bounded saturation
   └──────────┬───────────┘
              │  higher-order, universe-monomorphic facts
   ┌──────────▼───────────┐
   │ 4. HO Encoding        │  ← THE KEY NEW LAYER
   │    (defunc/comb/native)│ eliminate λ and partial application
   └──────────┬───────────┘
              │  first-order facts (or HO-native for cvc5)
   ┌──────────▼───────────┐
   │ 5. Translation        │  Expr → Crush.SMT.Term
   │    - user handlers     │  ← @[crush_translate] tried first, by priority
   │    - default structural│
   └──────────┬───────────┘
              │  Array SMT.Command
   ┌──────────▼───────────┐
   │ 6. Solve              │  spawn backend, hard timeout, parse result
   └──────────┬───────────┘
              │  sat / unsat(core,proof) / unknown
   ┌──────────▼───────────┐
   │ 7. Discharge          │  trust (crushSorry) | reconstruct | reconstructOrTrust
   └──────────────────────┘
```

Module map (⟢ = built & tested, ▷ = designed, □ = todo):

| Module | Layer | Status |
|---|---|---|
| `Crush/SMT/Syntax.lean` | typed SMT-LIB IR | ⟢ |
| `Crush/SMT/Print.lean` | IR → SMT-LIB text | ⟢ |
| `Crush/Frontend/Config.lean` | options + `Config` | ⟢ |
| `Crush/Translation/Monad.lean` | `TranslateM`, name map, provenance | ⟢ |
| `Crush/Translation/Attr.lean` | `@[crush_translate]` extension | ⟢ |
| `Crush/Translation/Builtins.lean` | `crush_map` sugar | ⟢ |
| `Crush/Translation/Theories.lean` | BV/String helpers + div-by-zero guards | ⟢ |
| `Crush/Solver/Process.lean` | process mgmt, hard timeout, `unknown` | ⟢ |
| `Crush/SMT/Sexp.lean` | s-expression parser | ⟢ |
| `Crush/SMT/Result.lean` | unsat-core + model parsing | ⟢ |
| `Crush/Reify/Term.lean` | `CTerm`/`CSort` IR (STLC, no `LamWF`) | ⟢ |
| `Crush/Reify/Collect.lean` | hypothesis & goal collection | ⟢ |
| `Crush/Reify/Reify.lean` | `Expr → CTerm`, atom allocation, `DTr` provenance | □ |
| `Crush/Translation/Preprocess.lean` | reduction, skolem prep | □ |
| `Crush/Translation/Monomorphize.lean` | poly → HOL saturation | □ |
| `Crush/Translation/HOEncoding.lean` | λ-elimination (defunc ⟢, native ⟢, comb □) | ⟢ |
| `Crush/Translation/Translate.lean` | driver: `Expr → SMT.Term` via handlers | ⟢ |
| `Crush/Solver/Reconstruct.lean` | unsat-core → Lean proof replay | □ |
| `Crush/Frontend/Tactic.lean` | the `crush` tactic (`trust` mode) | ⟢ |

---

## 4. The extension framework (the centerpiece)

### 4.1 API surface

A **translation handler** is an ordinary Lean value:

```lean
abbrev TranslationHandler := TranslationCtx → TranslateM (Option SMT.Term)
```

evaluated at *tactic time* via `evalConst`. `TranslationCtx` hands the handler
the applied head `fn`, its `args`, and recursion callbacks `emitTerm`/`emitSort`
plus a `declare` callback for emitting declarations lazily. A handler returns
`some t` to claim the term, or `none` to defer. This is strictly more expressive
than a static table: a handler can inspect types, synthesize instances, recurse,
emit auxiliary declarations, and make choices based on the concrete arguments.

Registration is by attribute, with `simp`-style priorities:

```lean
@[crush_translate high]
def succHandler : TranslationHandler := fun ctx => do
  let .const ``Nat.succ _ := ctx.fn | return none
  match ctx.args with
  | #[n] => return some (.app (.symb "+") #[← ctx.emitTerm n, .lit (.num 1)])
  | _ => return none
```

For the common "map this constant to this symbol/sort" case there is sugar that
desugars to a handler:

```lean
crush_map Nat.add => "+"
crush_map_sort Nat => "Int"
```

### 4.2 Why elaboration-time metaprograms

The user's requirement — "the meta-program should be able to be evaluated at
elaboration time to smt code" — is met by storing handler **declaration names**
in a `SimplePersistentEnvExtension` and resolving them with `evalConst`
(`unsafe`, wrapped via `@[implemented_by]` — the standard `KeyedDeclsAttribute`
idiom) when the tactic runs. This means:
- handlers are just Lean code, type-checked at declaration (`@[crush_translate]`
  verifies the `: TranslationHandler` type at attribute-application time, so
  mistakes surface early);
- they compose across files/imports (the extension is persistent);
- they have the full `MetaM` toolbox available.

### 4.3 Built-ins are handlers too

The core theory mappings (Bool, `=`, `∧/∨/¬/→`, Nat→Int with well-formedness
side-conditions, Int, BitVec, String, datatypes) will be registered as
`@[crush_translate]` handlers at low/default priority in
`Crush/Translation/Builtins.lean`. User handlers at `high` priority thus override
built-ins for the same constant. There is no privileged built-in path — anything
the built-ins can express, a user can.

---

## 4b. Monomorphization design (learning from lean-auto's scars)

Layer 3 instantiates polymorphic/dependent facts into universe-monomorphic HOL
via a saturation loop, as lean-auto does. A close reading of lean-auto's
`Monomorphization.lean` surfaced four concrete traps we design around from the
start rather than patching later:

1. **Instantiation reach must not be structurally capped at the first
   hypothesis.** lean-auto's `LemmaInst.ofLemmaHOL` only makes the *leading*
   non-`Prop` binder prefix instantiable, so in `∀ α, P α → ∀ β, Q β` the `β` is
   forever un-instantiable. We track instantiable positions through the whole
   telescope, not just the prefix.
2. **Fuel must be a meaningful quantity with a loud failure.** lean-auto's
   `saturationThreshold = 1024` counts a *bag of unrelated events* (queue pops +
   group visits + match calls), corresponds to no clean quantity, has no depth or
   term-size bound, and **silently returns** a truncated set on exhaustion (its
   own TODO: "Report errors when monomorphization fails"). We separate
   `crush.mono.fuel` (a real instance-count budget) from `crush.mono.rounds` (a
   saturation-round bound), add a term-depth guard, and on exhaustion emit a
   diagnostic naming what was dropped — never a silent truncation.
3. **Matching needs an index; dedup needs a normal form.** lean-auto has *no*
   term index and *no* congruence closure — matching is a full `Expr` walk with
   `Meta.isDefEq` at every candidate node, and dedup is a linear `isDefEq` scan in
   four separate places, i.e. O(n²) `isDefEq` calls throughout. We index candidate
   heads with a `DiscrTree` and canonicalize instances by a hashed fingerprint
   before falling back to `isDefEq`, so the common case is not quadratic.
4. **Definitional-equality transparency must be consistent across layers.**
   lean-auto mixes `default` (for `ConstInst`/type-canonicalization) and
   `reducible` (for reduction/reification); its `Test/SetMembershipDefEq.lean`
   documents a concrete crash from exactly that mismatch, "fixed" by silently
   dropping facts. We fix one transparency policy per phase and record it in
   `Config`, so the reifier and the monomorphizer never disagree about whether
   `MySet α ≡ α → Prop`.

Also adopted: the `Nonempty`/`Inhabited` → witness conversion for inhabitation
(via `Classical.choice`/`Inhabited.default`), since SMT-LIB assumes every sort is
non-empty (see §10.1); and `DTr`-style provenance on every generated instance so a
dropped or unprovable fact can be named.

## 5. Higher-order handling (the key capability)

`crush.ho.mode` selects the strategy applied in Layer 4, after monomorphization
and before first-order translation:

- **`defunctionalize`** (default). Collect the set of function-valued closures
  that actually appear; introduce an `apply` uninterpreted function per arrow
  sort and a constructor tag per closure, plus defining axioms. This is complete
  for the ground fragment and keeps everything in `QF_UF`/`UF`+theory logics
  that *every* backend supports.
- **`combinators`** (Sledgehammer-style). Translate λ via S/K/B/C/W combinators
  with their defining equations. Smaller encoding, weaker for extensionality;
  useful when defunctionalization blows up.
- **`native`**. Emit higher-order SMT to a HO-capable backend and let the solver
  handle application/partial application directly. Fastest path when the backend
  supports it; falls back with a diagnostic if the chosen backend is
  first-order-only (z3). **Implementation detail that bites**: cvc5 gates HO on
  the logic-string prefix — `(set-logic HO_ALL)` / `HO_UF`, *not* `ALL` (its
  `enableEverything` is gated on the `HO_` prefix). lean-smt emits `ALL` and thus
  never turns cvc5's HO solver on; the `native` mode must emit the `HO_` logic and
  can additionally pass `--uf-ho-exp`/`--ho-elim`. cvc5's own mechanism is a lazy
  applicative encoding plus extensionality + app-encode axioms ("Extending SMT
  Solvers to Higher-Order", Barbosa et al.) — i.e. our `defunctionalize` mode is
  the manual version of what cvc5 does internally.

Naming note: what we call `defunctionalize`/`combinators` are Sledgehammer's
`lam_trans = lifting`/`combs`. Sledgehammer forces `lifting` for *all* SMT
solvers, which is why `defunctionalize` (λ-lifting into per-closure `apply`
symbols) is our default rather than combinators.

The IR in `Crush/SMT/Syntax.lean` is deliberately first-order so that the
`defunctionalize`/`combinators` outputs map 1:1 onto what solvers accept; the
`native` path uses an extended emitter (planned `Crush/SMT/PrintHO.lean`).

`Crush/Translation/HOEncoding.lean` will expose:
```lean
def encodeHO (mode : HOMode) (facts : Array HOFact) : TranslateM (Array HOFact)
```
returning facts whose terms are first-order (for the first two modes) together
with the auxiliary `apply`/combinator declarations emitted into the script.

---

## 6. Solving, trust, and reconstruction

- **Process control** (`Crush/Solver/Process.lean`, built): data-driven
  `backendSpec`, our own wall-clock race with a hard `kill`, `try/finally`
  cleanup, and `unknown`/`timeout` as first-class results. Adding a backend is a
  table row.
- **Result parsing** (`Crush/SMT/Parser.lean`, todo): an s-expression parser
  feeding a model reader (for `sat` counterexamples) and an unsat-core reader
  (mapping `crush_fact_<id>` names back through the provenance table in
  `TranslateState.facts`).
- **Discharge policy** (`crush.trust`):
  - `trust` → close with `crushSorry` axiom (documented as unsound-by-trust,
    warns).
  - `reconstruct` → replay the unsat core into a Lean proof; **fail** if replay
    fails (sound, no new axioms).
  - `reconstructOrTrust` (default) → try replay, fall back to trust with a
    warning.
- **Reconstruction** (`Crush/Solver/Reconstruct.lean`, todo): initial version
  uses the **unsat core** to select the minimal fact set and hands it to a
  Lean-side finishing tactic (e.g. `duper`/`grind` over exactly those facts),
  turning "SMT says yes" into a checked proof without a bespoke verified checker.
  A later version can parse Alethe proofs (cvc5) à la lean-smt.

---

## 7. Frontend / tactic

```
crush [h₁, …, hₙ] [*] [* db] (u[c₁,…]) (d[c₁,…])
```

- `[…]` explicit facts (terms), `*` = all local hypotheses, `* db` = a named
  lemma database, `u[…]` unfold, `d[…]` definitional equalities. (Grammar
  mirrors lean-auto's for familiarity.)
- All behaviour is governed by `set_option crush.*` (see §8), read once into
  `Config` at entry.
- The tactic: collect → preprocess → monomorphize → HO-encode → translate
  (handlers) → solve → discharge, with `trace.*` classes at each boundary and
  the full script available via `crush.trace.script` / `crush.save`.

**Two hard lessons from lean-auto's frontend that shape ours:**
- **Report the pipeline, always.** lean-auto's most-complained-about error is a
  bare `"Auto failed to find proof"` that never says which of its three backends
  ran, what the solver's verdict was, or that a model exists — all of that is
  computed and thrown into trace classes that are off by default. `crush` emits a
  one-line outcome by default: backend, verdict (`unsat`/`sat`/`unknown`/timeout),
  wall time, #facts sent, #facts dropped. A `sat` result is surfaced as a
  **counterexample** (parsed from `get-model`), not as a generic failure — lean-auto
  has 527 lines of unused SMT→Expr model-parsing machinery it never wired up.
- **`(set-logic ...)` must be emitted.** lean-auto never emits it (the constructor
  exists but is never constructed), which silently disables theory- and
  HO-specific solver behaviour. `crush` always emits the resolved logic
  (auto-detected or `crush.logic`), and `HO_`-prefixed for `native` HO mode.

Per-call configuration is a planned surface: `crush (timeout := 5) (backend :=
cvc5) [hints]` overriding the `set_option` defaults, since lean-auto's 43
global-only options with no call-site syntax are the root of most of its
friction. The current milestone reads `Config` from options only; the config
syntax layers on without changing the pipeline.

---

## 8. Configuration options (all implemented as `register_option`)

| Option | Type | Default | Controls |
|---|---|---|---|
| `crush.backend` | `z3\|cvc5\|bitwuzla\|none` | `z3` | solver process / translation profile |
| `crush.timeout` | `Nat` (s) | `10` | hard wall-clock limit (enforced by us) |
| `crush.trust` | `trust\|reconstruct\|reconstructOrTrust` | `reconstructOrTrust` | how `unsat` discharges the goal |
| `crush.ho.mode` | `defunctionalize\|combinators\|native` | `defunctionalize` | HO elimination strategy |
| `crush.mono.fuel` | `Nat` | `512` | max monomorphization instances |
| `crush.mono.rounds` | `Nat` | `8` | max saturation rounds |
| `crush.logic` | `String` | auto | override SMT-LIB logic |
| `crush.additionalArgs` | `String` | `""` | extra solver flags |
| `crush.save` | `String` | `""` | write script to path |
| `crush.trace.script` | `Bool` | `false` | log generated script |

---

## 9. Milestones

**Milestone 0 — Foundations (DONE, builds + tested).**
SMT IR + printer, config/options, `TranslateM` + name map + provenance,
`@[crush_translate]` extension + `crush_map` sugar, robust solver process layer.
Smoke test (`Test/Smoke.lean`) confirms: valid SMT-LIB emission, 3 handlers
registered via both surfaces, config parse, and a live `z3` `unsat` round-trip.

**Milestone 1 — First-order end-to-end (DONE, builds + tested).**
`SMT/Sexp.lean` + `SMT/Result.lean` (s-expr parser, unsat-core + model parsing),
`Reify/Collect.lean` (hypotheses + negated goal), `Translation/Translate.lean`
(handler dispatch + default structural translator for Bool/Prop/Int/Nat/UF with a
Nat `≥0` quantifier guard), `Frontend/Tactic.lean` (the `crush` tactic in `trust`
mode with pipeline reporting and `sat`→counterexample). `Test/FirstOrder.lean` confirms:
`∀ x : Int, x + 0 = x`, hypothesis use, propositional logic, linear arithmetic,
uninterpreted-function congruence all close; a false goal (`x + 1 = x`) is
correctly *rejected* with a counterexample rather than silently closed.

**Milestone 2 — Theories + Nat (DONE, builds + tested).**
All of `Test/Theories.lean` passes: 9 negative tests correctly *rejected* (each
wrapped in `#guard_msgs`, so a regression that closed one would fail the build),
every positive test closed, and `#print axioms` confirms `crushSorry` remains the
only trust axiom.

* **Nat→Int** with the non-negativity soundness fix: every `Nat`-typed
  variable/atom/function-result carries a `≥0` well-formedness constraint, and
  `Nat.sub` truncates via `ite` — closing the `∀ n:Nat, n-1 < n` unsoundness that
  lean-auto's TODO flags and that this tool exhibited before the fix.
* **Datatypes**: non-parametric inductives — enumerations, structures, and
  (new) **self-recursive** types — via `declare-datatypes`, with constructor
  distinctness, injectivity, exhaustiveness, and projections/selectors.
* **Bit-vectors**: statically-known widths as `(_ BitVec w)`; arithmetic, bitwise,
  shifts (with `Nat`-amount coercion), unsigned/signed comparisons, `concat`,
  `extract`, `setWidth`/`signExtend`, and **guarded division-by-zero**.
* **Strings**: `str.++`/`str.len`/`str.prefixof`, with SMT-LIB-correct literal
  escaping (codepoint-accurate, and aware that `\` is not an SMT escape char).
* **Int div/mod**: verified Lean's default `Int./`/`%` are Euclidean (matching
  SMT-LIB), plus an exactness guard at a zero divisor.

Three soundness bugs were found and fixed *during* this milestone, all by
differential probing against Lean and z3 rather than by reading specs — see §10
items 3, 5, and 6. Item 3 (`Nat` in datatype fields) was a live false-`unsat`:
`crush` proved `False` from a true hypothesis, and thence `2 + 2 = 5`.

Remaining (deferred, not blocking M3): port lean-auto's `Test/SmtTranslation/*`
regressions; parametric datatypes (need monomorphization, M5); `BitVec.toNat`
(needs the `bv2nat` mixed-theory bridge).

**Milestone 3 — Higher-order (`defunctionalize` + `native` DONE; `combinators`
not started).**
`HOEncoding.lean` + the HO paths in `Translate.lean`. This is the headline feature —
the benchmark is the set of HO goals that make lean-auto throw "Higher order
input?". `Test/HigherOrder.lean` passes: 10 positive tests closed, 6 negative correctly
rejected, `crushSorry` still the only trust axiom, verified on z3 and cvc5.

**It turned out to be a soundness fix, not only a feature.** Before this milestone
an arrow type became an opaque sort and a function-typed *bound variable* was
declared as an unrelated `declare-fun`, so

```lean
h : ∀ (f : Int → Int), g f = f 0
```

emitted `(forall ((q Fn)) (= (g q) (q' 0)))` with `q'` disconnected from `q` — i.e.
asserting **`g` is constant**, strictly *stronger* than `h`. `crush` therefore
closed `g (fun x => x) = g (fun x => x + 1)`, whose negation is provable in Lean.
That goal is now the `must_reject_ho_constant` regression.

Shipped:
* **`defunctionalize`** (default) — one uninterpreted `Fn` sort and *n*-ary `app`
  symbol per arrow type; each λ becomes a closure constant with defining axiom
  `app(clo ȳ, x̄) = body`, parameterized by its captures when it closes over
  SMT-bound variables; named functions passed as values are η-expanded into
  closures bridged by `app(clo, x) = f(x)`.
* **Extensionality**, per arrow sort and *on demand* (only when an equation between
  function-typed terms occurs, since it is a costly quantifier alternation).
  Verified load-bearing: `∀ x, f x = g x ⊢ f = g` is `sat` without it, `unsat` with.
* **`native`** — `(-> σ τ)` sorts, direct application, `lambda` terms, under a
  `HO_`-prefixed logic. Confirmed empirically that cvc5 gates HO on the prefix
  (`HO_ALL` works, `ALL` does not) and that z3 ignores it with a warning and then
  fails on the sorts — so `native` is gated to cvc5 and falls back to
  `defunctionalize` with a diagnostic elsewhere. Note cvc5 answered `unknown`
  rather than `sat` on a satisfiable HO query in testing: sound, but it loses
  counterexamples.

Not done: **`combinators`** (S/K/B/C/W). The mode is accepted but warns and falls
back to `defunctionalize` rather than silently pretending. Its value is as an escape
hatch when defunctionalization blows up, which needs a workload that actually blows
up to tune against — so it is deferred until there is one. P5 stays 🔴.

Note on partial application: `app` is *n*-ary over the flattened argument list
rather than a chain of unary applies, which keeps the common fully-applied case
small. Genuine partial application still works, via the same η-expansion used for
named functions — `g (f 1)` with `f : Int → Int → Int` emits a closure with
`app(clo, x) = f(1, x)` (tested). What is *not* supported is a partially-applied
term whose remaining arity is itself higher-order.

**Milestone 4 — Soundness/reconstruction.**
Unsat-core-driven reconstruction (core → `duper`/`grind`; the "solver-as-oracle"
model), then Alethe replay for cvc5. Nat-in-constructor soundness fix that
lean-auto's TODO flags.

**Milestone 5 — Ergonomics & scale.**
Monomorphization fuel tuning, premise selection hook (on Lean core
`LibrarySuggestions`), portfolio backend, per-call config syntax, richer model
pretty-printing, docs and examples.

**Milestone 6 — Verified soundness.**
Discharge the §10b `sorry`s in `Crush/Proofs/`, prioritized P4 → P10 → P6 → P8 →
P7 (the passes that can silently produce a wrong `unsat`), then the definitional
ones. Each proof shrinks the trusted computing base, à la `bv_decide`.

Partial credit already banked: P11's **Lean-side** boundary facts are proven (9
theorems in `Crush/Proofs/Obligations.lean` — the `#eval` probes from the design
phase promoted to machine-checked statements), so a future toolchain that changed
`x / 0` or `Int./`'s rounding would break the build rather than silently
invalidate the encoding. The SMT side of P11 needs P8's denotational semantics.

---

## 10. Soundness obligations (the price of dropping the verified checker)

Dropping lean-auto's verified checker for the SMT path is the right call — a deep
study of the embedding confirms ~75% of lean-auto (~16k lines: all of
`Auto/Embedding/*`, plus the `Lam2Lam`/`BuildChecker` half of `LamReif.lean`) is
checker-specific and provides **zero** soundness guarantee on the SMT path (SMT
results in lean-auto are either closed with the `autoSMTSorry` axiom under
`smt.trust`, or used only as a premise selector). The entire `GLift`/`ILLift`/
`IsomType` universe-lifting apparatus (`Auto/Embedding/Lift.lean`) exists *only*
to state the checker's `LamThmValid` theorem and disappears with it. The
atoms-as-fvars reconstruction (`Lam2DAtomAsFVar.lean`) shows the unlifted path.

But the checker also *silently absorbs* a set of obligations that then become
**our** responsibility in unverified translation code. lean-auto's own `TODO.md`
admits it hasn't fully discharged them even *with* the checker. We enumerate them
here and each gets a dedicated test (both a "must be unsat" and a "must not be
falsely unsat" case):

1. **Inhabitation.** ✅ *addressed (M2).* SMT-LIB assumes every sort is non-empty;
   Lean types may be empty. Emitting an unconstrained `declare-sort` for a
   possibly-empty Lean type is unsound: `∀ x : Empty, P` is vacuously true, its
   naive image `(forall ((x S)) P)` is not. `quantifier` now **refuses** to
   translate a quantifier whose domain is a structurally-uninhabited inductive
   (`isEmptyType`), with a diagnostic, rather than emitting an unsound encoding.
   Note the non-dependent case (`Empty → False`, where the binder is unused) takes
   the implication path and abstracts the antecedent as an opaque `Bool` atom,
   which is independently sound. A zero-constructor inductive is also excluded from
   `isSupportedDatatype` (z3 rejects an empty `declare-datatypes` outright).
2. **`Nat` is not `Int`.** ✅ *fixed (M2).* Every `Nat`-typed quantifier carries a
   `≥ 0` guard and every `Nat`-valued symbol a non-negativity constraint;
   **truncated subtraction** (`Nat.sub`, where `3 - 5 = 0`) is emitted as an `ite`,
   not SMT `-`. Regression: `must_reject_sub` (`∀ n : Nat, n - 1 < n`), which this
   tool *did* wrongly prove before the fix.

   **Why not just use a `Nat` sort, or define our own?** This is the obvious first
   reaction to the guard machinery, so the answer is recorded here. SMT-LIB's
   arithmetic theory defines exactly `Int` and `Real` — there is **no `Nat` sort**
   (`(declare-const n Nat)` is an unknown-sort error in both z3 and cvc5), and no
   subsort or refinement mechanism to carve out "the `Int`s that are `≥ 0`". So
   non-negativity *must* be expressed as a constraint rather than as a type. The
   two ways to define our own were benchmarked against the current encoding:

   * **Dedicated uninterpreted sort + bijection to the non-negative `Int`s.**
     Appealing because non-negativity becomes structural, so datatype fields would
     need no `wf` at all. But the three bijection axioms (`n2i (i2n i) = i`,
     `i2n (n2i n) = n`, `n2i n ≥ 0`) are mutually-recursive quantified equalities
     that send z3 into an instantiation loop: it **times out on the bare
     consistency check**, before any goal. Strictly worse — it makes everything
     unsolvable, not just some things.
   * **Peano datatype (`zero | succ`).** Exact as a set, but discards linear
     arithmetic: `x + y = y + x` stops being a solver primitive and needs
     induction, which SMT has no rule for.

   Ranking: guarded `Int` > bijection sort (diverges immediately) > Peano (loses
   arithmetic). Note the guard is not free but its cost is narrow — a datatype with
   no `Nat` field gets a constantly-`true` `wf` and no guard is emitted at all.
   A possible future refinement: suppress the guard when the query's arithmetic
   never touches the guarded field.
3. **`Nat` inside inductive constructors.** ✅ *fixed (M2)* — lean-auto's TODO flags
   this as an active unsoundness, and it was live here too. The root cause is
   deeper than "selectors need a `≥ 0` constraint": SMT datatypes are **freely
   generated over their field sorts**, so a `Nat` field encoded as `Int` makes the
   SMT type strictly *larger* than the Lean type, populated by values with negative
   fields that no Lean value has. Consequently the **true** hypothesis
   `∀ p : PN, p.x ≥ 0` is *unsatisfiable* in SMT, and the solver derives `False`
   from it — a false `unsat`, the dangerous direction. (Confirmed: `crush` proved
   `False`, then `2 + 2 = 5`.) A per-selector constraint cannot fix this, because
   the problem is the *domain of quantification*, not the selector's range. Fix: a
   well-formedness predicate `wf_T` per datatype characterizing the image of the
   Lean type, defined in selector form per constructor
   (`(=> ((_ is C) x) ⟨field guards⟩)`) and used to guard **every quantifier** over
   `T` (`wfCondition`/`guardSort`). It composes transitively through nested
   datatypes and degenerates to constantly-`true` (hence free) when no field needs
   a guard. Regressions: `must_reject_nat_field`, `must_reject_field_sub`, plus
   `pn_field_nonneg`/`pn_field_cong` pinning that the guard is not over-restrictive.
   A recursive datatype with a guarded field yields a *recursive* `wf` axiom
   (`wf_L x = (is-cons x ⇒ hd x ≥ 0 ∧ wf_L (tl x))`), and this is the encoding's
   real cost. Tested through the tactic (`Test/Theories.lean`, `NList` group):
   many queries do discharge — constructor distinctness, propagation into nested
   tails, and quantification over the recursive type all close — but
   `must_not_close_nl_field` **times out**, and a longer budget does not help
   (checked at 30s), so it is genuine instantiation divergence rather than
   slowness. The outcome is sound (`unknown` never closes a goal, so no wrong
   answer), but it is a real loss of completeness on recursive types with guarded
   fields. Suppressing the guard when the query's arithmetic never touches the
   guarded field (see item 2's note) would recover most of these.
4. **Truncated vs. Euclidean division.** ✅ *resolved empirically (M2).* Verified
   directly rather than assumed: Lean's **default** `Int./` and `Int.%` are
   *Euclidean* (`(-7)/2 = -4`, `(-7)%2 = 1`), matching SMT-LIB `div`/`mod`, so the
   direct mapping is sound — no dual-operator apparatus needed for the default
   instance. `must_reject_tdiv` pins the T-division value as rejected.
   Additionally, SMT-LIB leaves `(div x 0)` *underspecified* while Lean pins
   `x / 0 = 0` and `x % 0 = x`. That gap is sound-but-incomplete (an
   underspecified operator admits Lean's interpretation, so `unsat` was already
   trustworthy); `intDivGuard` emits an `ite` to make the encoding exact.
5. **BitVec width and signedness.** ✅ *addressed (M2).* Only statically-known
   widths are translated (a symbolic `BitVec w` has no SMT sort and degrades to an
   opaque sort). Each operator was checked against both Lean and z3:
   - Lean's `/` and `%` on `BitVec` are the **unsigned** operations, and Lean's
     `<`/`≤` are **unsigned** comparisons (`(255 : BitVec 8) < 1` is `false`) —
     mapped to `bvudiv`/`bvurem`/`bvult`/`bvule`, with `BitVec.slt`/`sle` for the
     signed ones. Getting this backwards is unsound in both directions.
   - Shift amounts: Lean's `shl : BitVec n → Nat` vs SMT's `bvshl : BitVec n →
     BitVec n` — a `Nat` amount is materialized as a same-width literal
     (`shiftOp`). Amounts ≥ width agree (both yield 0 / sign-fill).
   - **Division by zero is a genuine disagreement, not an underspecification**:
     SMT-LIB *fixes* `bvudiv x 0` to all-ones and `bvsdiv x 0` to `±1`, while Lean
     gives `0`. Emitting the raw operator lets the solver prove Lean-false goals,
     so `bvDivGuard` rewrites to an `ite`. Regression:
     `must_reject_bv_div_zero`. By contrast `bvurem`/`bvsrem`/`bvsmod` already
     agree with Lean (all return the dividend) and are emitted raw.
   - Verified to agree exactly, needing no guard: `concat` operand order (left
     operand is high), `extract`, `zero_extend`/`sign_extend`, and the truncating
     behaviour of `setWidth`/`signExtend` when the target is narrower.
6. **Symbol collisions across datatypes.** ✅ *fixed (M2).* Two distinct Lean
   structures both using the default anonymous constructor name `mk` emitted two
   `mk`s and two `mk_sel0`s into one script, conflating unrelated types'
   constructors and selectors. Constructor and selector symbols are now qualified
   by the datatype's allocated (already-unique) SMT sort symbol
   (`ctorSymbol`/`selSymbol`). Regression: `no_collide`.
7. **String escaping.** ✅ *addressed (M2).* SMT-LIB doubles an embedded `"` and
   requires `\u{…}` for non-printable characters — and critically, `\` is **not**
   an escape character there (verified: `"\u{5c}"` and `"\\"` are *different*
   strings in z3), so a backslash must be emitted literally.
   `SMT.escapeSmtString` implements this. `str.len` counts codepoints, matching
   `String.length` (checked on `"λx"`).

8. **Function-typed bound variables.** ✅ *fixed (M3).* A quantifier over a function
   type must range over the encoded function sort with applications routed through
   `app`; declaring a fresh `declare-fun` for the bound variable leaves it
   *disconnected* from the quantifier, which silently **strengthens** the
   hypothesis. `∀ (f : Int → Int), g f = f 0` became "g is constant", and goals
   following from that were wrongly proved — a false `unsat`, confirmed by closing
   a goal whose negation is provable in Lean. Fixed by the HO encoding (§5); the
   regression is `must_reject_ho_constant`. Note this is the *same shape* of bug as
   items 1 and 3: in each case a Lean binder's domain was mapped to an SMT domain
   that is not its faithful image (too large for `Nat`-fielded datatypes and empty
   types, effectively too small — a single fixed value — here).

The theory semantics live in `Crush/Translation/Theories.lean` (width/literal
helpers and the division guards) and in `Translate.lean`'s `bitvecTerm?`/
`stringTerm?` recognizers. They are the reason built-ins need full `MetaM` access
(they must synthesize guards and inspect types), not a static table.

**Methodology note.** Every entry above was settled by *differential probing* —
evaluating the operator in Lean (`#eval`) and in z3 (`simplify`/`check-sat`) and
comparing — rather than from memory of either specification. Three of the seven
items turned out differently than the initial design assumed (item 3 was a live
false-`unsat`, item 4's default instance needed *no* special handling, item 5's BV
division needed a guard that `Int` division did not). Assumed semantics are how
unsoundness enters a hammer, so new theory support should follow the same
probe-first discipline.

## 10b. Formal proof obligations (verified soundness roadmap)

The obligations in §10 are, in Milestone 1–3, discharged by *testing* and by
*trusting the solver* (`crush.trust`). That is the pragmatic path and it matches
every deployed hammer. But the long-term goal is that each transformation pass
carries a **machine-checked semantic-equivalence theorem**, so that a chain of
passes composes into an end-to-end soundness guarantee and the trust surface
shrinks to (the solver's `unsat` verdict) + (the kernel). This section is the
ledger of what must be proven, tracked alongside the code. It is deliberately
separate from testing: a ✅ here means *a Lean proof exists in the repo*, not that
a test passes.

### The overarching statement

Let `⟦·⟧` denote the semantics of a fact in the source logic (a Lean `Prop`, or a
`CTerm` under an interpretation `I` assigning Lean meanings to atoms). Each pass
`T : Facts → Facts` must satisfy a **meaning-preservation** theorem of one of two
strengths:

- **Equivalence** (for normalization/encoding passes that must not change
  provability): `∀ I, (⟦Γ⟧_I) ↔ (⟦T(Γ)⟧_I)`, i.e. the pass neither loses nor
  invents models.
- **Equisatisfiability** (for passes introducing fresh symbols, e.g. Skolem/
  defunctionalization `apply` symbols): `(∃ I, ⟦Γ⟧_I) ↔ (∃ I', ⟦T(Γ)⟧_I')`, i.e.
  `T(Γ)` is unsat iff `Γ` is. This is the weaker but correct statement whenever a
  pass adds symbols that a model must interpret (you cannot demand the *same* `I`).

The composed guarantee we ultimately want:
> If the solver reports `unsat` on the emitted script, and every pass in the
> chain has its equivalence/equisatisfiability theorem, then the original goal
> `G` follows — reconstructed as a Lean proof term with no new axioms.

Reaching that fully closes the gap between `crush.trust reconstruct` being
*implemented* and being *proven*. Until each theorem below is ✅, the
corresponding pass is in the trusted computing base and must be flagged as such by
`#print axioms`-style auditing.

### Per-pass obligations

Status legend: 🔴 not started · 🟡 statement drafted, proof pending · ✅ proven.

| # | Pass (module) | Theorem to prove | Strength | Status |
|---|---|---|---|---|
| P1 | Preprocessing β/η, `let`/proj reduction (`Translation/Preprocess`) | reduced term is defeq to the original ⇒ same `Prop` | equivalence (definitional — cheap: `Eq.refl`/`rfl`-backed) | 🟡 `P1_obligation` stated; pass not built |
| P2 | Nat→Int embedding (`Translation/Translate`) | `⟦n : Nat⟧ = Int.ofNat n` and the `≥0` guard makes `∀`/`∃`/`sub`/`div` agree with Lean on the image | equivalence, per operator | 🔴 |
| P3 | Monomorphization (`Translation/Monomorphize`) | each generated instance is an instance of a source lemma ⇒ implied by it; instances are sound (already true "by construction" since each carries a Lean proof — the obligation is to *retain* that proof, not re-prove) | equivalence (Γ ⊢ each instance) | 🟡 |
| **P4** | **Defunctionalization (`Translation/HOEncoding`, `defunctionalize`)** | **for the introduced `apply`/closure symbols and their defining axioms `A`, `(∃ I, ⟦Γ⟧_I) ↔ (∃ I', ⟦defunc(Γ) ∪ A⟧_I')`** — the headline HO theorem | **equisatisfiability** | 🟡 **core ✅ proved** — `p4a`/`p4b`/`p4c` exhibit a canonical model satisfying the emitted axioms, with quantification over the function sort provably coinciding with the Lean function space; lifting to whole fact lists needs the semantics |
| P5 | Combinator encoding (`HOEncoding`, `combinators`) | S/K/B/C/W defining equations characterize the same functions ⇒ equisatisfiable | equisatisfiability | 🔴 |
| P6 | Skolemization (`Translation/Preprocess`) | `(∃ I, ⟦∀x∃y.φ⟧) ↔ (∃ I', ⟦∀x.φ[y:=f x]⟧)` with fresh `f`; classical, via `Classical.choice` | equisatisfiability | 🔴 |
| P7 | Reification `Expr → CTerm` (`Reify/Reify`) | `⟦reify(e)⟧_I = e` for the recovered interpretation `I` (the round-trip that makes reconstruction possible; lean-auto's `reifTermCheckType` checks types but not meaning) | equivalence | 🔴 |
| P8 | `CTerm → SMT.Term` lowering (`Translation/Translate`) | the SMT term denotes the same boolean/Int/… value as the `CTerm` under the sort interpretation | equivalence | 🔴 |
| P9 | Inhabitation discharge (`Translation/Translate`) | every sort emitted without a guard is genuinely non-empty (witness recorded), so SMT's non-emptiness assumption is sound | side-condition | 🟡 |
| **P10** | **Datatype well-formedness guard (`Translation/Translate`, `wfCondition`/`guardSort`)** | `wf_T` characterizes exactly the image of the Lean type: `∀ t, wf_T t ↔ ∃ (v : T), ⟦v⟧ = t`; hence guarding every quantifier over `T` yields a formula equivalent to the Lean one | equivalence | ✅ **proved** for the `Nat`→`Int` case the encoding implements (`p10_wf_exact`), plus `p10_guarded_quantifier` and `p10_guarded_existential` pinning the `⇒`-vs-`∧` shapes |
| P11 | Theory-operator agreement (`Translation/Theories`) | each emitted SMT operator denotes the same total function as its Lean counterpart — *including at the boundary values* where the two specs differ (`bvudiv`/`bvsdiv` at 0) or where SMT is silent (`div`/`mod` at 0) | equivalence, per operator | 🟡 **Lean side ✅ proven** (9 theorems: `bv_udiv_zero`, `int_div_zero`, `nat_sub_truncates`, `int_div_euclidean`, …); SMT side blocked on P8's semantics |
| P12 | Symbol allocation injectivity (`Translation/Monad`, `symbolFor`) | the atom→symbol map is injective, so distinct Lean atoms (notably same-named constructors of different datatypes) never share an SMT symbol | side-condition | 🟡 |

### Defunctionalization in detail (P4 — the one you flagged)

This is the theorem that most needs to exist, because it is the pass with no
prior art in the Lean SMT tools and the one whose bugs would be silent. Concretely
the pass, given a set of higher-order facts, produces:

- a fresh first-order sort `Fn σ τ` for each arrow sort `σ → τ` that occurs
  applied;
- an uninterpreted `apply_{σ,τ} : Fn σ τ → σ → τ`;
- for each λ-closure `c = λx. body[x, ȳ]` captured with free vars `ȳ`, a
  constructor `mk_c : (types of ȳ) → Fn σ τ` and a **defining axiom**
  `∀ ȳ x, apply_{σ,τ} (mk_c ȳ) x = body[x, ȳ]`.

The obligation, stated in Lean-ish:
```
theorem defunc_equisat (Γ : Facts) :
    (∃ I : Interp, Γ.satisfiedBy I) ↔
    (∃ J : Interp, (defunc Γ ∪ closureAxioms Γ).satisfiedBy J)
```
Proof strategy (the standard applicative-encoding argument): forward, extend any
model `I` of `Γ` to `J` by interpreting `Fn σ τ` as the function graph and
`apply` as function application — the closure axioms hold by β. Backward, from a
model `J` of the encoding, read off Lean functions via `fun x => apply (mk_c ȳ)
x`; the axioms force these to equal the intended bodies, so `Γ` holds. The subtle
points to get right in the proof (and thus the test cases): **extensionality**
(two closures with equal `apply` behaviour need not be equal `Fn` elements unless
we add an extensionality axiom — so the encoding is equisatisfiable, *not*
model-isomorphic, and the theorem must be stated as ∃/∃), and **capture** (the
free-variable list `ȳ` must be complete, or the defining axiom is unsound).

Until P4 is ✅, `crush.ho.mode defunctionalize` is trusted, and a `sat` result
from the *encoded* problem must not be reported as a genuine Lean counterexample
without first checking the closure axioms did not themselves cause the model
(a spurious-model risk the tests must cover).

### How the proofs are staged

We do **not** block Milestone 3's *implementation* on these proofs — the passes
ship first (trusted), with their equivalence theorems stated as `theorem … := by
sorry` in a `Crush/Proofs/` directory so the statement is type-checked and the gap
is visible to `#print axioms`. Discharging the `sorry`s is Milestone 6 ("Verified
soundness"), prioritized P4 → P6 → P8 → P7 (the passes that can silently produce a
wrong `unsat`), then the cheaper definitional ones. This mirrors `bv_decide`'s
history: the reflection loop shipped trusted, then the LRAT checker and bitblaster
were proven, shrinking the TCB incrementally.

## 11. Testing strategy

- **Unit**: IR printing (golden strings), config parsing, name-map idempotence.
- **Extension**: handler registration/priority/override, `crush_map` desugaring.
- **Solver**: round-trip against z3 and cvc5 for `sat`/`unsat`/`unknown`/timeout;
  process-cleanup assertions (no zombies after exceptions).
- **Translation**: per-theory golden SMT scripts; diff-review on changes.
- **End-to-end**: a `crush`-closes-this corpus, plus a `crush`-must-fail corpus
  (unsound patterns must not be silently trusted under `reconstruct`).
- **HO benchmark**: the goals lean-auto rejects, tracked as an xfail→pass list.

Solvers on this machine: `z3` (homebrew), `cvc5` (in `~/Downloads`). CI will pin
both. `vampire`/`zipperposition` are optional TPTP backends for a later phase.
