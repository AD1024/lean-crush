# lean-crush — Implementation Plan

**A Lean 4 ↔ SMT bridge with first-class higher-order support and a
metaprogrammed, user-extensible translation layer.**

Status: milestones 0–2 complete; 3 and 4 partial (see §9). The `crush` tactic
works end-to-end and, by default, produces kernel-checked proofs rather than
trusting the solver. This document is the architecture and roadmap; §9 is the
current status and remaining work.

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
| `Crush/Translation/HOEncoding.lean` | HO encoding helpers (defunc ⟢, native ⟢, combinators □) | ⟢ |
| `Crush/Translation/Translate.lean` | driver: `Expr → SMT.Term` via handlers | ⟢ |
| `Crush/Solver/Reconstruct.lean` | unsat-core → Lean proof replay | ⟢ core-directed; □ Alethe |
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

The IR in `Crush/SMT/Syntax.lean` is first-order apart from one `Term.lam`
constructor used only by `native`, so `defunctionalize` output maps 1:1 onto what
every solver accepts.

As built, the encoding is not a separate pass over a fact list but a set of
recognizers in the translation driver (`hoTerm?`, `emitClosure`,
`declareArrowSort`, `emitExtensionality`) plus the arrow case in `emitSort`. That
avoids a second traversal and lets the mode be selected per-term; `HOEncoding.lean`
holds the shared naming and shape helpers.

---

## 6. Solving, trust, and reconstruction

- **Process control** (`Crush/Solver/Process.lean`, built): data-driven
  `backendSpec`, our own wall-clock race with a hard `kill`, `try/finally`
  cleanup, and `unknown`/`timeout` as first-class results. Adding a backend is a
  table row.
- **Result parsing** (`Crush/SMT/Sexp.lean` + `Result.lean`, built): an
  s-expression parser feeding a model reader (for `sat` counterexamples) and an
  unsat-core reader (mapping `crush_fact_<id>` back through the provenance table in
  `TranslateState.facts`). The core must be split off the `get-proof` response that
  follows it on the same stream — a proof term mentions the fact names repeatedly,
  so scanning the concatenation yields the proof's internal references, not the
  core.
- **Discharge policy** (`crush.trust`):
  - `trust` → close with the `crushSorry` axiom, no replay attempted.
  - `reconstruct` → replay the unsat core into a Lean proof; **fail** if replay
    fails (sound, no new axioms).
  - `reconstructOrTrust` (default) → try replay, fall back to trust with a
    warning.
- **Reconstruction** (`Crush/Solver/Reconstruct.lean`, built): the **unsat core**
  selects the relevant hypotheses; the goal is rebuilt as the closed implication
  `h₁ → … → hₙ → goal` over only those and handed to `grind`/`omega`/`simp_all`.
  Restricting the context is the point — irrelevant hypotheses are what make those
  tactics time out. Turns "SMT says yes" into a checked proof with no bespoke
  verified checker. Alethe replay (cvc5) is the planned follow-up; it would cover
  the shapes a Lean tactic cannot re-find (§9 M4).

---

## 7. Frontend / tactic

**As built**, the tactic takes no arguments: `crush` uses every local `Prop`
hypothesis and the negated goal. All behaviour is governed by `set_option crush.*`
(§8), read once into `Config` at entry.

**Planned grammar** (§9 M5 item 1, and the most visible current gap — a user cannot
today point `crush` at a lemma that is not already a hypothesis):

```
crush [h₁, …, hₙ] [*] [* db] (u[c₁,…]) (d[c₁,…])
```

- `[…]` explicit facts (terms), `*` = all local hypotheses, `* db` = a named
  lemma database, `u[…]` unfold, `d[…]` definitional equalities.
- The tactic: collect → preprocess → monomorphize → HO-encode → translate
  (handlers) → solve → discharge, with `trace.*` classes at each boundary and
  the full script available via `crush.trace.script` / `crush.save`.

**Two hard lessons from lean-auto's frontend that shape ours:**
- **Report the pipeline, always.** A bare "failed to find proof" that never says
  which backend ran or what the verdict was is the single most common complaint
  about tools in this space, and it happens when the diagnostics exist but sit
  behind trace classes that default off. *Done:* every failure path names the
  verdict, and a `sat` result is surfaced as a **counterexample** parsed from
  `get-model` rather than a generic failure; reconstruction failures name the core
  hypotheses they could not replay. *Not yet:* a one-line success summary
  (backend, wall time, facts sent/dropped) is still trace-only — worth adding with
  the M5 frontend work, since the criticism applies to us until it is.
- **`(set-logic ...)` must be emitted.** lean-auto never emits it (the constructor
  exists but is never constructed), which silently disables theory- and
  HO-specific solver behaviour. `crush` always emits the resolved logic
  (auto-detected or `crush.logic`), and `HO_`-prefixed for `native` HO mode.

Per-call configuration is likewise planned: `crush (timeout := 5) (backend := cvc5)
[hints]` overriding the `set_option` defaults. `Config` is already a value read once
at entry, so this layers on without changing the pipeline.

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

Two notes. Enum-valued options take a **string literal**
(`set_option crush.trust "trust"`), since that is how `KVMap.Value` round-trips
them. And `crush.mono.*` are registered but inert until monomorphization exists
(§9 M5).

---

## 9. Milestones

Legend: **done** · **partial** (what is missing is named) · **todo**.

**M0 — Foundations. done.** SMT IR + printer, config/options, `TranslateM` with
the name map and provenance, `@[crush_translate]` + `crush_map` sugar, solver
process layer with a hard timeout.

**M1 — First-order end-to-end. done.** S-expression parser, unsat-core and model
parsing, fact collection, the structural translator, and the `crush` tactic.

**M2 — Theories. done.**
- `Nat`→`Int` with `≥0` well-formedness constraints and `ite`-truncated `Nat.sub`.
- Datatypes: non-parametric inductives including self-recursive ones, with
  distinctness, injectivity, exhaustiveness, and selectors.
- Bit-vectors at statically-known widths: arithmetic, bitwise, shifts, rotations,
  unsigned/signed comparisons, `concat`/`extract`/`setWidth`/`signExtend`,
  `toNat`/`toInt`/`ofNat`/`ofInt`, and guarded division-by-zero.
- Strings: `str.++`/`str.len`/`str.prefixof` with correct literal escaping.
- `Int` div/mod (Euclidean, matching SMT-LIB) with an exactness guard at zero.

*Remaining:* parametric datatypes (`Prod`/`Option`/`List`) — needs
monomorphization; pinned as expected-to-fail tests in `Test/Regression.lean`.

**M3 — Higher-order. partial.** `defunctionalize` (default) and `native` are done;
`combinators` is not.
- `defunctionalize`: one `Fn` sort and *n*-ary `app` per arrow type; each λ becomes
  a closure with defining axiom `app(clo ȳ, x̄) = body`, parameterized by its
  captures; named and partially-applied functions η-expand into closures.
- Extensionality per arrow sort, emitted on demand (it is a costly quantifier
  alternation, and only equations between function-typed terms need it).
- `native`: `(-> σ τ)` sorts and `lambda` terms under a `HO_`-prefixed logic.
  Gated to cvc5, which is the only backend that honours the prefix; falls back to
  `defunctionalize` with a diagnostic elsewhere.

*Remaining:* `combinators` (S/K/B/C/W). Accepted but warns and falls back. Its
value is as an escape hatch when defunctionalization blows up, so it wants a
workload that actually blows up to tune against. Also unsupported: a
partially-applied term whose *remaining* arity is higher-order.

**M4 — Reconstruction. partial.** Core-directed replay is done; Alethe replay is
not. `Crush/Solver/Reconstruct.lean` uses the unsat core to select the relevant
hypotheses, rebuilds the goal as `h₁ → … → hₙ → goal` over only those, and hands it
to `grind`/`omega`/`simp_all`. On success the solver leaves the trusted computing
base — it was only a search heuristic. This is the default policy
(`reconstructOrTrust`).

*Remaining:* Alethe proof replay for cvc5. It would cover the two shapes the
finishers cannot replay — nonlinear arithmetic and finite-domain exhaustiveness,
both pinned in `Test/Reconstruct.lean` — by replaying the solver's own inferences
instead of depending on a Lean tactic to re-find the argument.

**M5 — Ergonomics & scale. todo.** In rough priority order:
1. The hint grammar (§7): `crush [h₁, …] [*] (u[…]) (d[…])`. The tactic currently
    takes no arguments, so a user cannot point it at a lemma that is not already a
    hypothesis. This is the most visible gap for anyone using the tool.
2. Monomorphization (§4b), which also unlocks M2's parametric datatypes.
3. Premise selection on Lean core `LibrarySuggestions`.
4. Portfolio backend, per-call config syntax, richer model printing, docs.

**M6 — Verified soundness. partial.** See §10b for the ledger. The obligations
that can be stated concretely today are **proved** (`Crush/Proofs/Obligations.lean`
builds with no `sorry`); the per-pass equivalence theorems are stated as named
propositions to discharge once the passes and the denotational semantics exist.

---

## 10. Soundness obligations (the price of dropping the verified checker)

A verified checker *silently absorbs* a set of obligations that become **our**
responsibility in unverified translation code. Each one below is a way the Lean and
SMT semantics can disagree; each has regression tests covering both directions
("must be unsat" and, more importantly, "must not be falsely unsat").

All are addressed. The starred ones were **live false-`unsat` bugs** — `crush`
proved something false — found by differential probing rather than by reading specs.

| # | Obligation | Resolution |
|---|---|---|
| 1 | **Inhabitation.** Every SMT sort is non-empty; Lean types may be empty, so `∀ x : Empty, P` (vacuously true) has no faithful image | `quantifier` refuses an uninhabited domain with a diagnostic. Zero-constructor inductives are excluded from datatype emission (z3 rejects them anyway). The non-dependent case (`Empty → False`) takes the implication path and is independently sound |
| 2 | **`Nat` is not `Int`.** Encoded as `Int`, a `Nat` could go negative; and `Nat.sub` truncates | `≥0` constraint on every `Nat`-typed quantifier and symbol; `Nat.sub` via `ite`. ★ `∀ n:Nat, n-1 < n` was provable before this |
| 3 | **`Nat` inside datatype fields.** SMT datatypes are *freely generated over their field sorts*, so a `Nat` field makes the SMT type strictly larger than the Lean one | A per-datatype `wf_T` predicate carving out the image of the Lean type, guarding every quantifier over `T`, composing transitively. ★ The **true** hypothesis `∀ p : PN, p.x ≥ 0` was unsatisfiable, giving `False` and thence `2+2=5`. Note a per-selector constraint cannot fix this: the problem is the *domain of quantification*, not the selector's range |
| 4 | **Division rounding.** Truncated vs. Euclidean differ on negatives | Verified empirically: Lean's default `Int./`/`%` are *Euclidean*, matching SMT-LIB, so the direct mapping is sound and no dual-operator apparatus is needed |
| 5 | **BitVec width and signedness** | Only statically-known widths translate. Lean's `/`, `%`, `<`, `≤` on `BitVec` are the **unsigned** operations. Shift amounts coerce `Nat`→same-width literal. ★ SMT-LIB *fixes* `bvudiv x 0` to all-ones where Lean gives `0` — a genuine disagreement, not an underspecification, so it is guarded by an `ite` |
| 6 | **Symbol collisions.** Two structures both using the default constructor name `mk` | Constructor/selector symbols are qualified by the owning datatype's (already unique) sort symbol. ★ Two `mk`s and two `mk_sel0`s were being emitted into one script, conflating unrelated types |
| 7 | **String escaping** | Codepoint-accurate `\u{…}`; note `\` is *not* an SMT-LIB escape character, so a backslash is emitted literally |
| 8 | **Function-typed bound variables.** A quantifier over an arrow type | Must range over the encoded function sort with applications routed through `app` (§5). ★ Declaring a fresh symbol for the bound variable left it *disconnected from its own quantifier*, so `∀ (f : Int → Int), g f = f 0` asserted "`g` is constant" — strictly stronger than the hypothesis |

| 9 | **Non-value arguments.** A polymorphic constant's *type* argument and a dependent function's *proof* argument have no SMT counterpart | Both are dropped, and the symbol is keyed on the head *together with* its type arguments so distinct instantiations stay distinct. ★ `@List.length Int []` emitted the type as a `Bool`-sorted **term** fed to an `Int`-returning symbol. Worth stressing: **z3 does not reject ill-sorted input** — it silently accepts `(= x true)` for an `Int`-sorted `x`, so nothing surfaces at the boundary and the only symptom is wrong answers |
| 10 | **`Type` is not `Bool`.** Only `Prop` maps to SMT `Bool` | A larger universe gets an opaque sort. ★ Mapping `Type` to `Bool` puts every Lean type into a two-element set, so three distinct types are forced to collide — `crush` proved `tyfn a = tyfn b ∨ tyfn a = tyfn c ∨ tyfn b = tyfn c`, false for any injective `Nat → Type` |
| 11 | **Arrows that are not implications.** `Empty → False` is a function type, not `p ⇒ q` | The implication path now requires a `Prop` domain; other arrows fall through to the function-sort/quantifier paths. Emitting a non-`Bool` antecedent to `=>` produced ill-sorted output |

Items 1, 3, and 8 are the same shape of bug: a Lean binder's domain mapped to an
SMT domain that is not its faithful image — too large in 3, too small (a single
fixed value) in 8, and wrongly non-empty in 1. Items 9–11 are a second recurring
shape: **a non-value or non-proposition appearing where the encoding expects a term
of a given sort.** Both patterns are worth checking for deliberately whenever new
binder or application handling is added, since neither is caught by the solver.

**Why not just use a `Nat` sort, or define our own?** The obvious first reaction to
the guard machinery, so: SMT-LIB's arithmetic theory defines exactly `Int` and
`Real`. There is **no `Nat` sort** (`(declare-const n Nat)` is an unknown-sort error
in both z3 and cvc5) and no subsort or refinement mechanism, so non-negativity must
be a *constraint* rather than a *type*. Both roll-your-own alternatives measured
worse: a dedicated sort with a bijection to the non-negative `Int`s would make
non-negativity structural, but its mutually-recursive bijection axioms make z3 time
out on the bare consistency check, before any goal; a Peano datatype is exact but
discards linear arithmetic. The guard's cost is also narrower than it looks — a
`Nat`-free datatype gets a constantly-`true` `wf` and no guard is emitted.

Its real cost is recursive datatypes with guarded fields, where the `wf` axiom
becomes recursive and can send the solver into an instantiation loop
(`must_not_close_nl_field` times out even at 30s). That is sound — `unknown` never
closes a goal — but it is a genuine completeness loss. Suppressing the guard when
the query never touches the guarded field would recover most of it.

**Methodology.** Every item was settled by evaluating the operator in Lean (`#eval`)
*and* in the solver and comparing, not from memory of either specification. Three
came out differently than the design assumed. New theory support should follow the
same probe-first discipline.

## 10b. Formal proof obligations (verified soundness roadmap)

§10's obligations are discharged by *testing* plus *trusting the solver*. The
long-term goal is that each pass carries a machine-checked meaning-preservation
theorem, so a chain of passes composes into an end-to-end guarantee and the trust
surface shrinks to the solver's verdict plus the kernel. This is the ledger.

A ✅ means **a Lean proof exists in `Crush/Proofs/Obligations.lean`**, not that a
test passes. That module builds with **no `sorry`**.

Each pass `T` owes one of two strengths:
- **Equivalence** — `∀ I, ⟦Γ⟧_I ↔ ⟦T Γ⟧_I`: the pass neither loses nor invents
  models. For normalization and lowering.
- **Equisatisfiability** — `(∃ I, ⟦Γ⟧_I) ↔ (∃ I', ⟦T Γ⟧_I')`: `T Γ` is unsat iff
  `Γ` is. The correct (weaker) statement whenever a pass introduces symbols a model
  must interpret, since you cannot demand the *same* `I`.

### Status

| # | Pass | Owes | Status |
|---|---|---|---|
| P1 | Preprocessing (β/η, `let`/proj) | equivalence, definitional | 🟡 `P1_obligation` stated; pass not built |
| P2 | `Nat`→`Int` embedding | equivalence, per operator | 🟡 subsumed by P10/P11 for the parts that exist |
| P3 | Monomorphization | equivalence | 🟡 stated; pass not built |
| **P4** | **Defunctionalization** | **equisatisfiability** | 🟡 **core ✅** — `p4a`/`p4b`/`p4c` prove the emitted axioms hold in a canonical model where quantification over the function sort coincides with the Lean function space. Lifting to whole fact lists needs the semantics |
| P5 | Combinator encoding | equisatisfiability | 🔴 mode not implemented |
| P6 | Skolemization | equisatisfiability | 🔴 pass not built |
| P7 | Reification `Expr → CTerm` | equivalence | 🔴 pass not built |
| P8 | `CTerm → SMT.Term` lowering | equivalence | 🔴 blocks P11's SMT half |
| P9 | Inhabitation discharge | side-condition | 🟡 enforced by refusal (§10.1), not yet proven |
| **P10** | **Datatype well-formedness guard** | equivalence | ✅ **proved** for the `Nat`→`Int` case implemented (`p10_wf_exact`), plus `p10_guarded_quantifier`/`p10_guarded_existential` pinning the `⇒`-vs-`∧` shapes |
| P11 | Theory-operator agreement | equivalence, per operator | 🟡 **Lean side ✅** (9 theorems: `bv_udiv_zero`, `int_div_zero`, `nat_sub_truncates`, `int_div_euclidean`, …). SMT side needs P8 |
| P12 | Symbol allocation injectivity | side-condition | 🟡 stated |

Also proved: `equivalence_comp`, `equivalence_id`, `equisat_of_equivalence` — the
composition lemmas that make discharging obligations *per pass* worthwhile instead
of proving one monolithic theorem.

### A lesson about stating obligations

The first draft stated P1–P8 as `theorem … : Equivalence T := by sorry` over a
`variable` pass. Those statements are **false**, not merely unproven: universally
quantified over all `T`, they claim every function on fact lists preserves meaning
(refuted by `T := fun _ => []`). P4a–P4c and P10 had the same defect — quantified
over an arbitrary `app`, or stated over an opaque predicate, so unprovable by
construction.

The `sorry`s were hiding falsehoods rather than tracking open work. Attempting the
proofs is what exposed this. Obligations are therefore now either *proved against a
concrete construction* (P4a–c, P10, P11's Lean half) or recorded as *named
propositions to discharge for a specific pass* (`def P4_obligation (pass) : Prop`),
never as `sorry`-backed universal claims.

### P4 in detail

The pass introduces, for each arrow sort `σ → τ` occurring applied: a sort
`Fn σ τ`, an uninterpreted `app : Fn σ τ → σ → τ`, and per λ-closure
`λx. body[x, ȳ]` a constructor `clo : ȳ → Fn σ τ` with axiom
`∀ ȳ x, app (clo ȳ) x = body[x, ȳ]`.

The standard applicative-encoding argument: forward, extend any model of `Γ` by
interpreting `Fn` as the function graph and `app` as application — the closure
axioms then hold by β. Backward, read Lean functions off a model of the encoding via
`fun x => app (clo ȳ) x`; the axioms force these to be the intended bodies.

Two subtleties the proof must respect, both already reflected in the implementation:
**extensionality** (two closures with equal `app` behaviour need not be equal `Fn`
elements without the axiom — which is why the statement is equisatisfiability, not
model isomorphism) and **capture completeness** (the free-variable list `ȳ` must be
complete, or the defining axiom is unsound).

Until P4 is fully ✅, `defunctionalize` is trusted, and a `sat` result from the
*encoded* problem should not be reported as a genuine Lean counterexample without
checking that the closure axioms did not themselves produce the model.

## 11. Testing strategy

The suite is `Test/`, built by `lake build Test`. Every `theorem` that elaborates is
a passing test; the build must be clean and produce **no `sorry`**.

| File | Covers |
|---|---|
| `Smoke.lean` | IR printing, handler registration via both surfaces, config parse, a live `z3` round-trip |
| `FirstOrder.lean` | the basic end-to-end path: arithmetic, propositional logic, UF congruence |
| `Theories.lean` | `Nat`/`Int`, datatypes (incl. recursive), bit-vectors, strings, and the §10 soundness regressions |
| `HigherOrder.lean` | λ-arguments, captures, η-expansion, extensionality, partial application |
| `Regression.lean` | an independent corpus migrated from another Lean SMT bridge, plus cases derived from bugs reported against it |
| `Reconstruct.lean` | `#print axioms` assertions — reconstructed theorems must not name `crushSorry` — and the replay boundary |

**Negative tests use `#guard_msgs`, not `sorry`.** A goal that is *false* must be
rejected, and the guard pins the rejection message, so a regression that let `crush`
close it fails the build. An earlier `first | (crush; done) | sorry` idiom was
strictly worse: a regression made a warning *disappear*, which nothing enforced.
Switching immediately exposed one test that was passing for the wrong reason (it was
timing out, not being refuted).

`substring := true` matches only the stable message prefix, keeping
solver-dependent counterexample text out of the expectation.

**Known-limitation tests are also pinned**, not omitted — parametric datatypes, the
recursive-`wf` divergence, and the mixed BV/Int query neither solver discharges. Each
expects the current failure, so when a future change makes one work, the build fails
and prompts promoting it to a positive test.

Solvers on this machine: `z3` (homebrew), `cvc5` (in `~/Downloads`). Both are
exercised; CI will pin both. `vampire`/`zipperposition` are optional TPTP backends
for a later phase.
