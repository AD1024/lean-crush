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
| `Crush/Translation/Builtins.lean` | `crush_map` sugar + core theories | ⟢ (sugar), □ (theories) |
| `Crush/Solver/Process.lean` | process mgmt, hard timeout, `unknown` | ⟢ |
| `Crush/SMT/Parser.lean` | s-expr + result/model/core parsing | □ |
| `Crush/Reify/Term.lean` | `CTerm`/`CSort` IR (STLC, no `LamWF`) | ▷ |
| `Crush/Reify/Collect.lean` | hypothesis & hint collection | □ |
| `Crush/Reify/Reify.lean` | `Expr → CTerm`, atom allocation, `DTr` provenance | □ |
| `Crush/Translation/Preprocess.lean` | reduction, skolem prep | □ |
| `Crush/Translation/Monomorphize.lean` | poly → HOL saturation | □ |
| `Crush/Translation/HOEncoding.lean` | λ-elimination (defunc/comb) | □ |
| `Crush/Translation/Translate.lean` | driver: Expr → Command via handlers | ▷ |
| `Crush/Solver/Reconstruct.lean` | unsat-core → Lean proof replay | □ |
| `Crush/Frontend/Tactic.lean` | the `crush` tactic | □ |

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
- **`native`**. Emit higher-order SMT to a HO-capable backend (cvc5's HOL mode)
  and let the solver handle application/partial application directly. Fastest
  path when the backend supports it; falls back with a diagnostic if the chosen
  backend is first-order-only (z3).

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

**Milestone 1 — First-order end-to-end.**
`SMT/Parser.lean` (results/core), `Reify/Collect.lean`, `Translation/Translate.lean`
(handler dispatch + default structural translator for Bool/Int/UF), the `crush`
tactic in `trust` mode. Goal: `example : ∀ x : Int, x + 0 = x := by crush` closes.

**Milestone 2 — Theories + Nat.**
Built-in handlers for Nat→Int (with well-formedness guards), BitVec, String,
datatypes, `ite`, quantifiers. Regression suite ported from lean-auto's
`Test/SmtTranslation/*`.

**Milestone 3 — Higher-order.**
`HOEncoding.lean`: defunctionalization first, then combinators; `native` mode for
cvc5. This is the headline feature — the benchmark is the set of HO goals that
make lean-auto throw "Higher order input?".

**Milestone 4 — Soundness/reconstruction.**
Unsat-core-driven reconstruction (core → `duper`/`grind`), then Alethe replay for
cvc5. Nat-in-constructor soundness fix that lean-auto's TODO flags.

**Milestone 5 — Ergonomics & scale.**
Monomorphization fuel tuning, premise selection hook, portfolio backend, model
pretty-printing for `sat` (counterexample) reporting, docs and examples.

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

1. **Inhabitation.** SMT-LIB assumes every sort is non-empty; Lean types may be
   empty. Emitting an unconstrained `declare-sort` for a possibly-empty Lean type
   is unsound. Mitigation: only assert `∀`-instances for sorts we can witness
   inhabited (every atom allocated from a real term is inhabited by that term —
   lean-auto's `nonemptyOfAtom` trick); for genuinely-possibly-empty sorts, guard
   quantifiers or refuse. `Empty` short-circuits (`∀ → true`, `∃ → false`).
2. **`Nat` is not `Int`.** When encoding `Nat` as SMT `Int`, every `Nat`-typed
   quantifier needs a `≥ 0` guard, and **truncated subtraction** (`Nat.sub`, where
   `3 - 5 = 0`) must not be emitted as SMT `-`. Emit a guarded/`ite` definition.
3. **`Nat` inside inductive constructors.** lean-auto's TODO flags this as an
   active unsoundness. Datatype selectors returning `Nat` must carry the same
   `≥ 0` well-formedness constraint as top-level `Nat` symbols.
4. **Truncated vs. Euclidean division.** Lean's `Int.div`/`Int.mod` are
   truncated; SMT-LIB's `div`/`mod` are Euclidean. These are *different functions*
   on negatives (lean-auto's `IntConst` carries both `idiv/imod` and `iediv/iemod`
   for exactly this reason). Map each Lean operator to the correct SMT definition,
   not the same-named one.
5. **BitVec width and signedness.** Signed vs. unsigned comparisons, shift
   operand widths (Lean's `shl : BitVec n → Nat` vs SMT's `bvshl : BitVec n →
   BitVec n`), and `bvofNat`/`bvtoNat` boundaries need explicit width handling.

These live in `Crush/Translation/Builtins.lean` as the semantics of the built-in
handlers, and are the reason built-ins are real handlers with access to full
`MetaM` (they must synthesize guards and inspect types), not a static table.

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
