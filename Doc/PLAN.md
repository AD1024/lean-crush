# lean-crush — Implementation Plan

**A Lean 4 ↔ SMT bridge with first-class higher-order support and a
metaprogrammed, user-extensible translation layer.**

Status: milestones 0–2 complete; 3, 4, and 5 partial (see §9). The `crush` tactic
works end-to-end and, by default, produces kernel-checked proofs rather than
trusting the solver. The extension layer covers term handlers, sort handlers, and
`@[crush_unfold]` auto-unfolding; the hint grammar is in, as is monomorphization —
both of datatypes and of polymorphic *lemmas*, which is what lets the TIP list
theorems be proved over an arbitrary element type. This document is the architecture
and roadmap; §9 is the current status and remaining work.

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
   refinement.)
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
   matched `Expr` becomes SMT, and a user handler *overrides* any built-in mapping
   for the same head (handlers are tried before the structural translator). The
   extension surface is not second-class.
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
| `Crush/Translation/Attr.lean` | `@[crush_translate]` (term) + `@[crush_translate_sort]` (sort) extensions | ⟢ |
| `Crush/Translation/Unfold.lean` | `@[crush_unfold]`/`@[crush_defeq]` auto-unfold + relevance filter | ⟢ |
| `Crush/Translation/Builtins.lean` | `crush_map`/`crush_map_sort` sugar | ⟢ |
| `Crush/Translation/Theories.lean` | BV/String helpers + div-by-zero guards | ⟢ |
| `Crush/Solver/Process.lean` | process mgmt, hard timeout, `unknown` | ⟢ |
| `Crush/SMT/Sexp.lean` | s-expression parser | ⟢ |
| `Crush/SMT/Result.lean` | unsat-core + model parsing | ⟢ |
| `Crush/Reify/Term.lean` | `CTerm`/`CSort` IR (STLC, no `LamWF`) | ⟢ |
| `Crush/Reify/Collect.lean` | hypothesis & goal collection | ⟢ |
| `Crush/Reify/Reify.lean` | `Expr → CTerm`, atom allocation, `DTr` provenance | □ |
| `Crush/Translation/Preprocess.lean` | reduction, skolem prep | □ |
| `Crush/Translation/Monomorphize.lean` | poly *lemma* → ground instances, saturating (datatype mono is in `Translate.lean`) | ⟢ |
| `Crush/Translation/HOEncoding.lean` | HO encoding helpers (defunc ⟢, native ⟢, combinators □) | ⟢ |
| `Crush/Translation/Translate.lean` | driver: `Expr → SMT.Term` via handlers | ⟢ |
| `Crush/Solver/Reconstruct.lean` | unsat-core → Lean proof replay | ⟢ core-directed; □ Alethe |
| `Crush/Frontend/Tactic.lean` | the `crush` tactic + hint grammar (`[…] u[…] d[…]`) | ⟢ |

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

**Sort handlers.** A term handler maps an applied *constant*; a
`@[crush_translate_sort]` handler maps a Lean *type* to an SMT sort, with the same
`TranslationCtx` (the type's head and arguments in `fn`/`args`, `emitSort` to recurse).
This is what lets a user retarget a whole type to a *theory* sort rather than an
uninterpreted one — the motivating case being a finite/total map encoded as SMT's
`(Array K V)`, with `get`/`set` handlers emitting `select`/`store`:

```lean
@[crush_translate_sort]
def amapSort : SortHandler := fun ctx => do
  let .const ``AMap _ := ctx.fn | return none
  let #[k, v] := ctx.args | return none
  return some (.app (.symb "Array") #[← ctx.emitSort k, ← ctx.emitSort v])
```

Without a sort hook a user could remap a type's operations but not the type itself,
so `(select m k)` would be applied to a datatype-sorted `m` and the script would be
ill-sorted. Both hooks are guarded by a cheap "any registered?" check
(`hasTranslationHandlers`/`hasSortHandlers`) so the common no-handler case skips
resolution on the `emitTerm`/`emitSort` hot paths. Demonstrated end-to-end in
`Test/ArrayTheory.lean` (the array read-over-write axioms hold for the user type
purely because the encoding routed it into the Array theory).

**Automatic unfolding — `@[crush_unfold]` / `@[crush_defeq]`.** A recursive definition
`crush` must reason about needs its equation lemmas as facts. Rather than spelling out
`u[f]`/`d[f]` on every call (§7), mark the definition once — like `@[simp]` — and its
equations are folded into every query automatically:

```lean
@[crush_unfold] def add : N → N → N | Z, y => y | S x, y => S (add x y)
theorem add_succ (x y : N) : add x (S y) = S (add x y) := by
  induction x with | Z => crush | S x ih => crush [ih]   -- no u[add] needed
```

Two design points, both load-bearing:
- **Relevance filtering** (`relevantAutoUnfoldLemmas`). A recursive function's equations
  are *quantified* axioms; adding unrelated ones invites solver instantiation loops
  (the divergence documented for guarded recursive datatypes). So a marked definition
  contributes only when reachable from the goal/hypotheses, transitively through the
  marked set. A `@[crush_unfold]` the query never mentions costs nothing.
- **Seed instantiation.** Relevance seeds are the constants in the goal and hypothesis
  types, read *after* `instantiateMVars` — because after a tactic like `induction` the
  goal type carries unassigned metavariables that `getUsedConstants` will not traverse,
  so the recursive function under proof would otherwise be invisible to relevance and
  its equations silently omitted (a bug caught during development, since it makes
  auto-unfold appear to work outside `induction` but fail inside it).

`set_option crush.autoUnfold false` disables the mechanism; explicit `u[…]`/`d[…]` still
work. The attributes live in `Crush/Translation/Unfold.lean`; tested in
`Test/AutoUnfold.lean` and used throughout `Test/TIP.lean`.

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

### 4.3 User handlers override built-ins

The core theory mappings (Bool, `=`, `∧/∨/¬/→`, Nat→Int with well-formedness
side-conditions, Int, BitVec, String, datatypes) live in the **structural
translator** (`Crush/Translation/Translate.lean`), not as handlers — several need
type-directed dispatch (`bitvecTerm?`, `stringTerm?`) that the head-constant handler
shape does not express, and inlining them is simpler and faster than routing every
built-in through `evalConst`.

What matters for extensibility is the *dispatch order*, and it delivers the same
guarantee a dogfooded design would: `emitTerm` tries registered `@[crush_translate]`
handlers (highest priority first) **before** the structural translator, so a user
handler for any constant — including one the built-ins already handle — takes
precedence. There is no privileged built-in path in the sense that matters: anything
a built-in maps, a user can remap. (The earlier plan to register built-ins *as*
handlers, "dogfooding" the API, was dropped; it bought nothing over the ordering
guarantee and cost a `evalConst` indirection per built-in.)

---

## 4b. Monomorphization

Two distinct things go under this name, and lean-crush has one of them:

**Datatype monomorphization — *done*.** A fully-applied parametric type
(`Option Int`, `Int × Int`, `List Bool`) is emitted as a real SMT datatype at that
instantiation. `isSupportedDatatypeApp` checks the applied type is ground and its
constructor fields — instantiated at the type arguments — are all translatable;
`declareDatatype n typeArgs` keys the SMT sort on the head *and* its arguments (so
`Option Int` and `Option Bool` are distinct sorts, and same-named constructors across
instantiations never collide), instantiates each constructor's field types via
`instantiateForall`, and recurses at the same instantiation for nested/recursive
occurrences. `needsWFGuard`/`wfCondition` compose the `Nat` `≥0` guard through type
parameters, so `Option Nat` is not freely generated over negative `Int`s. Type-class
inductives and function/proof-typed fields stay opaque. Tested in
`Test/Monomorphize.lean`.

**Lemma-instantiation saturation — *built* (`Crush/Translation/Monomorphize.lean`).**
A *polymorphic fact* (`∀ α, ∀ x : α, P α x`) is specialized at the types the query
mentions, so it talks about the same SMT symbols as the goal.

Why this is needed is not the obvious "the goal is polymorphic" story, and the real
reason is worth recording. Each SMT symbol is keyed on a constant *together with its
type arguments* — necessarily, since `@f Int` and `@f Bool` have different SMT sorts.
So a polymorphic fact emitted at an abstract instantiation produced symbols
**disjoint from the goal's**, and could not discharge it **even when the goal was
fully ground**:

```smtlib
(assert (forall ((q_1 s_0)) (= (app2_6 List_2_nil q_5) q_5)))  ; the lemma, abstract
(assert (not (= (app2_19 List_20_nil y_24) y_24)))             ; the goal, at Int
```

Two unrelated symbols over two unrelated datatypes. That is why `Test/TIP.lean`'s
list theorems originally had to be stated over a hand-written monomorphic
`append : List Int → List Int → List Int`; they now go through over a polymorphic
`List α`, including `prop_10` (`rev (rev x) = x`), with kernel-checked
reconstruction. `monomorphizeFacts` splits the fact set, collects ground type
candidates (fvars included — an `α : Type` in the local context is a fine
instantiation target, since `List α` is already a real datatype over an opaque
element sort), instantiates leading type binders, discharges any instance-implicit
binders that become determined, and saturates until fixpoint or a bound.

**Soundness direction.** Instantiation only ever *weakens* the asserted set: `P Int`
follows from `∀ α, P α`. Asserting weaker facts can make `unsat` harder to reach,
never easier, so the pass cannot cause a false `unsat` — it can only cost
completeness. Exhausting the budget is therefore a completeness matter, reported as a
warning, not a soundness one. Tested in `Test/LemmaMono.lean`, including that false
goals are still rejected.

A close reading of lean-auto's pass surfaced four concrete traps, which shaped the
implementation:

1. **Instantiation reach must not be structurally capped at the first
   hypothesis.** lean-auto's `LemmaInst.ofLemmaHOL` only makes the *leading*
   non-`Prop` binder prefix instantiable, so in `∀ α, P α → ∀ β, Q β` the `β` is
   forever un-instantiable. **Not yet addressed:** our pass also instantiates only
   the leading telescope, so it shares this boundary. Every equation lemma and
   essentially every real polymorphic lemma leads with its type binders, so this
   covers the payload case; reaching a `β` under a `Prop` binder needs going under
   that binder and re-abstracting. Documented in the module rather than silent.
2. **Fuel must be a meaningful quantity with a loud failure.** lean-auto's
   `saturationThreshold = 1024` counts a *bag of unrelated events* (queue pops +
   group visits + match calls), corresponds to no clean quantity, and **silently
   returns** a truncated set on exhaustion (its own TODO: "Report errors when
   monomorphization fails"). *Done:* `crush.mono.fuel` is a real instance-count
   budget and `crush.mono.rounds` a saturation-round bound, tracked separately;
   hitting either surfaces a **warning** naming the counts, and `MonoReport.dropped`
   names every polymorphic fact left un-instantiated. Never a silent truncation.
   Either option at `0` disables the pass.
3. **Matching needs an index; dedup needs a normal form.** lean-auto has *no*
   term index and *no* congruence closure — matching is a full `Expr` walk with
   `Meta.isDefEq` at every candidate node, and dedup is a linear `isDefEq` scan in
   four separate places, i.e. O(n²) `isDefEq` calls throughout. **Partially
   addressed:** instance dedup is by `Expr` hashing through a `HashSet` rather than
   a linear `isDefEq` scan, so it is not quadratic; candidate *matching* is still a
   linear scan per binder (bounded by the fuel budget). A `DiscrTree` index is the
   remaining refinement, and matters once fact sets get large.
4. **Definitional-equality transparency must be consistent across layers.**
   lean-auto mixes `default` (for `ConstInst`/type-canonicalization) and
   `reducible` (for reduction/reification); its `Test/SetMembershipDefEq.lean`
   documents a concrete crash from exactly that mismatch, "fixed" by silently
   dropping facts. Our pass uses `whnf`/`isDefEq` at the ambient (default)
   transparency throughout, matching the structural translator it feeds, so the two
   layers cannot disagree about whether `MySet α ≡ α → Prop`.

*Not yet:* the `Nonempty`/`Inhabited` → witness conversion for inhabitation (via
`Classical.choice`/`Inhabited.default`), which SMT-LIB's non-empty-sort assumption
wants (see §10, obligation 1); and `DTr`-style provenance is only a `descr` suffix
(`@inst`) rather than a structured derivation, so an instance can be named but not
traced back through its chain.

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
  - `reconstruct` (default) → replay the unsat core into a Lean proof; **fail** if
    replay fails (sound, no new axioms). The default is `reconstruct` precisely so a
    translation bug that yields a false `unsat` cannot silently close a false goal —
    it fails reconstruction and errors, rather than reaching for the axiom.
  - `reconstructOrTrust` → try replay, fall back to trust with a warning; an opt-in
    for goals genuinely beyond the finishers (nonlinear arithmetic, finite-domain
    exhaustiveness) where trusting the solver is acceptable.
- **Reconstruction** (`Crush/Solver/Reconstruct.lean`, built): the **unsat core**
  selects the relevant hypotheses; the goal is rebuilt as the closed implication
  `h₁ → … → hₙ → goal` over only those and handed to `grind`/`omega`/`simp_all`.
  Restricting the context is the point — irrelevant hypotheses are what make those
  tactics time out. Turns "SMT says yes" into a checked proof with no bespoke
  verified checker. Alethe replay (cvc5) is the planned follow-up; it would cover
  the shapes a Lean tactic cannot re-find (§9 M4).

---

## 7. Frontend / tactic

**As built**, the tactic takes the hint grammar below; bare `crush` still uses every
local `Prop` hypothesis and the negated goal. All other behaviour is governed by
`set_option crush.*` (§8), read once into `Config` at entry.

**Hint grammar** (§9 M5 item 1 — *done*):

```
crush [h₁, …, hₙ, *] (u[c₁,…]) (d[c₁,…])
```

- `[…]` an explicit fact list. A `term` element asserts that lemma or hypothesis —
  this is how you point `crush` at a lemma **not** in the local context, which was
  the most visible gap when the tactic was argumentless. A `*` element additionally
  sweeps in all local hypotheses; an explicit list *without* `*` restricts to
  exactly the listed facts (plus the goal), matching Sledgehammer/`auto`.
- `u[c₁,…]` unfold: add each constant's equation lemmas (`getEqnsFor?`, falling back
  to its unfold equation).
- `d[c₁,…]` definitional equalities: add each constant's unfold equation
  (`getUnfoldEqnFor? (nonRec := true)`, the `f x = body` form).
- Parsing/collection lives in `Crush/Frontend/Tactic.lean` (`parseHintList`,
  `parseUOrDs`) and `Crush/Reify/Collect.lean` (`Hints`, `collectFacts`); tested in
  `Test/Hints.lean`.
- The tactic pipeline: collect → monomorphize → HO-encode → translate (handlers) →
  solve → discharge, with `trace.*` classes at each boundary (including
  `crush.mono`) and the full script available via `crush.trace.script` /
  `crush.save`. (A separate preprocessing pass is not yet in the chain — see §9 M5.)

*Not yet in the grammar:* a `* db` named lemma database (there is no `LemDB` yet) and
premise selection.

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
| `crush.trust` | `trust\|reconstruct\|reconstructOrTrust` | `reconstruct` | how `unsat` discharges the goal (default never uses the axiom) |
| `crush.ho.mode` | `defunctionalize\|combinators\|native` | `defunctionalize` | HO elimination strategy |
| `crush.mono.fuel` | `Nat` | `512` | max monomorphization instances |
| `crush.mono.rounds` | `Nat` | `8` | max saturation rounds |
| `crush.logic` | `String` | auto | override SMT-LIB logic |
| `crush.additionalArgs` | `String` | `""` | extra solver flags |
| `crush.save` | `String` | `""` | write script to path |
| `crush.trace.script` | `Bool` | `false` | log generated script |
| `crush.autoUnfold` | `Bool` | `true` | fold `@[crush_unfold]`/`@[crush_defeq]` equations of relevant defs into each query |

Two notes. Enum-valued options take a **string literal**
(`set_option crush.trust "trust"`), since that is how `KVMap.Value` round-trips
them. And `crush.mono.*` bound the lemma-instantiation loop (§4b) — `fuel` is an
instance-count budget, `rounds` a saturation-round bound, and either at `0` disables
the pass; datatype monomorphization is type-directed and needs no fuel.

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
- Datatypes: non-parametric inductives including self-recursive ones, **and
  fully-applied parametric ones** (`Option Int`, `Int × Int`, `List Bool`) via
  datatype monomorphization (below), with distinctness, injectivity, exhaustiveness,
  and selectors. Distinct instantiations get distinct sorts; a `Nat` reached through
  a type parameter (`Option Nat`) still picks up its `≥0` guard.
- Bit-vectors at statically-known widths: arithmetic, bitwise, shifts, rotations,
  unsigned/signed comparisons, `concat`/`extract`/`setWidth`/`signExtend`,
  `toNat`/`toInt`/`ofNat`/`ofInt`, and guarded division-by-zero.
- Strings: `str.++`/`str.len`/`str.prefixof` with correct literal escaping.
- `Int` div/mod (Euclidean, matching SMT-LIB) with an exactness guard at zero.

Tested in `Test/Theories.lean`, `Test/Regression.lean`, `Test/Monomorphize.lean`.

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
base — it was only a search heuristic. This is the default policy (`reconstruct`),
which errors rather than falling back to the axiom when the finishers cannot replay.

*Remaining:* Alethe proof replay for cvc5. The intent was to cover the two shapes the
finishers cannot replay — nonlinear arithmetic and finite-domain exhaustiveness, both
pinned in `Test/Reconstruct.lean`. **Probing cvc5 1.3.4's actual Alethe output on
those exact cases reshaped the scope, and the naive version of this plan does not
work:**

- *Finite-domain exhaustiveness* (the `pigeonhole` case) cannot be produced at all:
  cvc5 answers `unsat` but `--dump-proofs --proof-format-mode=alethe` returns
  `(error "Proof unsupported by Alethe: contains operator DUMMY_SKOLEM")`. The
  datatype-exhaustiveness argument uses skolemization Alethe cannot express, so there
  is no certificate to replay. Alethe replay would **not** cover this pinned case.
- *Nonlinear arithmetic* is more subtle. At the default proof granularity the
  certificate is full of `:rule hole :args ("untranslated rewrite")` steps — 37 of
  them out of 315 — i.e. cvc5 admitting it cannot render its nonlinear rewriting in
  Alethe, which would make the certificate unreplayable. But
  `--proof-granularity=dsl-rewrite` turns every hole into a concrete `rare_rewrite`
  step naming a specific rule (`bool-double-not-elim`, …), giving a hole-free proof.
  So this case *is* replayable in principle — but only with the right granularity
  flag, and it requires implementing a Lean-side checker for the Alethe/RARE rule set
  the proof uses (dozens of distinct rules, each needing a soundness lemma).

Net: Alethe replay is real work with a payoff narrower than first assumed — it buys
the nonlinear shape but not the finite-domain one, and only under a specific cvc5
flag. The cheaper alternative — (a) adding a nonlinear finisher to the existing
core-directed path — was probed and **does not pan out on this toolchain**: no
built-in tactic (`omega`, `grind` incl. `arith := true`, `decide`, `simp_all; omega`)
closes `x*x=4 ∧ x>0 → x=2`, and the tactic that would (`nlinarith`) lives in Mathlib,
which is not a dependency and is far too heavy to add for one edge case. So the only
route to the nonlinear case is the full Alethe checker.

Given all this, **M4 is deprioritized on the evidence**, not merely unstarted: it is
weeks of work (large rule set, each rule needing a proven-sound Lean replay), covers
one of the two motivating pinned cases (not `pigeonhole`), needs
`--proof-granularity=dsl-rewrite`, and — because the default `reconstruct` policy
already makes both cases fail *soundly* as an error rather than a false close — it is
a **completeness** upgrade, not a soundness fix. Worth doing if nonlinear goals become
a common workload; not the best next investment otherwise. See `Test/Reconstruct.lean`
for the pinned cases and this section for the probe findings.

**M5 — Ergonomics & scale. partial.** In rough priority order:
1. The hint grammar (§7): `crush [h₁, …, *] (u[…]) (d[…])`. **done** — a user can now
    point `crush` at a lemma that is not in context, restrict to an explicit fact
    list, and unfold definitions. Tested in `Test/Hints.lean`.
2. Monomorphization (§4b). **done, with two named gaps.** *Datatype* monomorphization
    emits fully-applied parametric types as real SMT datatypes, unlocking M2's
    parametric datatypes. *Lemma-instantiation* monomorphization
    (`Crush/Translation/Monomorphize.lean`) specializes a polymorphic fact at the types
    a query mentions and saturates to a fixpoint under `crush.mono.fuel`/`rounds`,
    reporting rather than silently truncating. This is what let `Test/TIP.lean`'s list
    theorems — `prop_10` (`rev (rev x) = x`) among them — be restated over a
    *polymorphic* `List α`; they previously had to be pinned to `List Int`. Tested in
    `Test/LemmaMono.lean`. Remaining: instantiation reaches only the leading binder
    telescope (a `β` under a `Prop` binder is not reached), and candidate matching is
    still a linear scan rather than a `DiscrTree` index. Both detailed in §4b.
3. Auto-unfold attributes (§4). **done** — `@[crush_unfold]`/`@[crush_defeq]` fold a
    marked definition's equations into every relevant query, so recursive functions in
    a hammer-in-the-loop proof need no per-call `u[…]` hint. Relevance-filtered to avoid
    flooding the solver. Tested in `Test/AutoUnfold.lean`, exercised in `Test/TIP.lean`.
4. Sort handlers (§4.1). **done** — `@[crush_translate_sort]` lets a user retarget a
    type to a theory sort (e.g. a map to SMT `(Array K V)`); `Test/ArrayTheory.lean`.
5. Premise selection on Lean core `LibrarySuggestions`.
6. Portfolio backend, per-call config syntax, richer model printing, docs.
7. **Minimized counterexample models** (`crush.model.minimize`, backlog — wanted by
    downstream users who consume the `sat` model, e.g. PLean). On `sat`, iteratively
    shrink the model to minimal cardinality before printing, so a counterexample is
    the *smallest* witness rather than whatever the solver happened to pick. The
    algorithm (as in Veil's `z3model.py`): after the goal is known `sat`, for each
    uninterpreted sort and relation, assert a cardinality constraint `|S| ≤ n` from
    `n = 1` upward under a push/pop frame, incrementing until `sat` returns, then keep
    that constraint and move to the next sort; `unknown` mid-search aborts to the
    un-minimized model. This needs (a) per-sort cardinality-constraint synthesis
    (`∃ x₁…xₙ, ∀ y, y = x₁ ∨ … ∨ y = xₙ`), (b) an incremental push/pop driver in
    `Crush/Solver/Process.lean` (we already pass `--incremental` to cvc5), and (c)
    feeding the minimized `get-model` back through the existing `parseModel` /
    `formatCounterexample` path. Orthogonal to reconstruction; a printing/diagnostics
    feature, not a soundness one. See also the `unknown`-model note in §11 (cvc5
    withholds a model it computed): both are counterexample-surfacing improvements.

**M6 — Verified soundness. not started (out of scope for now).** An earlier
`Crush/Proofs/` tree stated per-pass equivalence/equisatisfiability obligations, but
it never contained a soundness proof of the translation: there was no
`SMT.Term`→`Prop` interpretation, so the end-to-end statement "solver `unsat` ⇒ the
Lean goal holds" could not even be stated. The proved content was supporting facts
(the `Nat`→`Int` guard is exact; Lean's division/modulus boundary values) and trivial
composition lemmas — none a statement about the translator. That tree has been
**removed** so the repository does not advertise a verified-soundness story it does
not have. Today's soundness guarantee is entirely the `reconstruct` discharge policy
(§6): on the default path the solver's verdict is replayed into a kernel-checked Lean
proof, so the translator and solver are search heuristics, not part of the trusted
base. Reviving a machine-checked ledger would mean building the interpretation layer
and routing the pipeline through a total IR — see the note at the end of §10b for the
prerequisites — and is deferred.

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
closes a goal.

An earlier revision proposed suppressing the guard when a query never touches the
guarded field, to recover completeness. **Probing showed there is little to recover,
so this was not built.** Eight *true* goals over the recursive guarded `NList` — five
purely structural (quantified constructor discrimination, tail injectivity, deep
`cons` chains) and three that reference the guarded `Nat` field (including
`t.len ≥ 0`) — all close today; none diverge. The only divergence is
`must_not_close_nl_field`, which is a *false* goal we *want* rejected, and whose
`unknown` is sound. So the queries that would benefit from suppression already
succeed, and the guard is free when unexercised (constantly-`true` `wf`).
Suppression would trade the obligation-3 unsoundness risk (a false-`unsat` bug this
guard exists to prevent) for a completeness gain the evidence does not show exists —
a bad trade. Left as-is deliberately.

**Methodology.** Every item was settled by evaluating the operator in Lean (`#eval`)
*and* in the solver and comparing, not from memory of either specification. Three
came out differently than the design assumed. New theory support should follow the
same probe-first discipline.

## 10b. Machine-checked soundness (deferred)

§10's obligations are discharged by *testing* plus the `reconstruct` discharge policy
(§6). There is **no** machine-checked meaning-preservation proof of the translation,
and the repository no longer pretends otherwise: an earlier `Crush/Proofs/` tree stated
per-pass `Equivalence`/`Equisat` obligations, but it could not state the theorem that
matters — "solver `unsat` ⇒ the Lean goal holds" — because there was no interpretation
mapping an `SMT.Term` back to a Lean `Prop`. Its proved content was real but beside the
point (the `Nat`→`Int` guard is exact; Lean's division/modulus boundary values; trivial
composition lemmas), and its higher-order "proofs" were tautologies that defined both
sides of the property equal and closed by `rfl`. The whole tree has been removed.

Should a verified ledger be revived, the prerequisites — in dependency order — are:

1. **An interpretation `⟦·⟧ : SMT.Term → Prop`** (and `CSort → Type`), the analogue of
   lean-auto's `LamWF.interp`. Without it no obligation can be *stated*, only named.
2. **Route the pipeline through the pure `CTerm` IR** (`Reify/Term.lean` exists but is
   dead code; the live path is `Expr → SMT.Term` directly). A proof about a `CTerm`
   layer is worthless if nothing runs that layer.
3. **Make the post-reification passes total.** A `partial def` has no unfold equations
   and is opaque to `decide`/`simp` (§10c), so nothing can be proved about it. This is
   feasible for passes over the finite IR, not for the `whnf`-driven reifier itself.
4. **A higher-order value domain** to state defunctionalization (P4) with `app`/`clo`
   *uninterpreted*, so the closure axiom does real work rather than holding by `rfl`.

With (1)–(4) the end-to-end argument mirrors lean-auto's `LamThmValid.getFalse`. This
is essentially rebuilding the verified-checker infrastructure §1 deliberately dropped,
so the higher-leverage investment is instead **Alethe proof replay** (M4), which makes
the *default* discharge path kernel-checked end-to-end. Both are out of scope for the
current feature-completion work.

## 10c. Totality and termination

`partial def` defines a function via `Inhabited` rather than by recursion. It
type-checks, but it has no unfold equations and is opaque to `decide`/`simp`/`rfl`, so
**nothing can be proven about it**. That is disqualifying for any code a proof would
depend on, and it is a prerequisite (§10b item 3) for any future verified ledger.

Everything outside the translator is total, so `termToString.eq_def` and friends
exist. Three obstacles came up, each needing a different technique:

| Obstacle | Where | Fix |
|---|---|---|
| Nested inductive (`Term`/`SSort`/`Sexp` carry `Array` of themselves), so `Array.map`/`foldl` hides the recursive call | `SMT/Print.lean`, `SMT/Result.lean` | recurse through explicit mutual list helpers; `Array.mk.sizeOf_spec` for `sizeOf a.toList < sizeOf a` |
| Recursion on a shrinking `List Char` | `SMT/Sexp.lean` | `termination_by cs.length`; needed a local proof of `(l.dropWhile p).length ≤ l.length`, absent from core |
| Recursion on *another function's output* — `parseList` recurses on what `parseOne` returned | `SMT/Sexp.lean` | explicit fuel, rather than tying the definition to a "consumes ≥ 1 char" theorem about itself |

Two traps worth remembering: an intervening `.map (·.2)` to project a pair defeats
the termination checker just as `foldl` does, so binder lists need their own helpers;
and a `.app f #[]` fast-path *pattern* compiles to a decidable-equality test that
blocks the unfold equations, so it must be written `if args.isEmpty`.

**`Translation/Translate.lean` is the exception and stays `partial`.** Its functions
recurse on an `Expr` while calling `whnf`, and the recursion depth is not bounded by
the input. Given `def Grow : Nat → Type | 0 => Int | n+1 => Grow n × Grow n`, the
input `Grow 12` is a three-node `Expr` but unfolds to 4096 leaves — no measure on
`sizeOf e` dominates that, because the work is driven by definitional unfolding rather
than by the syntax of the argument. In general `whnf` on a user definition need not
terminate; Lean bounds it with `maxRecDepth`, not a proof. This is why Lean's own
elaborator is written the same way.

That is not a soundness gap under the `reconstruct` policy: these are metaprograms that
*construct* SMT terms, and a closed goal is re-proved from the unsat core by a Lean
tactic, so the translator never enters the trusted base.

## 11. Testing strategy

The suite is `Test/`, built by `lake build Test`. Every `theorem` that elaborates is
a passing test; the build must be clean and produce **no `sorry`**.

| File | Covers |
|---|---|
| `Smoke.lean` | IR printing, handler registration via both surfaces, config parse, a live `z3` round-trip |
| `FirstOrder.lean` | the basic end-to-end path: arithmetic, propositional logic, UF congruence |
| `Extension.lean` | user `@[crush_translate]` handlers *fire* and *override* built-ins (the §4.3 contract), plus the `crush_map` sugar |
| `ArrayTheory.lean` | `@[crush_translate_sort]` + term handlers retargeting a user map type to SMT's `(Array K V)` theory (`select`/`store`); the array axioms then hold |
| `Hints.lean` | the hint grammar (§7): explicit lemma hints, `*`, list-as-restriction, `u[…]`/`d[…]` unfolding, and the malformed-hint diagnostics |
| `AutoUnfold.lean` | `@[crush_unfold]`/`@[crush_defeq]`: the attribute fires without a hint, relevance filtering, transitive reach, `crush.autoUnfold` gating, misuse errors |
| `Theories.lean` | `Nat`/`Int`, datatypes (incl. recursive), bit-vectors, strings, and the §10 soundness regressions |
| `Monomorphize.lean` | parametric datatypes: distinct instantiations, nesting, `Nat`-through-parameter guard, selectors/η |
| `LemmaMono.lean` | lemma-instantiation: polymorphic facts specialized at the query's types, saturation, the polymorphic TIP list theorems, `crush.mono.fuel` gating, and that false goals are still rejected |
| `MonoStress.lean` | recursive parametric `Tree`, two-parameter `Map`, nested `FSet`, and all of these combined with higher-order functions |
| `HigherOrder.lean` | λ-arguments, captures, η-expansion, extensionality, partial application |
| `Regression.lean` | an independent corpus migrated from another Lean SMT bridge, plus cases derived from bugs reported against it |
| `Reconstruct.lean` | `#print axioms` assertions — reconstructed theorems must not name `crushSorry` — and the replay boundary |
| `TIP.lean` | inductive theorems from the TIP `prod` benchmarks over a *polymorphic* element type, proved hammer-in-the-loop (manual `induction`, `crush` per case, `@[crush_unfold]` definitions) |
| `Cvc5.lean` | the **cvc5 backend** and **`native` HO mode** (`HO_ALL`, `(-> σ τ)` sorts, `lambda`), which the default `z3`/`defunctionalize` suite never exercises; plus the z3-vs-cvc5 `sat`/`unknown` difference on false HO goals |

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

**CI** (`.github/workflows/ci.yml`) builds the library and the whole suite on every
push and PR against pinned `z3` and `cvc5` releases, and fails on any `sorry` (Lean
reports `sorry` as a *warning*, so `lake build` exits 0 without this guard). Solver
versions are pinned rather than floating because several `#guard_msgs` expectations
contain solver-dependent text, so an unannounced upgrade could redden the build for a
reason unrelated to a code change.

The default backend is `z3`, so most of the suite exercises the
`z3` / `defunctionalize` path. `Test/Cvc5.lean` covers the other two: the **cvc5**
backend (process round-trip, theories, backend-agnostic reconstruction) and the
**`native` higher-order mode** (`HO_ALL` logic, `(-> σ τ)` sorts, `lambda` terms),
which gates on cvc5 and so is tested alongside it. CI installs cvc5, so these run in
CI.

A behavioural difference surfaced there, and investigating it (saving the exact
scripts and running the solvers directly) is worth recording because the naive
reading is wrong. On a *false* higher-order goal, z3 (defunctionalize) returns a
`sat` counterexample, but cvc5 returns `unknown` under *both* HO modes. cvc5 is not
failing to find a model: `(get-model)` after its `unknown` returns a valid
counterexample (`k := λx.7`, `g := λf. ite (f = λx.7) 7 0`, so `g k = 7 ≠ 8`). It
declines to report `sat` because it will not *certify* that model complete over the
infinite function domain the `∀ (q : …)` quantifier ranges over — a conservative
choice, unchanged by `--finite-model-find`/`--fmf-fun`/`--full-saturate-quant`. z3's
model-based quantifier instantiation is willing to commit; cvc5 is not. The scripts
are correct in both encodings; this is a solver-philosophy difference, not a
translation fault. Both verdicts are sound (`unknown` never closes a goal); z3 is
simply more informative on false HO goals.

That cvc5 computes a model it then withholds points at a diagnostics improvement not
yet built: on `unknown`, `(get-model)` output is currently discarded, but it often
holds a *candidate* counterexample that could be surfaced as a tentative,
explicitly-uncertified hint. `vampire`/`zipperposition` are optional TPTP backends
for a later phase.
