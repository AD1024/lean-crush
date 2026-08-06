# lean-crush — Implementation Plan

**A Lean 4 ↔ SMT bridge with first-class higher-order support and a
metaprogrammed, user-extensible translation layer.**

Status: milestones 0–2 complete; 3, 4, and 5 partial (see §9). The `crush` tactic
works end-to-end; it closes goals on the solver's verdict by default, and on request
produces kernel-checked proofs by replaying cvc5's Alethe certificate or via the
core-directed finishers (`crush.trust`, `crush.reconstruct`).
The extension layer covers term handlers, sort handlers, and
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
| `Crush/Solver/Reconstruct.lean` | unsat-core → Lean proof replay (finisher ladder) | ⟢ core-directed |
| `Crush/Solver/Alethe.lean` | cvc5 Alethe proof parser | ⟢ |
| `Crush/Solver/AletheTerm.lean` | Alethe `Sexp` → Lean `Expr` (`:named` sharing, `Bool`→`Prop`) | ⟢ |
| `Crush/Solver/AletheReplay.lean` | per-step certificate replay; declines rather than trusts | ⟢ |
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

More than "weakens", the pass is *certifying* when asked to be: each instance is not
a bare proposition but `proof` applied to the chosen type/instance arguments, so it
ships a Lean proof term of exactly that proposition. Under the default `reconstruct`
policy this is re-checked by the kernel during replay for free. Under a trusting
policy (`trust`/`reconstructOrTrust`) nothing else re-checks it — `buildScript`
translates the proposition and never inspects the proof — so `crush.mono.certify`
(off by default) re-verifies `inferType proof ≡ proposition` at generation time and
drops any instance that fails, with a loud warning. A failure indicates a bug in the
pass, not a user error; the option turns "sound by construction" into "checked at
each call" for the modes where the kernel is not already doing it.

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
  verified checker.
  - *Higher-order obligations reconstruct too.* When the verdict is a **function
    equality** `f = g`, the first-order finishers cannot make progress, so the set
    also includes `funext`-prefixed variants (`funext …; simp_all`, `ext; grind`):
    `funext` reduces the goal to its pointwise body and a first-order closer finishes
    it. This is what lets a higher-order `unsat` — a Church-numeral identity,
    β-reduction through a closure, function extensionality — be replayed as a
    kernel-checked proof instead of falling back to the trust axiom
    (`CaseStudies/LeanAuto.lean`'s `church_tower` has `#print axioms` witnessing
    `crushSorry` is absent; the `Test/HigherOrder.lean` shapes reconstruct under the
    default policy for the same reason). The `funext` binder depth is currently
    covered for the common 1–2 arrows; deeper equalities and *non-equational* HO
    verdicts (an ∃ over a function, genuine HO unification) are what Alethe replay is
    for.
  - *Ground-evaluation obligations reconstruct too.* When the refutation turns on
    **computing** a ground term rather than reasoning about it — `String.length "ab" = 2`
    — none of the above finishers apply, since they rewrite and case-split but never
    evaluate. The ladder therefore ends with `subst_vars`-then-`decide`/`rfl` rungs:
    `subst_vars` replaces variables with the ground values the core's equations pin, then
    `decide`/`rfl` computes. This makes the string-length shapes kernel-checked
    (`Test/Reconstruct.lean`), and needs no solver proof, so it works under z3 as well as
    cvc5. The rungs are placed last (`decide` is the most expensive) and fail fast when
    the goal is not a computation.
  - *Certificate replay comes first, when cvc5 supplies one.* Some verdicts are a long
    chain of trivial inferences that no single tactic re-finds (a Boolean pigeonhole, a deep
    EUF conflict). cvc5's Alethe proof *is* that chain, so `Crush/Solver/AletheReplay.lean`
    walks it step by step ahead of the ladder, proving each step from its premises and
    letting the kernel check every one. The rule name is only a tactic *hint*, so soundness
    does not depend on rule coverage: an unreplayable step makes replay **decline** and the
    ladder runs (§9 M4 phase 3).

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
| `crush.trust` | `trust\|reconstruct\|reconstructOrTrust` | `trust` | how `unsat` discharges the goal (the default closes via the auditable `crushSorry` axiom) |
| `crush.reconstruct` | `auto\|alethe\|core` | `auto` | which reconstruction path runs when `crush.trust` asks for one: Alethe certificate replay, the core-directed finisher ladder, or both in order |
| `crush.ho.mode` | `defunctionalize\|combinators\|native` | `defunctionalize` | HO elimination strategy |
| `crush.mono.fuel` | `Nat` | `512` | max monomorphization instances |
| `crush.mono.rounds` | `Nat` | `8` | max saturation rounds |
| `crush.mono.certify` | `Bool` | `false` | type-check each mono instance's proof against its proposition (matters under the default trusting policy; the kernel does this on the `reconstruct` path) |
| `crush.logic` | `String` | auto | override SMT-LIB logic |
| `crush.additionalArgs` | `String` | `""` | extra solver flags |
| `crush.save` | `String` | `""` | write script to path |
| `crush.trace.script` | `Bool` | `false` | log generated script |
| `crush.autoUnfold` | `Bool` | `true` | fold `@[crush_unfold]`/`@[crush_defeq]` equations of relevant defs into each query |
| `crush.profile` | `Bool` | `false` | log a per-phase wall-clock breakdown (collect/monomorphize/translate/solve/reconstruct) |

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
- *Partial application whose result is itself higher-order* is handled: applying a
  function-typed variable to fewer than the flattened `app` arity (`x (y f)` in a
  Church numeral) η-expands to a closure of the residual arrow sort, rather than
  emitting `app` under-applied. This was a translation bug (`unknown constant app_Fn
  (Fn Fn)`) the lean-auto case study surfaced; see §11b.
- Extensionality per arrow sort, emitted on demand (it is a costly quantifier
  alternation, and only equations between function-typed terms need it).
- `native`: `(-> σ τ)` sorts and `lambda` terms under a `HO_`-prefixed logic.
  Gated to cvc5, which is the only backend that honours the prefix; falls back to
  `defunctionalize` with a diagnostic elsewhere.
- Higher-order verdicts now *reconstruct* (kernel-checked), not merely translate:
  the reconstruction finishers include `funext`-prefixed variants, so a function-
  equality `unsat` (Church numerals, β-through-a-closure, funext) closes under the
  default policy without the trust axiom (§6).

*Remaining:* `combinators` (S/K/B/C/W). Accepted but warns and falls back. Its
value is as an escape hatch when defunctionalization blows up, so it wants a
workload that actually blows up to tune against.

**M4 — Reconstruction. partial.** Core-directed replay is done, and Alethe **proof replay**
is now real (phase 3, below). `Crush/Solver/Reconstruct.lean` uses the unsat core
to select the relevant hypotheses, rebuilds the goal as `h₁ → … → hₙ → goal` over only
those, and runs a ladder of finishers on it, taking the first that closes it (§6 maps
each rung to the goal shape it targets). On success the solver leaves the trusted
computing base — it was only a search heuristic. This is the default policy
(`reconstruct`), which errors rather than falling back to the axiom when the ladder
cannot replay. The ladder covers three shapes the finishers reach that a naive
whole-context `grind` would not:

- *Function equalities* (`funext`-prefixed rungs) — a higher-order `unsat` (Church
  numerals, funext) reduces to a pointwise body a first-order closer finishes.
- *Ground evaluation* (`subst_vars; decide`/`rfl`) — a goal that turns on *computing* a
  closed term once the core's equations are substituted (`String.length "ab" = 2`),
  which the reasoning closers structurally cannot do. This is what makes the
  string-length shapes kernel-checked (`Test/Reconstruct.lean`); it needs no solver
  proof, so it applies to z3 and cvc5 alike. (An earlier revision gated these rungs on
  a cvc5 Alethe proof "guide"; measurement showed the gate withheld the win from z3 and
  the proof added nothing over just trying the rungs, so the ladder tries them
  unconditionally — a mis-fitting rung fails fast.)

*Alethe replay — staged, all three phases done.* Built under one invariant: **any step a
replay cannot discharge is a hard failure, never a trusted gap**, so partial coverage stays
sound and merely falls back to the core-directed finisher. Phase 1, the parser
(`Crush/Solver/Alethe.lean`), turns cvc5's `--dump-proofs --proof-format-mode=alethe` output
into an `AletheProof` of `assume`/`step`/`anchor` commands over clauses; it is tested against
verbatim cvc5 output (`Test/Alethe.lean`), including that an `(error …)` reply parses to
`none` so the caller falls back rather than mis-reading. Phase 2 requests the proof behind
`crush.reconstruct`. Phase 3 — the reverse term map and the replay engine — is below.

*Scope findings.* The intent was to cover the two shapes the
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
flag. Two cheaper alternatives to a full checker were probed:

- *A nonlinear finisher* on the core-directed path **does not pan out on this
  toolchain**: no built-in tactic (`omega`, `grind` incl. `arith := true`, `decide`,
  `simp_all; omega`) closes `x*x=4 ∧ x>0 → x=2`, and the tactic that would (`nlinarith`)
  lives in Mathlib, too heavy to add for one edge case. And cvc5 itself cannot prove the
  nonlinear cases — it times out where z3's nlsat succeeds in ~40 ms — so no cvc5 proof
  work reaches them either. The nonlinear shape stays a documented `trust`-mode win.
- *Reading the cvc5 proof to pick finishers* was built and then removed. A measurement
  sweep (quantifier, arithmetic, datatype, bitvector, string) found that on every goal
  where cvc5 returns `unsat`, the existing finishers already reconstruct **except**
  goals turning on ground evaluation, and that `forall_inst` witnesses add nothing
  (`grind` is strictly stronger than cvc5's instantiation on every shape tested). So the
  only new win was the ground-evaluation one — and that needs no proof at all: adding
  `subst_vars; decide`/`rfl` rungs to the ladder closes `s = "ab" ⊢ s.length = 2` and the
  append shape (kernel-checked, `#print axioms` shows no `crushSorry`; `Test/Reconstruct
  .lean`) under **z3 as well as cvc5**. Gating those rungs on a cvc5 proof withheld the
  win from the default backend and added nothing, so the ladder tries them
  unconditionally.

### Phase 3 — proof replay. done (per-step, not per-rule)

`Crush/Solver/AletheReplay.lean` replays a cvc5 Alethe certificate into a Lean proof, and
it is tried **before** the finisher ladder under a reconstructing policy
(`crush.reconstruct auto`, the default; `alethe` runs it with no ladder fallback and `core`
skips it). The insight that made this tractable: an Alethe proof
*decomposes* one hard goal into 20–60 **trivial** steps, so we do not need to re-search —
we restate each step's clause as a Lean proposition, prove it from its premises' proofs
with a small tactic, and carry the result forward. The final empty clause is `False`, which
discharges the negated goal via `Classical.byContradiction`.

**Per-step, not per-rule, is the key design choice.** We do *not* prove each Alethe rule
sound once and for all (lean-auto's reflective-checker approach, ~12k lines). The rule name
is only a *hint* for which tactic to try first; the kernel checks every step's concrete
proof term. So soundness does not depend on rule coverage — a rule we have never heard of
either gets discharged by the generic tactic ladder or makes replay **decline**, and the
finisher ladder runs instead. There is no path in which an unreplayed certificate closes a
goal. (Verified: sabotaging the internal checks does not let a false goal through, because
the solver must first say `unsat` and the kernel must accept the assembled term.)

Supporting pieces: `TranslateState.nameToExpr` (phase 3a — the emitted-symbol → Lean-term
reverse map, since translation is otherwise one-directional) and
`Crush/Solver/AletheTerm.lean` (Alethe `Sexp` → Lean `Expr`, including the `:named`
sharing pre-pass and the `Bool`→`Prop` lifting SMT's single `Bool` sort forces).

*Measured payoff* (2026-08-06). The class replay buys is goals with a hole-free certificate
that the single-shot ladder **cannot** reconstruct: a **Boolean pigeonhole** (four `Bool`s,
~62 steps) and an **EUF conflict** (congruence + literal evaluation, 22 steps). Both were
errors under the default policy before; both are now kernel-checked, `#print axioms` showing
no `crushSorry` (`Test/AletheReplay.lean`). A sweep over quantifier, arithmetic, datatype,
bitvector, and string goals found everything else already reconstructed by the ladder.

*Two shapes remain unreachable, and not for want of coverage:*

- *Finite-domain exhaustiveness over a datatype* (the `pigeonhole` case): cvc5 answers
  `unsat` but cannot express the argument in Alethe, replying `(error "… DUMMY_SKOLEM")` —
  **there is no certificate at all**, so no checker can reach it.
- *Nonlinear arithmetic*: cvc5 cannot prove it (times out where z3's nlsat succeeds in
  ~40 ms), so again no certificate exists. It stays a documented `trust`-mode win.

*Subproof blocks are handled.* `(anchor :step t) (assume t.a0 φ) … (step t … :rule subproof
:discharge (t.a0))` binds `φ` as a real Lean hypothesis, replays the block under it,
abstracts it out with `mkLambdaFVars`, and proves the closing clause from the resulting
implication — so the discharge is kernel-checked, not assumed. This needed the parser to stop
dropping `:discharge` (an ignored discharge would silently lose the antecedent) and
`AletheTerm` to gain quantifier and sort translation.

*Remaining work.* Rules justified by their `:args` rather than their premises —
`forall_inst` (the instantiation witness), `bind`, `sko_ex`, `sko_forall` — are declined.
This is a **soundness-motivated** decline, and it cost a real bug to learn: letting a tactic
guess at `forall_inst` produced a term the elaborator accepted and only the *final kernel*
rejected, surfacing as an opaque "(kernel) application type mismatch" *after* replay had
reported success, with no fallback left. (Neither `Meta.check` nor `inferType` catches it —
they are more permissive than the kernel.) Consuming the witness to instantiate directly is
the next extension; meanwhile such proofs fall back to the ladder, which closes the common
instantiation shapes anyway (`Test/AletheReplay.lean` pins one). `ite` terms and nested
anchors are also declined.

*Scaling: `SymM`.* If replay becomes a bottleneck on large certificates, the engine should
move to Lean's `Lean.Meta.Sym` (`SymM`) monad — de Moura's symbolic-computation monad
(the engine under `grind`/`cbv`): O(1) metavariable-assignment checks, syntactic matching
with proofs and instances ignored (proof-irrelevance + instance-diamond handling we already
do by hand in `defaultApp`/the canonical-instance check), skipped type-checks on ground
terms, and — most relevant — carrying `GrindM` state across many goals so shared hypotheses
are processed once. An Alethe proof is exactly "many small goals over large, similar ground
contexts", the workload `SymM` exists to make fast; lean-auto's own checker is "slow on
large input", the failure mode `SymM` avoids. Our per-step engine currently spawns an
independent tactic call per step on bare `MetaM`, which is the thing `SymM` would amortize.

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

External validation of obligation 1: porting lean-auto's `SmtTranslation` suite
(`Test/LeanAutoPort.lean`) shows lean-auto *proves* `∀ x y : Empty, x = y` via an
encoding its own source flags as unsound ("SMT-LIB assume that all types are
inhabited, while in DTT it's not"), whereas `crush` declines it — the inhabitation
guard doing exactly its job. The same port also drove two BitVec translation gaps to
ground (`zeroExtend`, `extractLsb hi lo`), now fixed. The deeper case studies (§11b)
drove three more fixes — mutually-recursive datatype emission, polymorphic-hint
re-abstraction, and the monomorphization candidate filter — each found by porting a
goal and diagnosing the emitted SMT.

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
the *default* discharge path kernel-checked end-to-end.

**Why there is no cheap per-call closure certification** (the analogue of
`crush.mono.certify` for defunctionalization). Monomorphization can be certified per
call because each instance is a genuine pair of *Lean* objects — a proof term and a
proposition — so `isDefEq (inferType proof) prop` is a real kernel-checkable
property. A closure axiom `∀ ȳ x̄, app(clo ȳ, x̄) = ⟦body⟧` has no such pair: `app`,
`clo`, and `⟦body⟧` are SMT artifacts with no Lean counterpart. Its only failure mode
is `⟦body⟧` mistranslating the λ body — i.e. translation faithfulness — which is
exactly prerequisite (1)/(4) above, not a `rfl`. A "closure certify" that emitted a
Lean lemma `∀ x, L x = body` and closed it by `rfl` would check only Lean's own
β-reduction, comparing the translator to itself; it was considered and rejected as
vacuous. Note this is not a gap on the default path: under `reconstruct`, closure
axioms are never consumed by the Lean replay (`coreHypotheses` reads only real
`Fact` proofs; `grind` does its own β-reduction), so defunctionalization is already
outside the trusted base there. The reliance exists only under `trust` /
`reconstructOrTrust`, and closing *that* needs the full interpretation layer.

Both the ledger and closure certification are out of scope for the current
feature-completion work.

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
| `HigherOrder.lean` | λ-arguments, captures, η-expansion, extensionality, partial application; all reconstruct under the default policy (kernel-checked, `#print axioms` pins no `crushSorry`), thanks to the `funext` finishers |
| `Regression.lean` | an independent corpus migrated from another Lean SMT bridge, plus cases derived from bugs reported against it |
| `Reconstruct.lean` | `#print axioms` assertions — reconstructed theorems must not name `crushSorry` — and the replay boundary |
| `TIP.lean` | inductive theorems from the TIP `prod` benchmarks over a *polymorphic* element type, proved hammer-in-the-loop (manual `induction`, `crush` per case, `@[crush_unfold]` definitions) |
| `Cvc5.lean` | the **cvc5 backend** and **`native` HO mode** (`HO_ALL`, `(-> σ τ)` sorts, `lambda`), which the default `z3`/`defunctionalize` suite never exercises; plus the z3-vs-cvc5 `sat`/`unknown` difference on false HO goals |
| `Alethe.lean` | the Alethe proof **parser** (M4 phase 1) against verbatim cvc5 output: command/clause/`:named` structure, premise reading, the empty-clause conclusion, and that an `(error …)` reply parses to `none` |
| `AletheReplay.lean` | Alethe **proof replay** (M4 phase 3): the measured payoff class — Boolean pigeonhole and EUF conflict, which the finisher ladder cannot reconstruct — closes kernel-checked (`#print axioms`, no `crushSorry`); plus the decline cases (no certificate, unprovable, false goal) pinned so a certificate is never taken on faith, and the path-selection cases (`crush.reconstruct core`/`alethe`, plus z3, which emits no certificate) |
| `LeanAutoPort.lean` | goals ported from lean-auto's `SmtTranslation/` suite (BoolNatInt, BitVec, String, inductive/enum, recursive-with-unfold): demonstrates the same corpus translates and solves, and pins the `Empty`-type cases where we are deliberately *sound* and lean-auto documents itself unsound |
| `CaseStudies/LeanAuto.lean` | the *harder* lean-auto corpus (§11b): mutually-recursive and single-ctor datatypes, HO Church numerals (kernel-reconstructed), polymorphic lemmas, leading-∀ matching, `Function.comp_def`, and the Paxos consensus goal — each filed as handled / sound-refusal / known-gap; drove four translation fixes and closed three of four gaps |
| `CaseStudies/Loom.lean` | representative Loom verification conditions (§11b): GCD/MaxElem/IsSorted/SumOfDigits/sqrt/cbrt/binary-search arithmetic, quantified array invariants, an array-update VC, and Cashmere balance invariants; the Mathlib-bound `Multiset`/`Finset` VCs reduce (hammer-in-the-loop) to arithmetic residuals `crush` closes |

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

## 11b. Case studies (`Test/CaseStudies/`)

Two downstream projects that use lean-auto were taken as external validation:
lean-auto's own harder test corpus, and [Loom](https://github.com/AD1024/loom) (a
framework for building program verifiers, which dispatches its verification
conditions through lean-auto). Neither can literally `require` lean-crush — the three
projects are on incompatible Lean toolchains (Loom on v4.24.0 + Mathlib, lean-auto on
v4.32.0-rc1, lean-crush on v4.32.2) and a Lean `require` forces one shared toolchain,
and Loom's Velvet examples have moved to a separate repo — so each case study instead
**ports representative goals** to `crush` and maps coverage into three honest buckets:
*handled* (a real closed theorem), *sound refusal* (a true goal `crush` declines
rather than close unsoundly, pinned with `#guard_msgs`), and *known gap* (out of reach
today, with the emitted-SMT diagnosis).

**What the case studies confirmed works.** Mutually-recursive and single-constructor
datatypes; HO goals over a *ground* function space; polymorphic `List` lemmas and
leading-∀ matching; `Function.comp_def` composition (under the default `reconstruct`
policy, so kernel-checked); and — for Loom — the full arithmetic spine of the Velvet
examples (GCD termination via `Nat.mod_lt`, MaxElem/IsSorted quantified array
invariants, the nonlinear sqrt/cbrt/binary-search postconditions, insertion-sort's
array-update invariant expressed as the pointwise equation a WP generator emits) and
Cashmere's balance invariants. Most Loom VCs are core-Lean arithmetic + quantified
`Array`/`List` goals with no Mathlib in the *goal*, so a `loom_solver` → `crush` swap
(a one-`macro_rules` change, the seam Cashmere already uses for `aesop`) would target
them directly.

**Four `crush` improvements the case studies drove**, each surfaced by probing a
ported goal, diagnosed from the emitted SMT, and fixed with a regression:

1. *Mutually-recursive datatypes* (`Translate.lean`, `declareDatatype`). Each member
   of a mutual block used to be emitted as its own `declare-datatypes`, so `tree`'s
   selector referenced `treelist` before it was declared and z3 rejected the script
   (`unknown sort 'treelist'`). Now the whole `iv.all` block is emitted as one grouped
   `declare-datatypes` with every sort in scope, and all `wf_T` predicates are declared
   before any axiom references a sibling's. The `declDatatypes` command already took an
   array; the non-mutual path (a singleton `all`) is unchanged.

2. *Polymorphic hints connect to the goal* (`Collect.lean`). Elaborating a bare library
   lemma (`crush [List.append_assoc]`) auto-binds its implicit `{α}` into a
   metavariable, so the fact arrived as `∀ (as … : List ?m), …` — the leading *type*
   binder gone, reading as monomorphic over an abstract sort disconnected from the
   goal, so monomorphization never fired and the lemma could not discharge anything.
   Term hints are now re-abstracted with `abstractMVars (levels := false)`, restoring
   the `∀ α`-binder monomorphization specializes at the query's types. `levels :=
   false` is load-bearing: a rigid universe parameter would not unify `Type u` with the
   candidate's `Type 0`. This is what lets `crush [List.append_assoc]` prove list-append
   associativity at all — previously only a hand-written monomorphic `append` worked.

3. *Monomorphization candidates must be data sorts* (`Monomorphize.lean`,
   `isGroundType`). Exposed by fix 2: a universe-polymorphic lemma binds `{γ : Sort
   u}`, and `Sort u` unifies with `Sort 0`, so a predicate application `P x : Prop` in
   the goal was collected as a candidate and `Function.comp_def`'s type binders
   instantiated at it — emitting a proposition where a sort was expected (`(... False)`
   as a sort) and cross-producting into ≈500 junk instances across its three binders.
   Candidates are now restricted to genuine data types (in `Type _`, not `Prop`/`Sort`,
   not arrows). Purely a completeness restriction — it only shrinks the instance set,
   so it cannot cause a false `unsat`.

4. *Partial application of a function-typed variable* (`Translate.lean`, `hoTerm?`).
   The defunctionalized `app` symbol is n-ary over an arrow's *fully flattened*
   argument list, so a higher-order term applying a function-valued bound variable to
   *fewer* arguments than that arity (`x (y f)` in a Church numeral, where `x :
   (A→A)→(A→A)` has flattened arity 2 but gets one argument) emitted `app`
   under-applied — an ill-sorted term z3 rejected (`unknown constant app_Fn (Fn Fn)`),
   and the result is a *function* value, not a base-sort one. Such a partial
   application is now η-expanded to a closure of the residual arrow sort, so the result
   is a proper `Fn` value and the script is well-formed. This closed the Church-numeral
   goal (§11b gaps below): once the SMT is valid, z3 discharges the whole tower in
   ~40 ms — the earlier "times out" reading was the malformed script, not solver
   difficulty. Native HO mode is unaffected (cvc5 applies functions directly).

**Gaps the case studies closed.** Three of the four originally-documented gaps turned
out to be reachable and are now passing tests:

* *Higher-order Church numerals* (over a ground function space) — closed by fix 4
  above.
* *The Paxos consensus goal* — translates cleanly, but the ≈60 ∀ / 14 ∃ deep
  alternation defeats z3's and cvc5's *default* E-matching. cvc5 with
  `--full-saturate-quant` (instantiation-based, passed via `crush.additionalArgs`)
  closes it in ~0.2 s. The finding was that the goal was reachable with the right
  solver flag, not blocked on the trigger support `crush` lacks; lean-auto reaches it
  via its own `trigger` annotations, a different route to the same end.
* *`Option.orElse` with a λ* — the bare goal is a sound refusal (no defining axiom for
  `orElse`), but `crush u[Option.orElse]` supplies the equation and closes it, the
  `crush` analogue of lean-auto's `d[Option.orElse]`.

**Gaps that remain** (roadmap, not regressions): the Church tower over an *abstract
universe* (`{α : Sort u}` bound *inside* each hypothesis — the nested-binder
monomorphization boundary; the ground-type version is handled); and Loom's
Mathlib-bound VCs, where the `Multiset`/`Finset` *type* has no first-order SMT theory —
but even there the split is hammer-in-the-loop, not a dead end: the structural lemma
(`Finset.sum_range_succ`, the permutation lemma) is applied in Lean by `grind`/`aesop`
and `crush` finishes the arithmetic residual, demonstrated on core-Lean renderings in
`CaseStudies/Loom.lean`.
