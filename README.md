# lean-crush

**An SMT hammer for Lean 4.** Write `by crush` and an SMT solver does the tedious part of
the proof for you.

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

When a goal is false, you get a counterexample instead of a failure:

```lean
example (x : Int) : x + 1 = x := by crush
-- crush: the goal is not provable — solver found a counterexample:
--   crush_fact_0 := (not (= (+ x_0 1) x_0))
--   x := 0
```

## Install

Requires the Lean toolchain in [`lean-toolchain`](lean-toolchain) and at least one solver on
your `PATH` — `z3` (≥ 4.12.2), `cvc5` (≥ 1.3), or `bitwuzla`. z3 is the default and enough
to start; cvc5 additionally enables proof replay and native higher-order support.

Add to your `lakefile.lean`:

```lean
require crush from git "https://github.com/AD1024/lean-crush" @ "main"
```

Then `import Crush` and the `crush` tactic is available. Note that the dependency currently
pulls in mathlib as well — only one case-study test file uses it, but Lake fetches it
regardless (`lake exe cache get` gets prebuilt binaries rather than compiling it).

```sh
lake build              # the library
lake build Test.Smoke   # smoke tests (needs z3 for the round-trip)
```

## Using it

`crush` reads every hypothesis in context, so a bare call is usually what you want. To go
further:

```lean
crush [h, myLemma]   -- also use these facts (lemmas need not be in context)
crush [*, myLemma]   -- everything in context, plus a lemma
crush u[myFn]        -- unfold `myFn` via its equation lemmas
```

Mark a definition and its equations come along automatically, with no `u[…]` needed:

```lean
@[crush_unfold]
def myFn : Nat → Nat
  | 0 => 0
  | n + 1 => myFn n + 2
```

`crush` proves goals, not inductions — so drive the induction yourself and let it close the
cases:

```lean
inductive N where | Z | S (n : N)

@[crush_unfold]
def N.add : N → N → N
  | x, .Z   => x
  | x, .S y => .S (N.add x y)

theorem add_succ (x y : N) : N.add x (N.S y) = N.S (N.add x y) := by
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

Under the default policy that same command reports `[Crush.crushSorry]` instead, which is how
you tell the two apart at a glance.

Other behaviour is controlled by `set_option`s (`crush.backend`, `crush.timeout`, and
others); each carries its own documentation where it is declared.

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
  cracks in one shot.
- **reconstructing from the unsat core** — the solver reports which few hypotheses actually
  mattered, and a Lean tactic redoes the argument from just those. This needs no
  certificate, so it works with any backend.

Beyond plain logic and arithmetic, lean-crush covers bitvectors, strings, and your own
inductive types, and it keeps functions-as-arguments alive all the way to the solver — the
case where Lean-to-SMT bridges usually give up. Polymorphic lemmas are specialized to the
types a goal mentions, so a general lemma still applies to your concrete instance.

You can also teach it to translate your own constants, which is how the built-in theory
mappings are themselves written:

```lean
crush_map Nat.add => "+"
crush_map_sort Nat => "Int"
```

For full control, register a metaprogram that runs at elaboration time:

```lean
@[crush_translate high]
def mySuccHandler : Crush.TranslationHandler := fun ctx => do
  let .const ``Nat.succ _ := ctx.fn | return none
  match ctx.args with
  | #[n] => return some (.app (.symb "+") #[← ctx.emitTerm n, .lit (.num 1)])
  | _    => return none
```

## Relation to lean-auto

lean-crush is a from-scratch redesign in the spirit of
[lean-auto](https://github.com/leanprover-community/lean-auto). The three points above are
exactly where it diverges, and in each case lean-auto's limitation is visible in its source:
it reifies into a higher-order logic but then hard-fails (`"Higher order input?"`) on any
function-typed argument while emitting SMT; its Lean→SMT mapping is closed, so extending it
means forking; and its SMT backend has no proof reconstruction yet, either producing no
proof or closing the goal with the `autoSMTSorry` axiom.

## Examples and case studies

[`Test/`](Test/) has runnable examples across every supported theory.
[`Test/CaseStudies/`](Test/CaseStudies/) runs `crush` against external corpora: lean-auto's
harder test suite, Loom/Velvet/Cashmere verification conditions, and mathlib-scale goals
including nonlinear arithmetic and real mathlib datatypes.

## Acknowledgements

lean-crush builds on ideas and test material from several projects:

- [lean-auto](https://github.com/leanprover-community/lean-auto) — the tool this redesigns;
  its monomorphization approach, typed SMT IR shape, and test corpus informed the design,
  and its `SmtTranslation` suite is ported in the case studies.
- [Loom](https://github.com/verse-lab/loom) and its verifiers
  [Velvet](https://github.com/verse-lab/velvet) (Dafny-style imperative) and Cashmere
  (effectful monadic) — the source of the verification-condition case study.
- [Veil](https://github.com/verse-lab/veil) — its model-minimization approach (`z3model.py`)
  informs the planned counterexample minimization.
