# lean-crush

A bridge between **Lean 4** and **SMT solvers**, with first-class higher-order
support and a **user-extensible, metaprogrammed translation layer**.

lean-crush is a from-scratch redesign in the spirit of
[lean-auto](https://github.com/leanprover-community/lean-auto), addressing three
of its core limitations:

- **Higher-order constructs survive to the solver.** lean-auto reifies into a
  higher-order logic but then hard-fails (`"Higher order input?"`) on any
  function-typed argument or partial application when emitting SMT. lean-crush has
  a dedicated HO-elimination layer (defunctionalization / combinators / native
  HO-SMT).
- **You can teach it how to translate your own constants.** Annotate a Lean
  metaprogram with `@[crush_translate]` (or use the `crush_map` sugar); it is
  evaluated at elaboration time to produce SMT. The built-in theory mappings are
  written against the *same* API.
- **Backends and limits are yours to choose.** `set_option crush.backend`,
  `crush.timeout` (hard wall-clock, enforced by lean-crush), `crush.trust`,
  `crush.ho.mode`, and more.

## How it works

The `crush` tactic collects the hypotheses and negated goal, translates them to SMT,
runs the backend under a hard wall-clock timeout, and — by default — **reconstructs a
kernel-checked Lean proof** from the unsat core rather than trusting the solver. The
default `crush.trust` policy is `reconstruct`, which never uses a trust axiom: a goal
the finishers cannot replay is an error, so a translation bug that yielded a false
`unsat` cannot silently close a false goal.

It covers first-order logic; the `Nat`/`Int`/`BitVec`/`String` theories; datatypes,
including fully-applied parametric ones (`Option Int` becomes a real SMT datatype); and
higher-order goals via defunctionalization or native HO on cvc5. A hint grammar
(`crush [lemmas] u[…] d[…]`) points the tactic at lemmas outside the local context,
`@[crush_unfold]` folds a definition's equations into every query, and monomorphization
specializes a polymorphic lemma to the types a query mentions — what lets a bare
`List.append_assoc`, or the TIP list theorems (`rev (rev x) = x` among them), be proved
over an arbitrary element type.

**Case studies** ([`Test/CaseStudies/`](Test/CaseStudies/)) run `crush` on external
corpora: lean-auto's harder test suite, representative Loom/Velvet/Cashmere verification
conditions, and mathlib-scale goals (nonlinear arithmetic, real mathlib datatypes). See
**[`Doc/PLAN.md`](Doc/PLAN.md)** for the architecture and coverage map, and
[`Test/`](Test/) for runnable examples across every supported theory.

## Requirements

- Lean toolchain as pinned in [`lean-toolchain`](lean-toolchain).
- At least one SMT solver on `PATH`: `z3` (≥ 4.12.2), `cvc5`, or `bitwuzla`.

## Quick taste

```lean
import Crush

-- Teach lean-crush a custom translation:
@[crush_translate high]
def mySuccHandler : Crush.TranslationHandler := fun ctx => do
  let .const ``Nat.succ _ := ctx.fn | return none
  match ctx.args with
  | #[n] => return some (.app (.symb "+") #[← ctx.emitTerm n, .lit (.num 1)])
  | _    => return none

-- Or with sugar:
crush_map Nat.add => "+"
crush_map_sort Nat => "Int"

-- Mark a recursive definition so its equations are folded into every `crush`
-- query automatically (relevance-filtered), instead of writing `u[myFn]` each time:
@[crush_unfold]
def myFn : Nat → Nat
  | 0 => 0
  | n + 1 => myFn n + 2
```

Point `crush` at lemmas that are not in context, and combine with a manual `induction`
for inductive goals:

```lean
theorem add_succ (x y : N) : N.add x (N.S y) = N.S (N.add x y) := by
  induction x with
  | Z => crush            -- @[crush_unfold] on N.add supplies its equations
  | S x ih => crush [ih]  -- feed the induction hypothesis as a fact
```

## Build

```sh
lake build          # library
lake build Test.Smoke   # smoke tests (needs z3 on PATH for the round-trip)
```

## Acknowledgements

lean-crush builds on ideas and test material from several projects:

- [lean-auto](https://github.com/leanprover-community/lean-auto) — the tool this
  redesigns; its monomorphization approach, typed SMT IR shape, and test corpus
  informed the design, and its `SmtTranslation` suite is ported in the case studies.
- [Loom](https://github.com/verse-lab/loom) and its verifiers
  [Velvet](https://github.com/verse-lab/velvet) (Dafny-style imperative) and Cashmere
  (effectful monadic) — the source of the verification-condition case study.
- [Veil](https://github.com/verse-lab/veil) — its model-minimization approach
  (`z3model.py`) informs the planned counterexample minimization.
