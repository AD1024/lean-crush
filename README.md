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

## Status

Early scaffolding. The foundational layers build and are tested; the reification
and tactic layers are in progress. See **[`Doc/PLAN.md`](Doc/PLAN.md)** for the
full architecture and roadmap, and [`Test/Smoke.lean`](Test/Smoke.lean) for
runnable examples of the SMT IR, the extension API, and a live solver round-trip.

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
```

## Build

```sh
lake build          # library
lake build Test.Smoke   # smoke tests (needs z3 on PATH for the round-trip)
```
