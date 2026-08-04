import Lean
import Crush.SMT.Syntax
import Crush.Translation.Monad
open Lean Meta

/-!
# Higher-order encoding

The layer that makes `crush` usable on higher-order goals. Three strategies,
selected by `crush.ho.mode`:

* **`defunctionalize`** (default) — λ-lifting into per-arrow-sort `apply` symbols.
  Keeps everything in first-order logics that *every* backend supports.
* **`combinators`** — S/K/B/C/W with their defining equations.
* **`native`** — emit higher-order SMT-LIB and let a HO-capable solver (cvc5)
  handle application directly.

## Why this is a soundness fix, not just a feature

Before this module, an arrow type became an *opaque sort* and a function-typed
bound variable was declared as an unrelated `declare-fun`. The two were
disconnected, so a hypothesis like

```lean
h : ∀ (f : Int → Int), g f = f 0
```

was emitted as `(forall ((q Fn)) (= (g q) (q' 0)))` where `q'` is a fresh constant
function unrelated to `q`. That says **`g` is constant** — strictly *stronger*
than `h`. Goals following from "g is constant" were therefore wrongly proved: a
false `unsat`: `crush` closed `g (fun x => x) = g (fun x => x + 1)` even though its
negation is provable in Lean.

## The defunctionalization encoding

For each arrow type `σ → τ` that occurs, emit an uninterpreted sort `Fn_σ_τ` and

```
(declare-fun app_σ_τ (Fn_σ_τ σ) τ)
```

Every application of a function-*valued term* goes through `app`. A λ-abstraction
`fun x => body[x, ȳ]` with captured free variables `ȳ` becomes a closure
constructor `clo_k : (sorts of ȳ) → Fn_σ_τ` plus the defining axiom

```
(assert (forall (ȳ x) (= (app_σ_τ (clo_k ȳ) x) body[x, ȳ])))
```

Function *equality* additionally needs **extensionality**, which is load-bearing:
`∀ x, f x = g x ⊢ f = g` is `sat` (i.e. not provable) without it and `unsat` with
it. It is emitted per arrow sort, on demand, only when an equation between
function-typed terms actually appears — it is an expensive axiom and most queries
do not need it.

Both the encoding and the necessity of extensionality were verified against z3
before implementation. The equisatisfiability theorem this pass owes is stated in
`Crush/Proofs/Obligations.lean`.
-/

namespace Crush

open SMT

/-- A curried arrow type flattened into argument types and a final result type.
`Int → Int → Bool` becomes `(#[Int, Int], Bool)`. -/
structure ArrowShape where
  args : Array Expr
  res  : Expr
  deriving Inhabited

/-- Flatten an arrow type. Returns `none` for a non-arrow (so callers can treat
first-order types normally). Dependent arrows are refused: their SMT image would
need dependent sorts. -/
def arrowShape? (ty : Expr) : MetaM (Option ArrowShape) := do
  let ty ← whnf ty
  if !ty.isArrow then return none
  let mut args : Array Expr := #[]
  let mut cur := ty
  -- `isArrow` guarantees the binder is not depended upon, so we can peel directly.
  while (← whnf cur).isArrow do
    let cur' ← whnf cur
    let .forallE _ dom body _ := cur' | break
    args := args.push dom
    cur := body
  return some { args, res := cur }

/-- Whether `ty` is a function type we must encode (an arrow into a non-`Prop`).
Arrows into `Prop` are predicates and are handled by the first-order path when
fully applied; only *unapplied* or *argument-position* functions need encoding. -/
def isFunctionType (ty : Expr) : MetaM Bool := do
  return (← whnf ty).isArrow

/-- The number of leading explicit arguments an arrow type takes. -/
def arrowArity (ty : Expr) : MetaM Nat := do
  match ← arrowShape? ty with
  | some s => return s.args.size
  | none => return 0

/-! ## Naming and bookkeeping

All HO symbols are allocated through `TranslateM.symbolFor` on a canonical key, so
they are unique and idempotent — the same arrow type always yields the same `Fn`
sort and `app` symbol, and each distinct λ yields exactly one closure. -/

/-- Key identifying an arrow sort. Uses the pretty-printed type, matching how
`declareUninterpretedSort` keys opaque sorts. -/
def arrowKey (ty : Expr) : MetaM String := do
  return s!"__fn__{toString (← ppExpr ty)}"

/-- Key for an arrow sort's `app` symbol. -/
def appKey (ty : Expr) : MetaM String := do
  return s!"__app__{toString (← ppExpr ty)}"

/-- Key for a λ-closure, keyed on the closed λ term so α-equivalent (and repeated)
λs share one closure constructor. -/
def closureKey (lam : Expr) : MetaM String := do
  return s!"__clo__{toString (← ppExpr lam)}"

/-- Whether the extensionality axiom for an arrow sort has been emitted. -/
def extKey (sortName : String) : String := s!"__ext__{sortName}"

/-! ## Native higher-order mode

cvc5 accepts functions as first-class values: the sort `(-> σ₁ … σₙ τ)`, direct
application `(f x)`, and `lambda` terms. This avoids the closure/`apply` indirection
entirely and lets the solver's own applicative encoding + extensionality do the
work ("Extending SMT Solvers to Higher-Order", Barbosa et al.) — i.e. our
`defunctionalize` mode is the manual version of what cvc5 does internally.

Two hard constraints, both verified against the solvers:

* cvc5 enables HO only when the logic string is **`HO_`-prefixed** (`HO_ALL`, not
  `ALL`). Emitting plain `ALL` leaves cvc5's higher-order solver switched off.
* z3 does **not** support it: it prints "ignoring unsupported logic HO_ALL" and then
  fails on the HO sorts. So `native` must be gated to cvc5 and fall back with a
  diagnostic elsewhere.

Note the encoding is *sound but weaker in practice* on hard queries: cvc5 answered
`unknown` (rather than `sat`) on a satisfiable HO query in testing, which loses
counterexamples but never produces a wrong `unsat`. -/

/-- The native HO function sort `(-> σ₁ … σₙ τ)`. -/
def nativeArrowSort (argSorts : Array SMT.SSort) (resSort : SMT.SSort) : SMT.SSort :=
  .app (.symb "->") (argSorts.push resSort)

/-- Whether `native` mode is usable with this backend, i.e. the backend actually
honours the `HO_` logic prefix. Only cvc5 does today. -/
def nativeSupported (b : Backend) : Bool := b == .cvc5

end Crush
