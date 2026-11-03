import Lean
import Crush.SMT.Syntax
import Crush.Translation.Monad

/-!
# Higher-order encoding

Shared arrow shapes and structural keys for two higher-order encodings. The default
defunctionalization gives each complete arrow type a function-value sort and an
application symbol taking its flattened arguments. Captured lambdas become closures
with guarded defining equations; function equality adds extensionality on demand.
Applications must remain connected to their quantified function values.

Native mode uses solver function sorts and lambdas, with validity and canonical
extensions enforced by `Translate`. Execution requires cvc5 and an `HO_`-prefixed
logic; backend `none` may emit native scripts for inspection. Structural keys reuse
sorts, application symbols, and closures consistently.
-/

open Lean Meta

namespace Crush

open SMT

/-- A curried arrow type flattened into argument types and a final result type.
`Int → Int → Bool` becomes `(#[Int, Int], Bool)`. -/
structure ArrowShape where
  args : Array Expr
  res  : Expr
  deriving Inhabited

/-- Flatten an arrow type for function-value encoding. Returns `none` for a
non-arrow. Dependent arrows need dependent sorts; proof domains are rejected
because ordinary arrow sorts do not model proof irrelevance or the domain's truth. -/
def arrowShape? (ty : Expr) : MetaM (Option ArrowShape) := do
  let ty ← whnf ty
  if !ty.isArrow then return none
  let mut args : Array Expr := #[]
  let mut cur := ty
  -- `isArrow` guarantees the binder is not depended upon, so we can peel directly.
  while (← whnf cur).isArrow do
    let cur' ← whnf cur
    let .forallE _ dom body _ := cur' | break
    if ← isProp dom then
      throwError "crush: cannot translate a proof-domain function type:{indentExpr ty}"
    args := args.push dom
    cur := body
  return some { args, res := cur }

/-- Whether `ty` is a function type we must encode (an arrow into a non-`Prop`).
Arrows into `Prop` are predicates and are handled by the first-order path when
fully applied; only *unapplied* or *argument-position* functions need encoding. -/
def isFunctionType (ty : Expr) : MetaM Bool := do
  return (← whnf ty).isArrow

/-! ## Naming and bookkeeping -/

/-- Structural key identifying an arrow sort. -/
def arrowKey (ty : Expr) : StructuralKey :=
  { tag := "arrow-sort", typeExprs := #[ty] }

/-- Key for an arrow sort's `app` symbol. -/
def appKey (ty : Expr) : StructuralKey :=
  { tag := "arrow-app", typeExprs := #[ty] }

/-- Key for a λ-closure, keyed on the closed λ term so α-equivalent (and repeated)
λs share one closure constructor. -/
def closureKey (lam : Expr) : StructuralKey :=
  { tag := "closure", exprs := #[lam] }

/-- Whether the extensionality axiom for an arrow sort has been emitted. -/
def extKey (sortName : String) : String := s!"__ext__{sortName}"

/-! ## Native higher-order mode -/

/-- The native HO function sort `(-> σ₁ … σₙ τ)`. -/
def nativeArrowSort (argSorts : Array SMT.SSort) (resSort : SMT.SSort) : SMT.SSort :=
  .app (.symb "->") (argSorts.push resSort)

/-- Whether `native` mode is usable with this backend. cvc5 honours the `HO_`
logic prefix; `none` is also accepted because it only emits the script and is
useful for inspecting or validating native-HO translation. -/
def nativeSupported (b : Backend) : Bool := b == .cvc5
  || b == .none

end Crush
