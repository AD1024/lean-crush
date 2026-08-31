import Lean

/-!
# Pure translator capture selection

The stateful higher-order encoder and its correctness proof share this exact
first-occurrence traversal.  It is independent of `TranslateM`, which lets proof
objects retain the typed capture witness without creating an import cycle.
-/

namespace Crush

open Lean

namespace collectFVarsOrdered

/-- Accumulator implementation exposed to the correspondence proofs. -/
def go (expression : Expr) (accumulator : Array FVarId) : Array FVarId :=
  match expression with
  | .fvar fvar =>
      if accumulator.contains fvar then accumulator else accumulator.push fvar
  | .app fn argument => go argument (go fn accumulator)
  | .lam _ type body _ => go body (go type accumulator)
  | .forallE _ type body _ => go body (go type accumulator)
  | .letE _ type value body _ => go body (go value (go type accumulator))
  | .mdata _ body => go body accumulator
  | .proj _ _ body => go body accumulator
  | _ => accumulator

end collectFVarsOrdered

/-- All free variables of an expression in deterministic first-occurrence
order. -/
def collectFVarsOrdered (expression : Expr) : Array FVarId :=
  collectFVarsOrdered.go expression #[]

/-- Filter the translator capture order by SMT-local eligibility. -/
def selectClosureCaptures (expression : Expr)
    (eligible : FVarId → Bool) : Array FVarId :=
  (collectFVarsOrdered expression).filter eligible

end Crush
