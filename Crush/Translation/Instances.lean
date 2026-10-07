import Crush.Translation.Monad

open Lean Meta

namespace Crush

/-- Check a numeral against the fixed library dictionary whose value SMT encodes.
Typeclass synthesis is deliberately not used: a higher-priority user instance
must not become the reference instance. Definitional equality admits aliases of
the standard dictionary while rejecting genuinely different interpretations. -/
def hasExpectedOfNatInstance (e : Expr) : MetaM Bool := do
  match_expr e with
  | OfNat.ofNat carrier numeral actual =>
    let carrier ← whnf carrier
    let expected ←
      if carrier.isConstOf ``Nat then
        pure (some (mkApp (mkConst ``instOfNatNat) numeral))
      else if carrier.isConstOf ``Int then
        pure (some (mkApp (mkConst ``instOfNat) numeral))
      else if carrier.isAppOfArity ``BitVec 1 then
        pure (some (mkApp2 (mkConst ``BitVec.instOfNat) carrier.appArg! numeral))
      else
        pure none
    let some expected := expected | return false
    isDefEqReadOnly actual expected
  | _ => return false

end Crush
