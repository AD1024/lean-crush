import Crush.Translation.Monad

/-!
# Canonical theory-instance validation

Validate numerals and overloaded operators against fixed library dictionaries,
without instance synthesis choosing a user override as the reference. Rigid
definitional equality admits canonical aliases without specializing metavariables;
unsupported carriers, signatures, and dictionaries retain uninterpreted semantics.
-/

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
    isDefEqRigid actual expected
  | _ => return false

/-- Select a fixed dictionary for a structural theory carrier. No search through
the instance environment is involved, including for the heterogeneous wrappers. -/
private def carrierInstance? (carrier : Expr)
    (natName intName bvName : Option Name) : Option Expr := do
  if carrier.isConstOf ``Nat then
    return mkConst (← natName)
  else if carrier.isConstOf ``Int then
    return mkConst (← intName)
  else if carrier.isAppOfArity ``BitVec 1 then
    return mkApp (mkConst (← bvName)) carrier.appArg!
  else
    none

/-- The exact library dictionary for the overloaded operators recognized by the
structural translator. Unsupported carriers or signatures remain uninterpreted. -/
private def expectedOverloadInstance? (e : Expr) : MetaM (Option Expr) := do
  let .const head _ := e.getAppFn | return none
  let args := e.getAppArgs
  let some carrier := args[0]? | return none
  let carrier ← whnf carrier
  let arithmetic :=
    if head == ``HAdd.hAdd then
      some (``instHAdd, ``instAddNat, ``Int.instAdd, ``BitVec.instAdd)
    else if head == ``HSub.hSub then
      some (``instHSub, ``instSubNat, ``Int.instSub, ``BitVec.instSub)
    else if head == ``HMul.hMul then
      some (``instHMul, ``instMulNat, ``Int.instMul, ``BitVec.instMul)
    else if head == ``HDiv.hDiv then
      some (``instHDiv, ``Nat.instDiv, ``Int.instDiv, ``BitVec.instDiv)
    else if head == ``HMod.hMod then
      some (``instHMod, ``Nat.instMod, ``Int.instMod, ``BitVec.instMod)
    else none
  if let some (wrapper, natName, intName, bvName) := arithmetic then
    return (carrierInstance? carrier natName intName bvName).map fun dictionary =>
      mkApp2 (mkConst wrapper [.zero]) carrier dictionary
  let bitwise :=
    if head == ``HAnd.hAnd then some (``instHAndOfAndOp, ``BitVec.instAndOp)
    else if head == ``HOr.hOr then some (``instHOrOfOrOp, ``BitVec.instOrOp)
    else if head == ``HXor.hXor then some (``instHXorOfXorOp, ``BitVec.instXorOp)
    else none
  if let some (wrapper, bvName) := bitwise then
    return (carrierInstance? carrier none none bvName).map fun dictionary =>
      mkApp2 (mkConst wrapper [.zero]) carrier dictionary
  if head == ``LE.le || head == ``GE.ge then
    return carrierInstance? carrier ``instLENat ``Int.instLEInt ``instLEBitVec
  if head == ``LT.lt || head == ``GT.gt then
    return carrierInstance? carrier ``instLTNat ``Int.instLTInt ``instLTBitVec
  if head == ``Neg.neg then
    return carrierInstance? carrier none ``Int.instNegInt ``BitVec.instNeg
  if head == ``Complement.complement then
    return carrierInstance? carrier none none ``BitVec.instComplement
  if head == ``Min.min then
    return carrierInstance? carrier ``instMinNat ``Int.instMin none
  if head == ``Max.max then
    return carrierInstance? carrier ``Nat.instMax ``Int.instMax none
  if head == ``HAppend.hAppend && carrier.isConstOf ``String then
    return some (mkApp2 (mkConst ``instHAppendOfAppend [.zero])
      carrier (mkConst ``instAppendString))
  if carrier.isAppOfArity ``BitVec 1 then
    let width := carrier.appArg!
    let some rightCarrier := args[1]? | return none
    let rightCarrier ← whnf rightCarrier
    if head == ``HShiftLeft.hShiftLeft || head == ``HShiftRight.hShiftRight then
      if rightCarrier.isConstOf ``Nat then
        let name := if head == ``HShiftLeft.hShiftLeft then
          ``BitVec.instHShiftLeftNat else ``BitVec.instHShiftRightNat
        return some (mkApp (mkConst name) width)
      if rightCarrier.isAppOfArity ``BitVec 1 then
        let name := if head == ``HShiftLeft.hShiftLeft then
          ``BitVec.instHShiftLeft else ``BitVec.instHShiftRight
        return some (mkApp2 (mkConst name) width rightCarrier.appArg!)
    if head == ``HAppend.hAppend && rightCarrier.isAppOfArity ``BitVec 1 then
      return some (mkApp2 (mkConst ``BitVec.instHAppendHAddNat) width rightCarrier.appArg!)
  return none

/-- Whether an operator's dictionary has the fixed semantics assigned by SMT.
Checking the dictionary type as well preserves heterogeneous argument/result
carriers; definitional equality allows aliases of the supported instances. -/
def hasExpectedOverloadInstance (e : Expr) (instanceIndex : Nat) : MetaM Bool := do
  let some actual := e.getAppArgs[instanceIndex]? | return false
  let some expected ← expectedOverloadInstance? e | return false
  unless ← isDefEqRigid (← inferType actual) (← inferType expected) do return false
  isDefEqRigid actual expected

end Crush
