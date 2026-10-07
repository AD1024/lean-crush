import Crush

set_option linter.unusedVariables false

/-! A literal denotes the value supplied by its `OfNat` dictionary. -/

example (inst : OfNat Int 5) (h : @OfNat.ofNat Int 5 inst = 7) : True := by
  fail_if_success have : False := by crush
  trivial

example (inst : OfNat Nat 5) (h : @OfNat.ofNat Nat (nat_lit 5) inst = 7) : True := by
  fail_if_success have : False := by crush
  trivial

example (inst : OfNat (BitVec 8) 5)
    (h : @OfNat.ofNat (BitVec 8) 5 inst = 7#8) : True := by
  fail_if_success have : False := by crush
  trivial

namespace NonstandardIntNumeral
instance (priority := high) : OfNat Int 5 := ⟨7⟩
example : True := by
  have h : (5 : Int) = 7 := rfl
  fail_if_success have : False := by crush
  trivial
end NonstandardIntNumeral

namespace NonstandardBitVecNumeral
instance (priority := high) : OfNat (BitVec 8) 5 := ⟨7#8⟩
example : True := by
  have h : (5 : BitVec 8) = 7#8 := rfl
  fail_if_success have : False := by crush
  trivial
end NonstandardBitVecNumeral

-- Reducible aliases of standard dictionaries still receive numeral semantics.
abbrev standardIntFive : OfNat Int 5 := instOfNat
abbrev standardNatFive : OfNat Nat 5 := instOfNatNat 5
abbrev standardBitVecFive : OfNat (BitVec 8) 5 := BitVec.instOfNat

#eval show Lean.MetaM Unit from do
  for (carrier, dictionary) in #[
      (Lean.mkConst ``Int, Lean.mkConst ``standardIntFive),
      (Lean.mkConst ``Nat, Lean.mkConst ``standardNatFive),
      (Lean.mkApp (Lean.mkConst ``BitVec) (Lean.mkNatLit 8), Lean.mkConst ``standardBitVecFive)] do
    let value := Lean.mkApp3 (Lean.mkConst ``OfNat.ofNat [Lean.Level.zero])
      carrier (Lean.mkNatLit 5) dictionary
    unless ← Crush.hasExpectedOfNatInstance value do
      throwError "standard numeral dictionary alias was rejected"

example (x : Int) (h : x = @OfNat.ofNat Int 5 standardIntFive) : x + 1 = 6 := by
  crush
example (x : Nat) (h : x = @OfNat.ofNat Nat 5 standardNatFive) : x + 1 = 6 := by
  crush
example (x : BitVec 8) (h : x = @OfNat.ofNat (BitVec 8) 5 standardBitVecFive) : x + 1#8 = 6#8 := by
  crush
