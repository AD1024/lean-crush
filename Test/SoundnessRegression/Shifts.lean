import Crush

/-!
Bit-vector shift amounts must retain their full value across width conversions.
Large amounts saturate logical shifts and sign-fill arithmetic shifts; smaller
amounts, width boundaries, and narrow operands must preserve exact Lean semantics.
-/

set_option crush.timeout 5

example : True := by
  have h : (1#8) <<< (256#16) = 0#8 := by decide
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : (128#8) >>> (256#16) = 0#8 := by decide
  fail_if_success have : False := by crush
  trivial

example : True := by
  have h : (128#8).sshiftRight' (256#16) = 255#8 := by decide
  fail_if_success have : False := by crush
  trivial

-- Amounts at or above the saturation threshold.
example (x : BitVec 8) : x <<< (256#16) = 0#8 := by crush
example (x : BitVec 8) : x >>> (256#16) = 0#8 := by crush
example : (128#8).sshiftRight' (256#16) = 255#8 := by crush
example : (127#8).sshiftRight' (256#16) = 0#8 := by crush

example (x : BitVec 8) (amount : BitVec 16) (h : amount ≥ 8#16) :
    x <<< amount = 0#8 := by crush
example (x : BitVec 8) (amount : BitVec 16) (h : amount ≥ 8#16) :
    x >>> amount = 0#8 := by crush
example (x : BitVec 8) (amount : BitVec 16) (h : amount ≥ 8#16) :
    x.sshiftRight' amount = x.sshiftRight 8 := by crush

-- Below the threshold, resizing preserves the full amount.
example (x : BitVec 8) (amount : BitVec 16) (h : amount < 8#16) :
    x <<< amount = x <<< (amount.setWidth 8) := by crush
example (x : BitVec 8) (amount : BitVec 16) (h : amount < 8#16) :
    x >>> amount = x >>> (amount.setWidth 8) := by crush
example (x : BitVec 8) (amount : BitVec 16) (h : amount < 8#16) :
    x.sshiftRight' amount = x.sshiftRight' (amount.setWidth 8) := by crush

-- Width boundaries and narrow or same-width amounts.
example (x : BitVec 8) : x <<< (8#16) = 0#8 := by crush
example (x : BitVec 8) : x >>> (8#16) = 0#8 := by crush
example (x : BitVec 1) : x <<< (2#2) = 0#1 := by crush
example (x : BitVec 8) : x <<< (2#3) = x <<< (2 : Nat) := by crush
example (x : BitVec 8) : x >>> (2#3) = x >>> (2 : Nat) := by crush
example (x : BitVec 8) : x.sshiftRight' (2#3) = x.sshiftRight 2 := by crush
example (x : BitVec 8) : x <<< (255#8) = 0#8 := by crush
example (x : BitVec 8) : x.sshiftRight' (255#8) = x.sshiftRight 8 := by crush
