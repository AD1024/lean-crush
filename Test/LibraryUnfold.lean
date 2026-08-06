import Crush
import Mathlib

/-!
# Unfolding library definitions

These goals are expected failures without extra configuration in
`Test/CaseStudies/Mathlib.lean`: their library definitions are otherwise translated as
uninterpreted symbols. Registering the definitions with `crush_unfold` exposes operations
that `crush` already supports.

`Int.natAbs`, `Int.sign`, and canonical divisibility instead use targeted SMT
lowerings. `Finset.card` still needs a separate finite-set encoding or normalization
theorem; unfolding it is not sufficient.
-/

open Crush

set_option crush.timeout 20
set_option crush.trust "reconstruct"

namespace LibraryUnfold

section Abs

attribute [local crush_unfold] abs

theorem abs_nonneg (a : Int) : 0 ≤ |a| := by crush

end Abs

section ListLength

attribute [local crush_unfold] List.length

theorem length_eq_zero_iff (l : List Int) : l.length = 0 ↔ l = [] := by crush

end ListLength

section Monotone

attribute [local crush_unfold] Monotone

theorem monotone_apply (f : Int → Int) (hm : Monotone f) (a b : Int) (h : a ≤ b) :
    f a ≤ f b := by crush

end Monotone

end LibraryUnfold
