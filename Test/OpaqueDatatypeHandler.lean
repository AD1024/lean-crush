import Crush

/-!
# A sort handler can make an opaque structure a datatype

Whether a structure is a datatype is decided by translating its field sorts, so a
`@[crush_translate_sort]` handler for an otherwise untranslatable field type turns
the structure into a datatype (review round 3, C5). The handler is global, so this
test lives in its own module.
-/

open Lean Crush SMT

namespace OpaqueDatatypeHandler

axiom Slot : Nat → Type

-- Each literal `Slot n` becomes its own uninterpreted SMT sort.
@[crush_translate_sort]
def translateSlotSort : SortHandler := fun ctx => do
  let .const ``Slot _ := ctx.fn | return none
  let #[n] := ctx.args | return none
  let .lit (.natVal width) := (← Meta.whnf n) | return none
  let name ← ctx.declare s!"slot-sort-{width}" s!"Slot{width}" fun name =>
    return #[.declSort name 0]
  return some (.app (.symb name) #[])

structure Holder where
  slot : Slot 5

-- Selector equality determines a single-constructor datatype value.
theorem holder_is_datatype (a b : Holder) (h : a.slot = b.slot) : a = b := by crush

end OpaqueDatatypeHandler
