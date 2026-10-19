import Crush.Metatheory.FO.Core

/-!
# Carriers and valuations for the first-order target

Function-value sorts have arbitrary carrier types; application and closure symbols
remain uninterpreted until constrained by the generated theory. This module supplies
carriers and valuations shared with the abstract-symbol models and term denotation
in `FO/FamilySemantics.lean`.
-/

namespace Crush.Metatheory.FO

/-- The carriers of an FO model.  A distinct arbitrary carrier is supplied for
every complete source arrow type. -/
structure Carriers where
  Base : BaseSort → Type
  Fn : Ty → Ty → Type
  baseNonempty : (sort : BaseSort) → Nonempty (Base sort)
  fnNonempty : (domain codomain : Ty) → Nonempty (Fn domain codomain)

namespace FOSort

/-- Interpretation of a first-order sort in a collection of model carriers. -/
@[reducible] def Denote (carriers : Carriers) : FOSort → Type
  | .bool => Prop
  | .base sort => carriers.Base sort
  | .fn domain codomain => carriers.Fn domain codomain

end FOSort

/-- Curried semantic type of a first-order symbol declaration. -/
def SymbolDenote (carriers : Carriers) : List FOSort → FOSort → Type
  | [], result => result.Denote carriers
  | argument :: arguments, result =>
      argument.Denote carriers → SymbolDenote carriers arguments result

/-- A valuation assigns values to the typed target variables. -/
abbrev Valuation (carriers : Carriers) (context : Context) :=
  {sort : FOSort} → Var context sort → sort.Denote carriers

namespace Valuation

def extend {carriers : Carriers} {context : Context} {sort : FOSort}
    (valuation : Valuation carriers context) (value : sort.Denote carriers) :
    Valuation carriers (sort :: context)
  | _, .here => value
  | _, .there ref => valuation ref

def empty (carriers : Carriers) : Valuation carriers [] :=
  fun {_} ref => nomatch ref

end Valuation

end Crush.Metatheory.FO
