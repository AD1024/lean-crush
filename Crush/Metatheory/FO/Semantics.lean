import Crush.Metatheory.FO.Core

/-!
# Carriers and valuations for the first-order target

Function-value sorts are interpreted by arbitrary carrier types.  In particular,
they are *not* interpreted as Lean functions: generated `app` and closure symbols
are uninterpreted until the defunctionalization theory constrains them.  This is
the semantics required for the later model-extension proof.

Models and term denotation live in `FO/FamilySemantics.lean`, over the abstract
symbol family; this module holds only what both the sort and term layers share.
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
