import Crush.Metatheory.HO.Core

/-!
# Typed renaming and weakening

Renaming is the binder infrastructure needed for total eta expansion and, later,
closure axioms.  Because variables are intrinsically typed, a renaming preserves
types by construction.
-/

namespace Crush.Metatheory

variable {signature : Signature} {source target : Context}
variable {ty domain : Ty}

/-- A type-preserving map between local contexts. -/
abbrev Renaming (source target : Context) :=
  {ty : Ty} → Var source ty → Var target ty

namespace Renaming

/-- Lift a renaming under a binder. -/
def lift (rho : Renaming source target) :
    Renaming (domain :: source) (domain :: target)
  | _, .here => .here
  | _, .there ref => .there (rho ref)

/-- Embed a context underneath one fresh head variable. -/
def weaken : Renaming source (domain :: source) :=
  fun {_} ref => .there ref

/-- Identity renaming. -/
def id : Renaming source source := fun {_} ref => ref

end Renaming

/-- Apply a typed renaming throughout a source term. -/
def Term.rename {signature : Signature} {source target : Context}
    (rho : Renaming source target) :
    {ty : Ty} → Term signature source ty → Term signature target ty
  | _, .var ref => .var (rho ref)
  | _, .const ref => .const ref
  | _, .boolLit value => .boolLit value
  | _, .not body => .not (body.rename rho)
  | _, .and left right => .and (left.rename rho) (right.rename rho)
  | _, .or left right => .or (left.rename rho) (right.rename rho)
  | _, .imp left right => .imp (left.rename rho) (right.rename rho)
  | _, .iff left right => .iff (left.rename rho) (right.rename rho)
  | _, .eq left right => .eq (left.rename rho) (right.rename rho)
  | _, .lam body => .lam (body.rename rho.lift)
  | _, .app fn argument => .app (fn.rename rho) (argument.rename rho)
  | _, .forallE body => .forallE (body.rename rho.lift)
  | _, .existsE body => .existsE (body.rename rho.lift)

/-- Move a term underneath one fresh binder. -/
def Term.weaken (term : Term signature source ty) :
    Term signature (domain :: source) ty :=
  term.rename Renaming.weaken

end Crush.Metatheory
