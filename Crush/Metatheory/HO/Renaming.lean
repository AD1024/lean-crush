import Crush.Metatheory.HO.Core

/-!
# Typed renaming and weakening

Renaming is the binder infrastructure needed for total eta expansion and, later,
closure equations.  Because variables are intrinsically typed, a renaming preserves
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
def lift (r : Renaming source target) :
    Renaming (domain :: source) (domain :: target)
  | _, .here => .here
  | _, .there ref => .there (r ref)

/-- Embed a context underneath one fresh head variable. -/
def weaken : Renaming source (domain :: source) :=
  fun {_} ref => .there ref

/-- Identity renaming. -/
def id : Renaming source source := fun {_} ref => ref

end Renaming

/-- Apply a typed renaming throughout a source term. -/
def Term.rename {signature : Signature} {source target : Context}
    (r : Renaming source target) :
    {ty : Ty} → Term signature source ty → Term signature target ty
  | _, .var ref => .var (r ref)
  | _, .const ref => .const ref
  | _, .boolLit value => .boolLit value
  | _, .not body => .not (body.rename r)
  | _, .and left right => .and (left.rename r) (right.rename r)
  | _, .or left right => .or (left.rename r) (right.rename r)
  | _, .imp left right => .imp (left.rename r) (right.rename r)
  | _, .iff left right => .iff (left.rename r) (right.rename r)
  | _, .eq left right => .eq (left.rename r) (right.rename r)
  | _, .lam body => .lam (body.rename r.lift)
  | _, .app fn argument => .app (fn.rename r) (argument.rename r)
  | _, .forallE body => .forallE (body.rename r.lift)
  | _, .existsE body => .existsE (body.rename r.lift)

/-- Move a term underneath one fresh binder. -/
def Term.weaken (term : Term signature source ty) :
    Term signature (domain :: source) ty :=
  term.rename Renaming.weaken

end Crush.Metatheory
