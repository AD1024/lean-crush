import Crush.Metatheory.FO.Family

/-!
# Typed renaming for abstract-symbol first-order syntax

Closure equations are assembled beneath a whole telescope of fresh binders.
This module provides the type-preserving renaming operation needed to move
already translated heads, captures, and argument prefixes into that extended
context.
-/

namespace Crush.Metatheory.FO

variable {symbols : SymbolFamily}
variable {source target third : Context}
variable {sort domain : FOSort}

/-- A sort-preserving map between first-order local contexts. -/
abbrev FamilyRenaming (source target : Context) :=
  {sort : FOSort} → Var source sort → Var target sort

namespace FamilyRenaming

/-- Identity renaming. -/
def id : FamilyRenaming source source := fun {_} ref => ref

/-- Composition of typed renamings. -/
def comp (after : FamilyRenaming target third)
    (before : FamilyRenaming source target) : FamilyRenaming source third :=
  fun {_} ref => after (before ref)

/-- Lift a renaming beneath one binder of the same sort. -/
def lift (r : FamilyRenaming source target) :
    FamilyRenaming (domain :: source) (domain :: target)
  | _, .here => .here
  | _, .there ref => .there (r ref)

/-- Embed a context beneath one fresh head variable. -/
def weaken : FamilyRenaming source (domain :: source) :=
  fun {_} ref => .there ref

/-- Embed a context beneath a telescope of fresh variables.  The prefix is in
de Bruijn context order (nearest binder first). -/
def weakenMany : (added : Context) →
    FamilyRenaming source (added ++ source)
  | [] => id
  | _ :: tail => fun ref => Var.there (weakenMany tail ref)

end FamilyRenaming

mutual
  /-- Apply a typed context renaming throughout an abstract-symbol FO term. -/
  def FamilyTerm.rename {source target : Context}
      (r : FamilyRenaming source target) :
      {sort : FOSort} → FamilyTerm symbols source sort →
        FamilyTerm symbols target sort
    | _, .var ref => .var (r ref)
    | _, .symbol symbol arguments =>
        .symbol symbol (arguments.rename r)
    | _, .boolLit value => .boolLit value
    | _, .not body => .not (body.rename r)
    | _, .and left right => .and (left.rename r) (right.rename r)
    | _, .or left right => .or (left.rename r) (right.rename r)
    | _, .imp left right => .imp (left.rename r) (right.rename r)
    | _, .iff left right => .iff (left.rename r) (right.rename r)
    | _, .eq left right => .eq (left.rename r) (right.rename r)
    | _, .forallE body => .forallE (body.rename (FamilyRenaming.lift r))
    | _, .existsE body => .existsE (body.rename (FamilyRenaming.lift r))

  /-- Apply the same context renaming to every argument in a typed telescope. -/
  def FamilyArgs.rename {source target : Context}
      (r : FamilyRenaming source target) :
      {sorts : List FOSort} → FamilyArgs symbols source sorts →
        FamilyArgs symbols target sorts
    | [], .nil => .nil
    | _ :: _, .cons argument rest =>
        .cons (argument.rename r) (rest.rename r)
end

/-- Move an FO family term beneath one fresh binder. -/
def FamilyTerm.weaken (term : FamilyTerm symbols source sort) :
    FamilyTerm symbols (domain :: source) sort :=
  term.rename FamilyRenaming.weaken

/-- Move an FO argument telescope beneath one fresh binder. -/
def FamilyArgs.weaken {sorts : List FOSort}
    (arguments : FamilyArgs symbols source sorts) :
    FamilyArgs symbols (domain :: source) sorts :=
  arguments.rename FamilyRenaming.weaken

/-- Concatenate typed argument telescopes without changing their source order. -/
def FamilyArgs.append {left right : List FOSort}
    (first : FamilyArgs symbols source left)
    (second : FamilyArgs symbols source right) :
    FamilyArgs symbols source (left ++ right) :=
  match first with
  | .nil => second
  | .cons argument rest => .cons argument (rest.append second)

@[simp] theorem FamilyTerm.rename_var
    (r : FamilyRenaming source target) (ref : Var source sort) :
    (FamilyTerm.var (symbols := symbols) ref).rename r =
      .var (r ref) := rfl

@[simp] theorem FamilyTerm.rename_weaken_var (ref : Var source sort) :
    (FamilyTerm.var (symbols := symbols) ref).weaken (domain := domain) =
      .var (.there ref) := rfl

end Crush.Metatheory.FO
