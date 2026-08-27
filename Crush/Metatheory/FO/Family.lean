import Crush.Metatheory.FO.Core

/-!
# First-order syntax over an abstract typed symbol family

The finite-list FO syntax is the final SMT-facing representation.  Recursive
verified passes are cleaner over a symbol family indexed directly by declaration:
constructing a generated symbol immediately proves its type, independently of
where a later finite allocator places it.

`FamilyTerm.reify` is the total bridge back to finite `FO.Term`, parameterized by
a typed resolver.  The production-link proof will instantiate that resolver with
the collected signature and stable symbol allocation.
-/

namespace Crush.Metatheory.FO

/-- An abstract collection of symbols indexed by their declarations. -/
abbrev SymbolFamily := SymbolDecl → Type

mutual
  inductive FamilyTerm (symbols : SymbolFamily) : Context → FOSort → Type where
    | var {context : Context} {sort : FOSort} :
        Var context sort → FamilyTerm symbols context sort
    | symbol {context : Context} {decl : SymbolDecl} :
        symbols decl → FamilyArgs symbols context decl.args →
        FamilyTerm symbols context decl.result
    | boolLit {context : Context} : Bool → FamilyTerm symbols context .bool
    | not {context : Context} :
        FamilyTerm symbols context .bool → FamilyTerm symbols context .bool
    | and {context : Context} :
        FamilyTerm symbols context .bool → FamilyTerm symbols context .bool →
        FamilyTerm symbols context .bool
    | or {context : Context} :
        FamilyTerm symbols context .bool → FamilyTerm symbols context .bool →
        FamilyTerm symbols context .bool
    | imp {context : Context} :
        FamilyTerm symbols context .bool → FamilyTerm symbols context .bool →
        FamilyTerm symbols context .bool
    | iff {context : Context} :
        FamilyTerm symbols context .bool → FamilyTerm symbols context .bool →
        FamilyTerm symbols context .bool
    | eq {context : Context} {sort : FOSort} :
        FamilyTerm symbols context sort → FamilyTerm symbols context sort →
        FamilyTerm symbols context .bool
    | forallE {context : Context} {domain : FOSort} :
        FamilyTerm symbols (domain :: context) .bool →
        FamilyTerm symbols context .bool
    | existsE {context : Context} {domain : FOSort} :
        FamilyTerm symbols (domain :: context) .bool →
        FamilyTerm symbols context .bool

  inductive FamilyArgs (symbols : SymbolFamily) :
      Context → List FOSort → Type where
    | nil {context : Context} : FamilyArgs symbols context []
    | cons {context : Context} {sort : FOSort} {sorts : List FOSort} :
        FamilyTerm symbols context sort → FamilyArgs symbols context sorts →
        FamilyArgs symbols context (sort :: sorts)
end

abbrev FamilyFormula (symbols : SymbolFamily) (context : Context) :=
  FamilyTerm symbols context .bool
abbrev FamilySentence (symbols : SymbolFamily) := FamilyFormula symbols []
abbrev FamilyTheory (symbols : SymbolFamily) := List (FamilySentence symbols)

/-- Universally close a formula over its entire local context, nearest binder
first. -/
def FamilyFormula.closeForall {symbols : SymbolFamily} :
    {context : Context} → FamilyFormula symbols context → FamilySentence symbols
  | [], formula => formula
  | _ :: _, formula => closeForall (.forallE formula)

mutual
  /-- Replace abstract typed symbols with references into a finite signature. -/
  def FamilyTerm.reify {symbols : SymbolFamily} {signature : Signature}
      (resolve : {decl : SymbolDecl} → symbols decl → Symbol signature decl) :
      {context : Context} → {sort : FOSort} →
        FamilyTerm symbols context sort → Term signature context sort
    | _, _, .var ref => .var ref
    | _, _, .symbol symbol arguments =>
        .symbol (resolve symbol) (arguments.reify resolve)
    | _, _, .boolLit value => .boolLit value
    | _, _, .not body => .not (body.reify resolve)
    | _, _, .and left right => .and (left.reify resolve) (right.reify resolve)
    | _, _, .or left right => .or (left.reify resolve) (right.reify resolve)
    | _, _, .imp left right => .imp (left.reify resolve) (right.reify resolve)
    | _, _, .iff left right => .iff (left.reify resolve) (right.reify resolve)
    | _, _, .eq left right => .eq (left.reify resolve) (right.reify resolve)
    | _, _, .forallE body => .forallE (body.reify resolve)
    | _, _, .existsE body => .existsE (body.reify resolve)

  def FamilyArgs.reify {symbols : SymbolFamily} {signature : Signature}
      (resolve : {decl : SymbolDecl} → symbols decl → Symbol signature decl) :
      {context : Context} → {sorts : List FOSort} →
        FamilyArgs symbols context sorts → Args signature context sorts
    | _, _, .nil => .nil
    | _, _, .cons argument rest =>
        .cons (argument.reify resolve) (rest.reify resolve)
end

end Crush.Metatheory.FO
