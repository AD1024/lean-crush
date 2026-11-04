import Crush.Metatheory.FO.Core

/-!
# First-order syntax over an abstract typed symbol family

Symbols are indexed by declarations, so their types do not depend on positions in a
growing finite signature. Translation therefore needs no signature-membership or
signature-weakening invariant.
Finite reification is outside this development: it requires an injective resolver
only for the symbols actually used, since the full family contains infinitely many
application declarations.
-/

namespace Crush.Metatheory.FO

universe u

/-- An abstract collection of symbols indexed by their declarations.

The universe parameter is needed by symbol families that retain semantic
contracts.  Ordinary syntactic families continue to instantiate it at
`Type`, while a certified symbol may quantify over source models and therefore
inhabit the next universe. -/
abbrev SymbolFamily := SymbolDecl → Type u

mutual
  inductive FamilyTerm (symbols : SymbolFamily.{u}) : Context → FOSort → Type u where
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

  inductive FamilyArgs (symbols : SymbolFamily.{u}) :
      Context → List FOSort → Type u where
    | nil {context : Context} : FamilyArgs symbols context []
    | cons {context : Context} {sort : FOSort} {sorts : List FOSort} :
        FamilyTerm symbols context sort → FamilyArgs symbols context sorts →
        FamilyArgs symbols context (sort :: sorts)
end

abbrev FamilyFormula (symbols : SymbolFamily) (context : Context) :=
  FamilyTerm symbols context .bool
abbrev FamilySentence (symbols : SymbolFamily) := FamilyFormula symbols []
abbrev FamilyTheory (symbols : SymbolFamily) := List (FamilySentence symbols)

/-- Transport a typed family term across equality of its result-sort index. -/
def FamilyTerm.castSort {symbols : SymbolFamily} {context : Context}
    {source target : FOSort} (equality : source = target)
    (term : FamilyTerm symbols context source) :
    FamilyTerm symbols context target :=
  equality ▸ term

/-- Universally close a formula over its entire local context, nearest binder
first. -/
def FamilyFormula.closeForall {symbols : SymbolFamily} :
    {context : Context} → FamilyFormula symbols context → FamilySentence symbols
  | [], formula => formula
  | _ :: _, formula => closeForall (.forallE formula)

end Crush.Metatheory.FO
