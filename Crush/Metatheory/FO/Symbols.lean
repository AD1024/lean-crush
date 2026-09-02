import Crush.Metatheory.FO.Core

/-!
# Total typed symbol lookup

Utilities for turning proved finite positions into intrinsically typed FO symbol
references.  These are used by the verified defunctionalizer instead of partial
array indexing or name-based lookup.
-/

namespace Crush.Metatheory.FO

universe u
variable {α : Type u} {signature : Signature} {decl : SymbolDecl}

/-- Add a prefix of declarations in front of an existing symbol reference. -/
def Symbol.prepend : (pre : Signature) →
    Symbol signature decl → Symbol (pre ++ signature) decl
  | [], symbol => symbol
  | _ :: tail, symbol => .there (Symbol.prepend tail symbol)

/-- Select a declaration from a mapped signature segment by a proved finite
position. -/
def Symbol.inMap (mapDecl : α → SymbolDecl) (suffix : Signature) :
    (values : List α) → (index : Fin values.length) →
      Symbol (values.map mapDecl ++ suffix) (mapDecl values[index])
  | [], index => Fin.elim0 index
  | _ :: _, ⟨0, _⟩ => .here
  | _ :: tail, ⟨index + 1, bound⟩ =>
      .there (Symbol.inMap mapDecl suffix tail ⟨index, by
        simp only [List.length_cons] at bound
        omega⟩)

/-- Select a declaration from a mapped segment surrounded by arbitrary prefix
and suffix segments. -/
def Symbol.inMappedSegment (pre : Signature) (mapDecl : α → SymbolDecl)
    (suffix : Signature) (values : List α) (index : Fin values.length) :
    Symbol (pre ++ values.map mapDecl ++ suffix) (mapDecl values[index]) := by
  rw [List.append_assoc]
  exact (Symbol.inMap mapDecl suffix values index).prepend pre

end Crush.Metatheory.FO
