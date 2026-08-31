import Crush.Metatheory.Datatype.Core
import Crush.Metatheory.FO.Core

/-!
# Typed HO and FO declarations for datatype symbols

Datatype constructors, selectors, and testers remain ordinary applications in
the intrinsically typed term languages. Their datatype-symbol positions are retained separately,
while this module computes the exact type or first-order declaration associated
with each typed datatype reference.
-/

namespace Crush.Metatheory.Datatype

/-- A datatype-list position is also a source de Bruijn constant position. -/
def Ref.toConst {types : List Ty} {type : Ty}
    (ref : Ref types type) : Const types type :=
  match ref with
  | .here => .here
  | .there ref => .there ref.toConst

/-- A source de Bruijn constant position is also a datatype-list position. -/
def Ref.ofConst {types : List Ty} {type : Ty}
    (ref : Const types type) : Ref types type :=
  match ref with
  | .here => .here
  | .there ref => .there (Ref.ofConst ref)

/-- Source type of one constructor field. Recursive fields use the base sort of
their selected datatype declaration. -/
def FieldSort.ty {arity : Nat} (block : Block arity) : FieldSort arity → Ty
  | .base sort => .base sort
  | .data child => .base (block.decl child).sort

/-- First-order sort of one constructor field. -/
def FieldSort.fo {arity : Nat} (block : Block arity) :
    FieldSort arity → FO.FOSort
  | .base sort => .base sort
  | .data child => .base (block.decl child).sort

/-- Source type of a named constructor field. -/
def FieldDecl.ty {arity : Nat} (block : Block arity)
    (field : FieldDecl arity) : Ty :=
  field.sort.ty block

/-- First-order sort of a named constructor field. -/
def FieldDecl.fo {arity : Nat} (block : Block arity)
    (field : FieldDecl arity) : FO.FOSort :=
  field.sort.fo block

/-- Curried source type of a constructor. -/
def CtorDecl.ty {arity : Nat} (block : Block arity)
    (data : DataRef block) (ctor : CtorDecl arity) : Ty :=
  ctor.fields.foldr (fun field result => .arrow (field.ty block) result)
    (.base data.decl.sort)

/-- Exact flattened first-order declaration of a constructor. -/
def CtorDecl.fo {arity : Nat} (block : Block arity)
    (data : DataRef block) (ctor : CtorDecl arity) : FO.SymbolDecl :=
  { args := ctor.fields.map (FieldDecl.fo block)
    result := .base data.decl.sort }

/-- Exact first-order declaration of a selector. -/
def FieldDecl.sel {arity : Nat} (block : Block arity)
    (data : DataRef block) (field : FieldDecl arity) : FO.SymbolDecl :=
  { args := [.base data.decl.sort]
    result := field.fo block }

/-- Exact first-order declaration of a constructor tester. -/
def CtorDecl.test {arity : Nat} (block : Block arity)
    (data : DataRef block) (_ctor : CtorDecl arity) : FO.SymbolDecl :=
  { args := [.base data.decl.sort]
    result := .bool }

/-! ## Canonical datatype source signature -/

/-- Source-constant types for one constructor: constructor, selectors in
field order, then its tester. -/
def CtorDecl.symbolTypes {arity : Nat} (block : Block arity)
    (data : DataRef block) (ctor : CtorDecl arity) : List Ty :=
  ctor.ty block data ::
    ctor.fields.map (fun field =>
      .arrow (.base data.decl.sort) (field.ty block)) ++
    [.arrow (.base data.decl.sort) .bool]

/-- Source-constant types for one datatype declaration. -/
def DataDecl.symbolTypes {arity : Nat} (block : Block arity)
    (data : DataRef block) : List Ty :=
  data.decl.ctors.flatMap (CtorDecl.symbolTypes block data)

/-- Canonical source signature for a complete mutual block. -/
def Block.symbolTypes {arity : Nat} (block : Block arity) : Signature :=
  (List.ofFn fun data : Fin arity => data).flatMap
    (DataDecl.symbolTypes block)

private def CtorRef.inSymbols {arity : Nat} {block : Block arity}
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {type : Ty}
    (inside : Ref (ctor.symbolTypes block data) type) :
    Ref block.symbolTypes type :=
  let dataRef := Ref.ofFn (fun child : Fin arity => child) data
  dataRef.flatMap (DataDecl.symbolTypes block)
    (ctorRef.flatMap (CtorDecl.symbolTypes block data) inside)

/-- Canonical source constant for one constructor. -/
def Block.ctorConst {arity : Nat} {block : Block arity}
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) :
    Const block.symbolTypes (ctor.ty block data) :=
  (ref.inSymbols .here).toConst

/-- Canonical source constant for one selector. -/
def Block.selConst {arity : Nat} {block : Block arity}
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    Const block.symbolTypes
      (Ty.arrow (Ty.base data.decl.sort) (field.ty block)) :=
  let selected := (fieldRef.map fun selected =>
    Ty.arrow (Ty.base data.decl.sort) (selected.ty block)).inLeft
      [Ty.arrow (Ty.base data.decl.sort) .bool]
  (ctorRef.inSymbols (.there selected)).toConst

/-- Canonical source constant for one tester. -/
def Block.testConst {arity : Nat} {block : Block arity}
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) :
    Const block.symbolTypes (Ty.arrow (Ty.base data.decl.sort) .bool) :=
  let tester := Ty.arrow (Ty.base data.decl.sort) .bool
  let headTypes := ctor.ty block data :: ctor.fields.map
    (fun field : FieldDecl arity =>
      Ty.arrow (Ty.base data.decl.sort) (field.ty block))
  let inside : Ref (headTypes ++ [tester]) tester :=
    (Ref.here : Ref [tester] tester).inRight headTypes
  (ref.inSymbols (by
    simpa [CtorDecl.symbolTypes, tester, headTypes] using inside)).toConst

@[simp] theorem CtorDecl.fo_args {arity : Nat} (block : Block arity)
    (data : DataRef block) (ctor : CtorDecl arity) :
    (ctor.fo block data).args = ctor.fields.map (FieldDecl.fo block) := rfl

@[simp] theorem CtorDecl.fo_result {arity : Nat} (block : Block arity)
    (data : DataRef block) (ctor : CtorDecl arity) :
    (ctor.fo block data).result = .base data.decl.sort := rfl

@[simp] theorem FieldDecl.sel_args {arity : Nat} (block : Block arity)
    (data : DataRef block) (field : FieldDecl arity) :
    (field.sel block data).args = [.base data.decl.sort] := rfl

@[simp] theorem FieldDecl.sel_result {arity : Nat} (block : Block arity)
    (data : DataRef block) (field : FieldDecl arity) :
    (field.sel block data).result = field.fo block := rfl

@[simp] theorem CtorDecl.test_args {arity : Nat} (block : Block arity)
    (data : DataRef block) (ctor : CtorDecl arity) :
    (ctor.test block data).args = [.base data.decl.sort] := rfl

@[simp] theorem CtorDecl.test_result {arity : Nat} (block : Block arity)
    (data : DataRef block) (ctor : CtorDecl arity) :
    (ctor.test block data).result = .bool := rfl

end Crush.Metatheory.Datatype
