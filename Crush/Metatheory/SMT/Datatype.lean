import Crush.Metatheory.Datatype.Syntax
import Crush.SMT.Syntax
import Crush.SMT.Quote

/-!
# Native SMT representation of intrinsic datatype blocks

This module is the pure syntactic half of datatype representation. It emits one
monomorphic `declare-datatypes` command for an intrinsic mutual block and retains
one injective namespace for its sorts, constructors, and selectors. Relational
command semantics and model lifting are proved separately.
-/

namespace Crush.Metatheory.SMT.Datatype

open Crush.Metatheory.Datatype

/-- Namespace key for every identifier owned by one datatype block. Natural
positions retain exact source declaration order. -/
inductive NameKey (arity : Nat) where
  | sort : Fin arity → NameKey arity
  | ctor : Fin arity → Nat → NameKey arity
  | sel : Fin arity → Nat → Nat → NameKey arity
  deriving BEq, DecidableEq, Repr

/-- Concrete names for datatype-owned entities and concrete sorts for external
constructor fields. -/
structure Encoding (arity : Nat) where
  name : NameKey arity → String
  baseSort : BaseSort → Crush.SMT.SSort

/-- Datatype sort names distinguish the members of one mutual block. Constructor,
selector, and cross-component freshness is checked once on the exact emitted
symbol list by `CommandWF`, rather than redundantly requiring behavior at
out-of-range natural-number keys. -/
def Encoding.WF {arity : Nat} (encoding : Encoding arity) : Prop :=
  Function.Injective fun data : Fin arity => encoding.name (.sort data)

/-- Nullary raw SMT sort owned by one datatype declaration. -/
def dataSort {arity : Nat} (encoding : Encoding arity)
    (data : Fin arity) : Crush.SMT.SSort :=
  .app (.symb (encoding.name (.sort data))) #[]

/-- Raw SMT representation of one constructor field sort. -/
def fieldSort {arity : Nat} {block : Block arity}
    (encoding : Encoding arity) : FieldSort arity → Crush.SMT.SSort
  | .base sort => encoding.baseSort sort
  | .data child => dataSort encoding child

/-- Raw declaration of one constructor, including positional selectors. -/
def ctorDecl {arity : Nat} {block : Block arity}
    (encoding : Encoding arity) (data : Fin arity) (ctorIndex : Nat)
    (ctor : Datatype.CtorDecl arity) : Crush.SMT.CtorDecl :=
  { name := encoding.name (.ctor data ctorIndex)
    selDecls := (ctor.fields.mapIdx fun fieldIndex field =>
      (encoding.name (.sel data ctorIndex fieldIndex),
        fieldSort (block := block) encoding field.sort)).toArray }

/-- Raw monomorphic body of one datatype declaration. -/
def dataDecl {arity : Nat} {block : Block arity}
    (encoding : Encoding arity) (data : Fin arity) : Crush.SMT.DatatypeDecl :=
  { params := #[]
    ctors := ((block.decl data).ctors.mapIdx fun ctorIndex ctor =>
      ctorDecl (block := block) encoding data ctorIndex ctor).toArray }

/-- Exact ordered entries of one mutual `declare-datatypes` block. -/
def entries {arity : Nat} (block : Block arity)
    (encoding : Encoding arity) :
    Array (String × Nat × Crush.SMT.DatatypeDecl) :=
  ((List.ofFn fun data : Fin arity => data).map fun data =>
    (encoding.name (.sort data), 0,
      dataDecl (block := block) encoding data)).toArray

/-- One native command representing the complete intrinsic block. -/
def command {arity : Nat} (block : Block arity)
    (encoding : Encoding arity) : Crush.SMT.Command :=
  .declDatatypes (entries block encoding)

/-! ## Guarded datatype predicate syntax -/

/-- Conjoin a dynamic list using the same compact shape as production: zero
arguments become `true` and a singleton is not wrapped in `and`. -/
def andAll (terms : Array Crush.SMT.Term) : Crush.SMT.Term :=
  match terms.toList with
  | [] => (smt| true)
  | [term] => term
  | _ => Crush.SMT.Term.symbApp "and" terms

/-- One production selector clause. Constructors without guarded fields
contribute no implication to the surrounding conjunction. -/
def wfClause? (ctor : String) (fields : Array Crush.SMT.Term)
    (value : Crush.SMT.Term) : Option Crush.SMT.Term :=
  if fields.isEmpty then none
  else
    let tester := Crush.SMT.Term.app (.indexed "is" #[.inl ctor]) #[value]
    let body := andAll fields
    some (smt| (=> $tester $body))

/-- Exact production-shaped body of one datatype well-formedness definition.
Each input pairs a constructor symbol with the already encoded guards on its
matching selectors. -/
def wfBody (parts : Array (String × Array Crush.SMT.Term))
    (value : Crush.SMT.Term := .bvar 0) : Crush.SMT.Term :=
  andAll (parts.filterMap fun part => wfClause? part.1 part.2 value)

/-- Exact unary Boolean recursive definition emitted for one datatype member.
The binder's printable name is administrative; its body uses de Bruijn index
zero and therefore has no semantic dependence on that spelling. -/
def wfDef (name binder : String) (sort : Crush.SMT.SSort)
    (parts : Array (String × Array Crush.SMT.Term)) : Crush.SMT.FunDef := {
  name
  args := #[(binder, sort)]
  resSort := Crush.SMT.boolSort
  body := wfBody parts }

@[simp] theorem entries_size {arity : Nat} (block : Block arity)
    (encoding : Encoding arity) :
    (entries block encoding).size = arity := by
  simp [entries]

@[simp] theorem ctor_get {arity : Nat} {block : Block arity}
    (encoding : Encoding arity) {data : DataRef block}
    {ctor : Datatype.CtorDecl arity}
    (ref : CtorRef block data ctor) :
    (dataDecl (block := block) encoding data).ctors[Ref.index ref]? =
      some (ctorDecl (block := block) encoding data (Ref.index ref) ctor) := by
  have get : data.decl.ctors[Ref.index ref]? = some ctor := by
    rw [List.getElem?_eq_getElem (Ref.index_lt ref)]
    simp
  change (block.decl data).ctors[Ref.index ref]? = some ctor at get
  simp [dataDecl, get]

@[simp] theorem sel_get {arity : Nat} {block : Block arity}
    (encoding : Encoding arity) {data : DataRef block}
    {ctor : Datatype.CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    ((ctorDecl (block := block) encoding data
      (Ref.index ctorRef) ctor).selDecls)[Ref.index fieldRef]? =
      some (encoding.name
        (.sel data (Ref.index ctorRef) (Ref.index fieldRef)),
        fieldSort (block := block) encoding field.sort) := by
  simp [ctorDecl]

end Crush.Metatheory.SMT.Datatype
