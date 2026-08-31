import Crush.Metatheory.Datatype.Semantics
import Crush.Metatheory.Datatype.Syntax
import Crush.Metatheory.HO.Semantics

/-!
# Datatype-aware source models

The intrinsically typed higher-order term language continues to use ordinary constants. A
`Symbols` record classifies selected constants as datatype constructors,
selectors, and testers. A `IsFreeDatatypeModel` witness then states their canonical meaning.
This keeps all existing term recursion unchanged while strengthening the class
of source models used for datatype-aware satisfiability.
-/

namespace Crush.Metatheory.Datatype

/-- A carrier isomorphism used without depending on a larger algebra library. -/
structure Iso (source target : Type) where
  to : source → target
  «from» : target → source
  left_inv : ∀ value, «from» (to value) = value
  right_inv : ∀ value, to («from» value) = value

/-- Convert a source field value to its canonical constructor payload. -/
def FieldDecl.toVal {arity : Nat} {block : Block arity}
    {Base : BaseSort → Type}
    (carrier : ∀ data : DataRef block,
      Iso (Base data.decl.sort) (Val block Base data))
    (field : FieldDecl arity) :
    (field.ty block).Denote Base → field.Denote block Base :=
  match field with
  | ⟨_, .base _⟩ => id
  | ⟨_, .data child⟩ => (carrier child).to

/-- Convert a canonical constructor payload back to its source carrier. -/
def FieldDecl.fromVal {arity : Nat} {block : Block arity}
    {Base : BaseSort → Type}
    (carrier : ∀ data : DataRef block,
      Iso (Base data.decl.sort) (Val block Base data))
    (field : FieldDecl arity) :
    field.Denote block Base → (field.ty block).Denote Base :=
  match field with
  | ⟨_, .base _⟩ => id
  | ⟨_, .data child⟩ => (carrier child).«from»

@[simp] theorem FieldDecl.fromVal_toVal {arity : Nat} {block : Block arity}
    {Base : BaseSort → Type}
    (carrier : ∀ data : DataRef block,
      Iso (Base data.decl.sort) (Val block Base data))
    (field : FieldDecl arity) (value : (field.ty block).Denote Base) :
    field.fromVal carrier (field.toVal carrier value) = value := by
  cases field with
  | mk name sort =>
      cases sort with
      | base => rfl
      | data child => exact (carrier child).left_inv value

@[simp] theorem FieldDecl.toVal_fromVal {arity : Nat} {block : Block arity}
    {Base : BaseSort → Type}
    (carrier : ∀ data : DataRef block,
      Iso (Base data.decl.sort) (Val block Base data))
    (field : FieldDecl arity) (value : field.Denote block Base) :
    field.toVal carrier (field.fromVal carrier value) = value := by
  cases field with
  | mk name sort =>
      cases sort with
      | base => rfl
      | data child => exact (carrier child).right_inv value

/-- Curry a constructor argument telescope into its reified source type. -/
def Args.curry {arity : Nat} {block : Block arity}
    {Base : BaseSort → Type}
    (carrier : ∀ data : DataRef block,
      Iso (Base data.decl.sort) (Val block Base data)) :
    (fields : List (FieldDecl arity)) → (result : Ty) →
    (Args block Base fields → result.Denote Base) →
      (fields.foldr (fun field rest => .arrow (field.ty block) rest) result).Denote Base
  | [], _, build => build .nil
  | { name, sort := .base sort } :: rest, result, build =>
      fun value => Args.curry carrier rest result fun tail =>
        build (.base value tail)
  | { name, sort := FieldSort.data child } :: rest, result, build =>
      fun value => Args.curry carrier rest result fun tail =>
        build (.data ((carrier child).to value) tail)

/-- Canonical curried interpretation of one constructor constant. -/
def CtorDecl.denote {arity : Nat} {block : Block arity}
    {Base : BaseSort → Type}
    (carrier : ∀ data : DataRef block,
      Iso (Base data.decl.sort) (Val block Base data))
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) :
    (ctor.ty block data).Denote Base :=
  Args.curry carrier ctor.fields (.base data.decl.sort) fun args =>
    (carrier data).«from» (.ctor ref args)

/-- Higher-order constants for one datatype block. -/
structure Symbols (signature : Signature) {arity : Nat} (block : Block arity) where
  ctor : {data : DataRef block} → {decl : CtorDecl arity} →
    CtorRef block data decl → Const signature (decl.ty block data)
  sel : {data : DataRef block} → {ctor : CtorDecl arity} →
    CtorRef block data ctor → {field : FieldDecl arity} →
    FieldRef ctor field →
      Const signature (.arrow (.base data.decl.sort) (field.ty block))
  test : {data : DataRef block} → {ctor : CtorDecl arity} →
    CtorRef block data ctor →
      Const signature (.arrow (.base data.decl.sort) .bool)

/-- Every mutual block has one canonical symbol map into its compact source
signature. Terms continue to use ordinary constants. -/
def Block.symbols {arity : Nat} (block : Block arity) :
    Symbols block.symbolTypes block where
  ctor := block.ctorConst
  sel := block.selConst
  test := block.testConst

namespace Symbols

/-- Keep one symbol map while extending the signature on the right. -/
def inLeft {signature : Signature} {arity : Nat} {block : Block arity}
    (symbols : Symbols signature block) (tail : Signature) :
    Symbols (signature ++ tail) block where
  ctor := fun ref => (symbols.ctor ref).inLeft tail
  sel := fun {_data} {_ctor} ctorRef {_field} fieldRef =>
    (symbols.sel ctorRef fieldRef).inLeft tail
  test := fun ref => (symbols.test ref).inLeft tail

/-- Keep one symbol map while extending the signature on the left. -/
def inRight {signature : Signature} {arity : Nat} {block : Block arity}
    (symbols : Symbols signature block) (head : Signature) :
    Symbols (head ++ signature) block where
  ctor := fun ref => (symbols.ctor ref).inRight head
  sel := fun {_data} {_ctor} ctorRef {_field} fieldRef =>
    (symbols.sel ctorRef fieldRef).inRight head
  test := fun ref => (symbols.test ref).inRight head

end Symbols

/-- A source model interprets the selected base sorts as canonical finite
datatype values and gives every datatype symbol its free-datatype meaning. Selectors are
constrained only on their own constructor. -/
structure IsFreeDatatypeModel {signature : Signature} {arity : Nat} {block : Block arity}
    (symbols : Symbols signature block) (model : Model signature) where
  carrier : ∀ data : DataRef block,
    Iso (model.Base data.decl.sort) (Val block model.Base data)
  ctor_denote : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor),
    model.const (symbols.ctor ref) = ctor.denote carrier ref
  sel_ctor : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    {field : FieldDecl arity} (fieldRef : FieldRef ctor field)
    (args : Args block model.Base ctor.fields),
    model.const (symbols.sel ctorRef fieldRef)
        ((carrier data).«from» (.ctor ctorRef args)) =
      field.fromVal carrier (args.get fieldRef)
  test_denote : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) (value : model.Base data.decl.sort),
    model.const (symbols.test ref) value ↔ IsCtor ref ((carrier data).to value)

/-- A datatype carrier satisfying the free-datatype model condition is necessarily
productive: the source model
supplies an inhabitant and the carrier isomorphism turns it into a finite
constructor tree. -/
theorem IsFreeDatatypeModel.productive {signature : Signature} {arity : Nat}
    {block : Block arity} {symbols : Symbols signature block}
    {model : Model signature} (law : IsFreeDatatypeModel symbols model) :
    Productive block := by
  intro data
  let ⟨value⟩ := model.baseNonempty data.decl.sort
  exact ⟨((law.carrier data).to value).map fun _ _ => ()⟩

/-! ## Multiple monomorphic datatype blocks -/

/-- One datatype block and its higher-order constants in a shared signature. -/
structure Entry (signature : Signature) where
  arity : Nat
  block : Block arity
  symbols : Symbols signature block

/-- Ordered datatype blocks used by one certified sentence. -/
abbrev Env (signature : Signature) := List (Entry signature)

namespace Env

/-- Weaken every datatype entry while extending the source signature on the
right. -/
def inLeft {signature : Signature} (env : Env signature)
    (tail : Signature) : Env (signature ++ tail) :=
  env.map fun entry => {
    arity := entry.arity
    block := entry.block
    symbols := entry.symbols.inLeft tail }

/-- Weaken every datatype entry after a newly prepended source signature. -/
def inRight {signature : Signature} (env : Env signature)
    (head : Signature) : Env (head ++ signature) :=
  env.map fun entry => {
    arity := entry.arity
    block := entry.block
    symbols := entry.symbols.inRight head }

@[simp] theorem inLeft_length {signature : Signature} (env : Env signature)
    (tail : Signature) : (env.inLeft tail).length = env.length := by
  unfold inLeft
  simp

@[simp] theorem inRight_length {signature : Signature} (env : Env signature)
    (head : Signature) : (env.inRight head).length = env.length := by
  unfold inRight
  simp

/-- A shared source model satisfies the free-datatype condition for every block. -/
inductive IsFreeDatatypeModel {signature : Signature} (model : Model signature) :
    Env signature → Type where
  | nil : IsFreeDatatypeModel model []
  | cons {entry : Entry signature} {rest : Env signature} :
      Datatype.IsFreeDatatypeModel entry.symbols model → IsFreeDatatypeModel model rest →
        IsFreeDatatypeModel model (entry :: rest)

/-- Semantic unsatisfiability in every model satisfying the complete datatype
environment. -/
abbrev Unsatisfiable {signature : Signature} (env : Env signature)
    (formula : Sentence signature) : Prop :=
  UnsatisfiableUnder (fun model => IsFreeDatatypeModel model env) formula

/-- Semantic unsatisfiability of a complete source theory in every model satisfying
for the datatype environment. -/
abbrev TheoryUnsatisfiable {signature : Signature} (env : Env signature)
    (theory : Theory signature) : Prop :=
  ∀ model : Model signature, ∀ _freeDataModel : IsFreeDatatypeModel model env,
    ¬model.SatisfiesTheory theory

end Env

/-- With no native datatype components, environment-aware unsatisfiability is
the ordinary source proposition. -/
theorem Env.unsatisfiable_nil_iff {signature : Signature}
    (formula : Sentence signature) :
    Env.Unsatisfiable [] formula ↔ Crush.Metatheory.Unsatisfiable formula := by
  constructor
  · intro unsat model valid
    exact unsat model .nil valid
  · intro unsat model freeDataModel valid
    exact unsat model valid

end Crush.Metatheory.Datatype
