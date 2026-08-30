import Crush.Metatheory.Datatype.Model
import Crush.Metatheory.Datatype.Flattened
import Crush.Metatheory.SMT.DatatypeWF
import Crush.Metatheory.SMT.Representation

/-!
# Datatypes in the shared SMT representation

A datatype is an ordinary intrinsic base sort with ordinary typed FO symbols.
This certificate records only what is special at the SMT declaration boundary:
the sort and symbols are supplied by one native `declare-datatypes` command,
and testers use SMT-LIB's indexed identifier. Term encoding and raw-model
lifting remain the generic definitions in `SMT.Representation` and
`SMT.Soundness`.
-/

namespace Crush.Metatheory.SMT.Datatype

open Crush.Metatheory.Datatype
open Crush.Metatheory.Defunctionalization.Flattened

/-- One intrinsic datatype block represented inside the shared FO-to-SMT
encoding. No parallel term encoder or ownership record is needed. -/
structure Representation {signature : Signature} {arity : Nat}
    (block : Block arity) (symbols : Symbols signature block)
    (fo : SMT.Encoding (Symbol signature))
    (data : BlockEncoding arity) where
  wf : CommandWF block data
  /-- One flattened symbol cannot simultaneously play two native datatype
  roles. Reification establishes this from distinct source-constant ownership;
  retaining it here makes native model selection deterministic. -/
  exclusive : symbols.native.Exclusive
  sort_native : ∀ child : DataRef block,
    fo.nativeSort (.base child.decl.sort) = true
  sort_eq : ∀ child : DataRef block,
    fo.sort (.base child.decl.sort) = dataSort data child
  base_eq : ∀ sort : BaseSort,
    data.baseSort sort = fo.sort (.base sort)
  ctor_native : ∀ {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor),
    fo.nativeSymbol (.sourceConstant (symbols.ctor ref)) = true
  ctor_ident : ∀ {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor),
    fo.ident (.sourceConstant (symbols.ctor ref)) =
      .symb (data.name (.ctor child ref.index))
  sel_native : ∀ {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field),
    fo.nativeSymbol (.sourceConstant (symbols.sel ctorRef fieldRef)) = true
  sel_ident : ∀ {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field),
    fo.ident (.sourceConstant (symbols.sel ctorRef fieldRef)) =
      .symb (data.name (.sel child ctorRef.index fieldRef.index))
  test_native : ∀ {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor),
    fo.nativeSymbol (.sourceConstant (symbols.test ref)) = true
  test_ident : ∀ {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor),
    fo.ident (.sourceConstant (symbols.test ref)) =
      .indexed "is" #[.inl (data.name (.ctor child ref.index))]

namespace Representation

variable {signature : Signature} {arity : Nat}
variable {block : Block arity} {symbols : Symbols signature block}
variable {fo : SMT.Encoding (Symbol signature)}
variable {data : BlockEncoding arity}

@[simp] theorem SMT.Encoding.ident_cast
    {family : FO.SymbolFamily} (encoding : SMT.Encoding family)
    {actual expected : FO.SymbolDecl}
    (equal : actual = expected) (symbol : family actual) :
    encoding.ident (castSymbol equal symbol) = encoding.ident symbol := by
  cases equal
  rfl

/-- Constructor ownership at the flattened declaration has the same encoded
identifier as the underlying source constant. -/
theorem native_ctor_ident
    (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    fo.ident (symbols.native.ctor ref) =
      .symb (data.name (.ctor child ref.index)) := by
  let equal : Defunctionalization.sourceDecl (ctor.ty block child) =
      ctor.fo block child := by
    simpa [CtorDecl.fo, CtorDecl.ty] using
      sourceDecl_ctor (block := block) ctor.fields child.decl.sort
  have casted : symbols.native.ctor ref =
      castSymbol equal (.sourceConstant (symbols.ctor ref)) := by
    simp only [Symbols.native]
  calc
    fo.ident (symbols.native.ctor ref) =
        fo.ident (castSymbol equal (.sourceConstant (symbols.ctor ref))) :=
      congrArg fo.ident casted
    _ = fo.ident (.sourceConstant (symbols.ctor ref)) :=
      SMT.Encoding.ident_cast fo equal _
    _ = _ := represented.ctor_ident ref

/-- Selector ownership uses the same encoded identifier as its source
constant. -/
theorem native_sel_ident
    (represented : Representation block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    fo.ident (symbols.native.sel ctorRef fieldRef) =
      .symb (data.name (.sel child ctorRef.index fieldRef.index)) := by
  cases field with
  | mk name sort => cases sort <;>
      exact represented.sel_ident ctorRef fieldRef

@[simp] theorem sort_omitted
    (represented : Representation block symbols fo data)
    (declarations : List
      (SMT.Declaration (Symbol signature)))
    (source : FO.FamilyTheory (Symbol signature)) (child : DataRef block) :
    .base child.decl.sort ∉
      SMT.ordinarySorts fo declarations source :=
  SMT.native_sort_omitted _ _ _ _
    (represented.sort_native child)

@[simp] theorem ctor_omitted
    (represented : Representation block symbols fo data)
    (declarations : List
      (SMT.Declaration (Symbol signature)))
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    (⟨_, .sourceConstant (symbols.ctor ref)⟩ :
      SMT.Declaration (Symbol signature)) ∉
      SMT.ordinaryDecls fo declarations :=
  SMT.native_decl_omitted _ _ _
    (represented.ctor_native ref)

@[simp] theorem sel_omitted
    (represented : Representation block symbols fo data)
    (declarations : List
      (SMT.Declaration (Symbol signature)))
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    (⟨_, .sourceConstant (symbols.sel ctorRef fieldRef)⟩ :
      SMT.Declaration (Symbol signature)) ∉
      SMT.ordinaryDecls fo declarations :=
  SMT.native_decl_omitted _ _ _
    (represented.sel_native ctorRef fieldRef)

@[simp] theorem test_omitted
    (represented : Representation block symbols fo data)
    (declarations : List
      (SMT.Declaration (Symbol signature)))
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    (⟨_, .sourceConstant (symbols.test ref)⟩ :
      SMT.Declaration (Symbol signature)) ∉
      SMT.ordinaryDecls fo declarations :=
  SMT.native_decl_omitted _ _ _
    (represented.test_native ref)

end Representation

/-- Dependency-ordered datatype blocks represented by one shared encoding.
The encoding itself owns the exact native command array, so this witness does
not duplicate a second command trace. -/
inductive Represented {signature : Signature}
    (fo : SMT.Encoding (Symbol signature)) :
    Env signature → Type 1 where
  | nil : Represented fo []
  | cons {entry : Entry signature} {rest : Env signature}
      {data : BlockEncoding entry.arity}
      (head : Representation entry.block entry.symbols fo data)
      (tail : Represented fo rest) : Represented fo (entry :: rest)

namespace Represented

/-- Every represented native block supplies the structural well-formedness
needed by guarded dependency composition. -/
def blocksWF {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)} :
    {env : Env signature} → Represented fo env → Env.BlocksWF env
  | [], .nil => .nil
  | _ :: _, .cons head tail => .cons head.wf.blockWF tail.blocksWF

/-- Exact dependency-ordered native command sequence described by an
environment representation. -/
def commands {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)} :
    {env : Env signature} → Represented fo env → Array Crush.SMT.Command
  | [], .nil => #[]
  | _ :: _, .cons (entry := entry) (data := data) head tail =>
      #[command entry.block data] ++ commands tail

end Represented

/-- Exact representation of every datatype block owned by a shared encoding.
The command equation is the single source of truth for native command order;
individual block certificates do not retain redundant membership proofs. -/
structure EnvRepresentation {signature : Signature}
    (fo : SMT.Encoding (Symbol signature))
    (env : Env signature) where
  blocks : Represented fo env
  native_eq : fo.nativeCommands = blocks.commands

/-- The empty datatype environment is the ordinary encoding case. -/
def EnvRepresentation.nil {signature : Signature}
    (fo : SMT.Encoding (Symbol signature)) (native_eq : fo.nativeCommands = #[]) :
    EnvRepresentation fo [] :=
  ⟨.nil, native_eq⟩

/-- Assemble the guarded flattened target carried by all represented blocks.
The ordinary canonical model remains the fixed source of the resulting single
model relation. -/
noncomputable def EnvRepresentation.lifted {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)} {env : Env signature}
    (represented : EnvRepresentation fo env) (source : Model signature)
    (lawful : Env.Lawful source env) :
    Lifted (canonicalModel source) :=
  Env.lift source env lawful represented.blocks.blocksWF

/-- Assemble represented datatype blocks over a caller-supplied interpreted or
otherwise guarded base model. -/
noncomputable def EnvRepresentation.liftedFrom {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)} {env : Env signature}
    (represented : EnvRepresentation fo env) (source : Model signature)
    (lawful : Env.Lawful source env)
    (prior : Lifted (canonicalModel source)) :
    Lifted (canonicalModel source) :=
  Env.liftFrom source env lawful represented.blocks.blocksWF prior

end Crush.Metatheory.SMT.Datatype
