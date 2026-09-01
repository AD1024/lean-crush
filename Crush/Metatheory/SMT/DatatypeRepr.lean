import Crush.Metatheory.Datatype.Model
import Crush.Metatheory.Datatype.Flattened
import Crush.Metatheory.SMT.DatatypeWF
import Crush.Metatheory.SMT.Repr

/-!
# SMT datatype representation evidence

A datatype is an ordinary typed base sort with ordinary typed FO symbols.
This certificate records only what is special at the SMT declaration boundary:
the sort and symbols are supplied by one `declare-datatypes` command,
and testers use SMT-LIB's indexed identifier. Term encoding and raw-model
lifting remain the generic definitions in `SMT.Repr` and
`SMT.Soundness`.
-/

namespace Crush.Metatheory.SMT.Datatype

open Crush.Metatheory.Datatype
open Crush.Metatheory.Defunctionalization.Flattened

/-- One reified datatype block represented inside the shared FO-to-SMT
encoding. No parallel term encoder or block-membership record is needed. -/
structure Repr {signature : Signature} {arity : Nat}
    (block : Block arity) (symbols : Symbols signature block)
    (fo : SMT.Encoding (Symbol signature))
    (data : BlockEncoding arity) where
  wf : CommandWF block data
  /-- One flattened symbol cannot simultaneously play two datatype
  roles. Reification establishes this from distinct source-constant positions;
  retaining it here makes datatype-model selection deterministic. -/
  rolesUnique : symbols.datatypeSymbols.RolesUnique
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

namespace Repr

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

/-- A constructor's flattened declaration has the same encoded
identifier as the underlying source constant. -/
theorem flattenedCtor_ident
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    fo.ident (symbols.datatypeSymbols.ctor ref) =
      .symb (data.name (.ctor child ref.index)) := by
  let equal : Defunctionalization.sourceDecl (ctor.ty block child) =
      ctor.fo block child := by
    simpa [CtorDecl.fo, CtorDecl.ty] using
      sourceDecl_ctor (block := block) ctor.fields child.decl.sort
  have casted : symbols.datatypeSymbols.ctor ref =
      castSymbol equal (.sourceConstant (symbols.ctor ref)) := by
    simp only [Symbols.datatypeSymbols]
  calc
    fo.ident (symbols.datatypeSymbols.ctor ref) =
        fo.ident (castSymbol equal (.sourceConstant (symbols.ctor ref))) :=
      congrArg fo.ident casted
    _ = fo.ident (.sourceConstant (symbols.ctor ref)) :=
      SMT.Encoding.ident_cast fo equal _
    _ = _ := represented.ctor_ident ref

/-- A selector uses the same encoded identifier as its source
constant. -/
theorem flattenedSelector_ident
    (represented : Repr block symbols fo data)
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    fo.ident (symbols.datatypeSymbols.sel ctorRef fieldRef) =
      .symb (data.name (.sel child ctorRef.index fieldRef.index)) := by
  cases field with
  | mk name sort => cases sort <;>
      exact represented.sel_ident ctorRef fieldRef

@[simp] theorem sort_omitted
    (represented : Repr block symbols fo data)
    (declarations : List
      (SMT.Decl (Symbol signature)))
    (source : FO.FamilyTheory (Symbol signature)) (child : DataRef block) :
    .base child.decl.sort ∉
      SMT.ordinarySorts fo declarations source :=
  SMT.native_sort_omitted _ _ _ _
    (represented.sort_native child)

@[simp] theorem ctor_omitted
    (represented : Repr block symbols fo data)
    (declarations : List
      (SMT.Decl (Symbol signature)))
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    (⟨_, .sourceConstant (symbols.ctor ref)⟩ :
      SMT.Decl (Symbol signature)) ∉
      SMT.ordinaryDecls fo declarations :=
  SMT.native_decl_omitted _ _ _
    (represented.ctor_native ref)

@[simp] theorem sel_omitted
    (represented : Repr block symbols fo data)
    (declarations : List
      (SMT.Decl (Symbol signature)))
    {child : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block child ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    (⟨_, .sourceConstant (symbols.sel ctorRef fieldRef)⟩ :
      SMT.Decl (Symbol signature)) ∉
      SMT.ordinaryDecls fo declarations :=
  SMT.native_decl_omitted _ _ _
    (represented.sel_native ctorRef fieldRef)

@[simp] theorem test_omitted
    (represented : Repr block symbols fo data)
    (declarations : List
      (SMT.Decl (Symbol signature)))
    {child : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block child ctor) :
    (⟨_, .sourceConstant (symbols.test ref)⟩ :
      SMT.Decl (Symbol signature)) ∉
      SMT.ordinaryDecls fo declarations :=
  SMT.native_decl_omitted _ _ _
    (represented.test_native ref)

end Repr

/-- Dependency-ordered datatype blocks represented by one shared encoding.
The encoding itself contains the exact SMT datatype command sequence, so this witness does
not duplicate that command list. -/
inductive Represented {signature : Signature}
    (fo : SMT.Encoding (Symbol signature)) :
    Env signature → Type 1 where
  | nil : Represented fo []
  | cons {entry : Entry signature} {rest : Env signature}
      {data : BlockEncoding entry.arity}
      (head : Repr entry.block entry.symbols fo data)
      (tail : Represented fo rest) : Represented fo (entry :: rest)

namespace Represented

/-- Every represented SMT datatype block supplies the structural well-formedness
needed by guarded dependency composition. -/
def blocksWF {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)} :
    {env : Env signature} → Represented fo env → Env.BlocksWF env
  | [], .nil => .nil
  | _ :: _, .cons head tail => .cons head.wf.blockWF tail.blocksWF

/-- Exact dependency-ordered SMT datatype command sequence described by an
environment representation. -/
def commands {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)} :
    {env : Env signature} → Represented fo env → Array Crush.SMT.Command
  | [], .nil => #[]
  | _ :: _, .cons (entry := entry) (data := data) head tail =>
      #[command entry.block data] ++ commands tail

end Represented

/-- Exact representation of every datatype block under a shared encoding.
The command equation is the single source of truth for SMT datatype command order;
individual block certificates do not retain redundant membership proofs. -/
structure EnvRepr {signature : Signature}
    (fo : SMT.Encoding (Symbol signature))
    (env : Env signature) where
  blocks : Represented fo env
  datatypeCommands_eq : fo.nativeCommands = blocks.commands

/-- The empty datatype environment is the ordinary encoding case. -/
def EnvRepr.nil {signature : Signature}
    (fo : SMT.Encoding (Symbol signature)) (datatypeCommands_eq : fo.nativeCommands = #[]) :
    EnvRepr fo [] :=
  ⟨.nil, datatypeCommands_eq⟩

/-- Assemble the guarded flattened target carried by all represented blocks.
The ordinary canonical model remains the fixed source of the resulting single
model relation. -/
noncomputable def EnvRepr.lifted {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)} {env : Env signature}
    (represented : EnvRepr fo env) (source : Model signature)
    (freeDataModel : Env.IsFreeDatatypeModel source env) :
    Lifted (canonicalModel source) :=
  Env.lift source env freeDataModel represented.blocks.blocksWF

/-- Assemble represented datatype blocks over a caller-supplied interpreted or
otherwise guarded base model. -/
noncomputable def EnvRepr.liftedFrom {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)} {env : Env signature}
    (represented : EnvRepr fo env) (source : Model signature)
    (freeDataModel : Env.IsFreeDatatypeModel source env)
    (prior : Lifted (canonicalModel source)) :
    Lifted (canonicalModel source) :=
  Env.liftFrom source env freeDataModel represented.blocks.blocksWF prior

/-- Installing an empty datatype environment leaves an existing carrier
representation unchanged. -/
@[simp] theorem EnvRepr.liftedFrom_nil {signature : Signature}
    {fo : SMT.Encoding (Symbol signature)}
    (represented : EnvRepr fo []) (source : Model signature)
    (freeDataModel : Env.IsFreeDatatypeModel source [])
    (prior : Lifted (canonicalModel source)) :
    represented.liftedFrom source freeDataModel prior = prior := by
  cases represented with
  | mk blocks commandsEq =>
      cases blocks
      cases freeDataModel
      rfl

end Crush.Metatheory.SMT.Datatype
