import Crush.Metatheory.Datatype.Carrier

/-!
# Datatype components in one FO family model

One typed symbol map identifies the constructor, selector, and tester
symbols belonging to a datatype block. The target model gives those symbols
their full free-algebra meanings and lifts every other symbol generically.
-/

namespace Crush.Metatheory.Datatype

open Crush.Metatheory.Guarded

universe u

/-- Datatype symbols inside an otherwise generic FO symbol family. -/
structure DatatypeSymbols (symbols : FO.SymbolFamily.{u}) {arity : Nat}
    (block : Block arity) where
  ctor : {data : DataRef block} → {decl : CtorDecl arity} →
    CtorRef block data decl → symbols (decl.fo block data)
  sel : {data : DataRef block} → {ctor : CtorDecl arity} →
    CtorRef block data ctor → {field : FieldDecl arity} →
    FieldRef ctor field → symbols (field.sel block data)
  test : {data : DataRef block} → {ctor : CtorDecl arity} →
    CtorRef block data ctor → symbols (ctor.test block data)

/-- A typed reference showing that a family symbol belongs to this datatype block. -/
inductive DatatypeSymbolRef {symbols : FO.SymbolFamily.{u}} {arity : Nat}
    {block : Block arity} (datatypeSymbols : DatatypeSymbols symbols block) :
    {decl : FO.SymbolDecl} → symbols decl → Type u where
  | ctor {data : DataRef block} {decl : CtorDecl arity}
      (ref : CtorRef block data decl) : DatatypeSymbolRef datatypeSymbols (datatypeSymbols.ctor ref)
  | sel {data : DataRef block} {ctor : CtorDecl arity}
      (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
      (fieldRef : FieldRef ctor field) :
      DatatypeSymbolRef datatypeSymbols (datatypeSymbols.sel ctorRef fieldRef)
  | test {data : DataRef block} {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor) : DatatypeSymbolRef datatypeSymbols (datatypeSymbols.test ref)

/-- No family symbol has two datatype roles in the same block. -/
def DatatypeSymbols.RolesUnique {symbols : FO.SymbolFamily.{u}} {arity : Nat}
    {block : Block arity} (datatypeSymbols : DatatypeSymbols symbols block) : Prop :=
  ∀ {decl : FO.SymbolDecl} (symbol : symbols decl),
    Subsingleton (DatatypeSymbolRef datatypeSymbols symbol)

/-- Source-model laws for one typed datatype symbol map. Selectors retain
their intentionally unspecified behavior away from their own constructor. -/
structure IsFreeDatatypeFamilyModel {symbols : FO.SymbolFamily.{u}} {arity : Nat}
    {block : Block arity} (datatypeSymbols : DatatypeSymbols symbols block)
    (source : FO.FamilyModel symbols) where
  carrier : ∀ data : DataRef block,
    Iso (source.carriers.Base data.decl.sort)
      (Val block source.carriers.Base data)
  ctor_denote : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor),
    source.symbol (datatypeSymbols.ctor ref) =
      BaseLift.sourceCtor source.carriers carrier ref
  sel_ctor : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    {field : FieldDecl arity} (fieldRef : FieldRef ctor field)
    (args : Args block source.carriers.Base ctor.fields),
    source.symbol (datatypeSymbols.sel ctorRef fieldRef)
        ((carrier data).«from» (.ctor ctorRef args)) =
      BaseLift.sourceField carrier field (args.get fieldRef)
  test_denote : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor)
    (value : source.carriers.Base data.decl.sort),
    source.symbol (datatypeSymbols.test ref) value ↔
      IsCtor ref ((carrier data).to value)

namespace DatatypeSymbolRef

/-- Full target denotation selected by one datatype symbol reference. -/
noncomputable def denote {symbols : FO.SymbolFamily.{u}} {arity : Nat}
    {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers) :
    {decl : FO.SymbolDecl} → {symbol : symbols decl} →
      DatatypeSymbolRef datatypeSymbols symbol →
      FO.SymbolDenote (BaseLift.carriers productive prior.carriers)
        decl.args decl.result
  | _, _, .ctor ref =>
      BaseLift.targetCtor wf productive prior.carriers ref
  | _, _, .sel ctorRef fieldRef =>
      BaseLift.targetSel wf productive priorRel law.carrier ctorRef fieldRef
        (source.symbol (datatypeSymbols.sel ctorRef fieldRef))
  | _, _, .test ref =>
      BaseLift.targetTest wf productive prior.carriers ref

end DatatypeSymbolRef

/-! ## Dependency-ordered extension -/

/-- Extend a previously related target model by one later datatype block.
Symbols whose complete declaration is external to the new block are transported
from the prior model; symbols mentioning a sort declared by the new block are lifted
afresh. This preserves datatype interpretations installed by earlier dependency
blocks without adding a parallel block-symbol registry. -/
noncomputable def IsFreeDatatypeFamilyModel.extend {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel) :
    FO.FamilyModel symbols := by
  classical
  exact {
    carriers := BaseLift.carriers productive prior.carriers
    symbol := fun {decl} symbol =>
      if symbolRef : Nonempty (DatatypeSymbolRef datatypeSymbols symbol) then
        (Classical.choice symbolRef).denote law wf productive prior priorRel
      else if external : BaseLift.ExternalDecl block decl then
        BaseLift.transportSymbol productive external.1 external.2 (prior.symbol symbol)
      else
        FO.liftSymbol
          (BaseLift.carrierRel wf productive priorRel law.carrier)
          (source.symbol symbol) }

theorem IsFreeDatatypeFamilyModel.extend_symbol_datatype {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {decl : FO.SymbolDecl} (symbol : symbols decl)
    (symbolRef : Nonempty (DatatypeSymbolRef datatypeSymbols symbol)) :
    (law.extend wf productive prior priorRel priorModels).symbol symbol =
      (Classical.choice symbolRef).denote law wf productive prior priorRel := by
  classical
  simp [IsFreeDatatypeFamilyModel.extend, symbolRef]

theorem IsFreeDatatypeFamilyModel.extend_symbol_external {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {decl : FO.SymbolDecl} (symbol : symbols decl)
    (notInBlock : ¬Nonempty (DatatypeSymbolRef datatypeSymbols symbol))
    (external : BaseLift.ExternalDecl block decl) :
    (law.extend wf productive prior priorRel priorModels).symbol symbol =
      BaseLift.transportSymbol productive external.1 external.2
        (prior.symbol symbol) := by
  classical
  simp [IsFreeDatatypeFamilyModel.extend, notInBlock, external]

theorem IsFreeDatatypeFamilyModel.extend_symbol_fresh {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {decl : FO.SymbolDecl} (symbol : symbols decl)
    (notInBlock : ¬Nonempty (DatatypeSymbolRef datatypeSymbols symbol))
    (fresh : ¬BaseLift.ExternalDecl block decl) :
    (law.extend wf productive prior priorRel priorModels).symbol symbol =
      FO.liftSymbol
        (BaseLift.carrierRel wf productive priorRel law.carrier)
        (source.symbol symbol) := by
  classical
  simp [IsFreeDatatypeFamilyModel.extend, notInBlock, fresh]

/-- One dependency step preserves every source symbol. Earlier external
interpretations use `transportSymbol_rel`; current or forward-looking symbols use the
ordinary canonical lift. -/
theorem IsFreeDatatypeFamilyModel.extend_rel {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel) :
    FO.ModelRel source
      (law.extend wf productive prior priorRel priorModels)
      (BaseLift.carrierRel wf productive priorRel law.carrier) where
  symbol := by
    intro decl symbol
    classical
    by_cases symbolRef : Nonempty (DatatypeSymbolRef datatypeSymbols symbol)
    · rw [law.extend_symbol_datatype wf productive prior priorRel priorModels
          symbol symbolRef]
      let ref := Classical.choice symbolRef
      change FO.SymbolRel _ (source.symbol symbol)
        (ref.denote law wf productive prior priorRel)
      cases ref with
      | @ctor data ctor ctorRef =>
          rw [law.ctor_denote ctorRef]
          exact BaseLift.ctor_rel wf productive source.carriers
            prior.carriers priorRel law.carrier ctorRef
      | @sel data ctor ctorRef field fieldRef =>
          exact BaseLift.sel_rel wf productive source.carriers
            prior.carriers priorRel law.carrier ctorRef fieldRef _
      | @test data ctor ctorRef =>
          exact BaseLift.test_rel wf productive source.carriers
            prior.carriers priorRel law.carrier ctorRef _
              (law.test_denote ctorRef)
    · by_cases external : BaseLift.ExternalDecl block decl
      · rw [law.extend_symbol_external wf productive prior priorRel
            priorModels symbol symbolRef external]
        exact BaseLift.transportSymbol_rel wf productive priorRel law.carrier
          external.1 external.2 (source.symbol symbol) (prior.symbol symbol)
          (priorModels.symbol symbol)
      · rw [law.extend_symbol_fresh wf productive prior priorRel priorModels
            symbol symbolRef external]
        exact FO.liftSymbol_rel
          (BaseLift.carrierRel wf productive priorRel law.carrier)
          (source.symbol symbol)

/-- `RolesUnique` ensures that a symbol reference selects exactly one datatype
operation in the current dependency extension. -/
theorem IsFreeDatatypeFamilyModel.extend_datatypeSymbol {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (rolesUnique : datatypeSymbols.RolesUnique) (wf : block.WF)
    (productive : Productive block) (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {decl : FO.SymbolDecl} {symbol : symbols decl}
    (ref : DatatypeSymbolRef datatypeSymbols symbol) :
    (law.extend wf productive prior priorRel priorModels).symbol symbol =
      ref.denote law wf productive prior priorRel := by
  rw [law.extend_symbol_datatype wf productive prior priorRel priorModels
    symbol ⟨ref⟩]
  have chosen : Classical.choice
      (show Nonempty (DatatypeSymbolRef datatypeSymbols symbol) from ⟨ref⟩) = ref :=
    rolesUnique _ |>.elim _ _
  rw [chosen]

theorem IsFreeDatatypeFamilyModel.extend_ctor {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (rolesUnique : datatypeSymbols.RolesUnique) (wf : block.WF)
    (productive : Productive block) (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) :
    (law.extend wf productive prior priorRel priorModels).symbol
        (datatypeSymbols.ctor ref) =
      BaseLift.targetCtor wf productive prior.carriers ref := by
  simpa [DatatypeSymbolRef.denote, CtorDecl.fo] using
    law.extend_datatypeSymbol rolesUnique wf productive prior priorRel priorModels
      (DatatypeSymbolRef.ctor ref)

theorem IsFreeDatatypeFamilyModel.extend_sel {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (rolesUnique : datatypeSymbols.RolesUnique) (wf : block.WF)
    (productive : Productive block) (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    (law.extend wf productive prior priorRel priorModels).symbol
        (datatypeSymbols.sel ctorRef fieldRef) =
      BaseLift.targetSel wf productive priorRel law.carrier ctorRef fieldRef
        (source.symbol (datatypeSymbols.sel ctorRef fieldRef)) := by
  simpa [DatatypeSymbolRef.denote, FieldDecl.sel] using
    law.extend_datatypeSymbol rolesUnique wf productive prior priorRel priorModels
      (DatatypeSymbolRef.sel ctorRef fieldRef)

theorem IsFreeDatatypeFamilyModel.extend_test {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : IsFreeDatatypeFamilyModel datatypeSymbols source)
    (rolesUnique : datatypeSymbols.RolesUnique) (wf : block.WF)
    (productive : Productive block) (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) :
    (law.extend wf productive prior priorRel priorModels).symbol
        (datatypeSymbols.test ref) =
      BaseLift.targetTest wf productive prior.carriers ref := by
  simpa [DatatypeSymbolRef.denote, CtorDecl.test] using
    law.extend_datatypeSymbol rolesUnique wf productive prior priorRel priorModels
      (DatatypeSymbolRef.test ref)

/-- A target model together with its complete relation to the fixed source
model. Packaging the dependent relation avoids parallel carrier/model arrays
while folding dependency blocks. -/
structure Lifted {symbols : FO.SymbolFamily.{u}}
    (source : FO.FamilyModel symbols) where
  target : FO.FamilyModel symbols
  relation : FO.CarrierRel source.carriers target.carriers
  models : FO.ModelRel source target relation

namespace Lifted

/-- Empty dependency prefix. -/
def refl {symbols : FO.SymbolFamily.{u}} (source : FO.FamilyModel symbols) :
    Lifted source where
  target := source
  relation := FO.CarrierRel.refl source.carriers
  models := FO.ModelRel.refl source

/-- Every value belongs to the image of the identity carrier
representation. -/
theorem refl_guard {symbols : FO.SymbolFamily.{u}}
    (source : FO.FamilyModel symbols) (sort : FO.FOSort)
    (value : sort.Denote source.carriers) :
    ((refl source).relation sort).guard value := by
  cases sort <;> trivial

/-- Canonically enlarge only the opaque base carriers of a family model. The
defunctionalized function-value carriers stay unchanged; every source symbol is
totalized through the supplied guarded base relations. This is the initial
model used, for example, when `Nat` is represented by guarded `Int`. -/
noncomputable def ofBase {symbols : FO.SymbolFamily.{u}}
    (source : FO.FamilyModel symbols) {Target : BaseSort → Type}
    (base : ∀ sort, SubsetRepr (source.carriers.Base sort) (Target sort)) :
    Lifted source := by
  let carriers : FO.Carriers := {
    Base := Target
    Fn := source.carriers.Fn
    baseNonempty := fun sort => (base sort).targetNonempty
    fnNonempty := source.carriers.fnNonempty }
  let relation : FO.CarrierRel source.carriers carriers :=
    FO.CarrierRel.ofBase base fun domain codomain =>
      @SubsetRepr.refl (source.carriers.Fn domain codomain)
        (source.carriers.fnNonempty domain codomain)
  exact {
    target := source.lift carriers relation
    relation
    models := source.lift_rel carriers relation }

/-- Add one dependency block while retaining one source-to-current-model
relation for the complete symbol family. -/
noncomputable def extend {symbols : FO.SymbolFamily.{u}}
    {source : FO.FamilyModel symbols} (prior : Lifted source)
    {arity : Nat} {block : Block arity} {datatypeSymbols : DatatypeSymbols symbols block}
    (law : IsFreeDatatypeFamilyModel datatypeSymbols source) (wf : block.WF)
    (productive : Productive block) : Lifted source where
  target := law.extend wf productive prior.target prior.relation prior.models
  relation := BaseLift.carrierRel wf productive prior.relation law.carrier
  models := law.extend_rel wf productive prior.target prior.relation prior.models

end Lifted

end Crush.Metatheory.Datatype
