import Crush.Metatheory.Datatype.Carrier

/-!
# Native datatype components in one FO family model

One typed ownership map identifies the constructor, selector, and tester
symbols belonging to a datatype block. The target model gives those symbols
their full free-algebra meanings and lifts every other symbol generically.
-/

namespace Crush.Metatheory.Datatype

open Crush.Metatheory.Guarded

universe u

/-- Datatype-owned symbols inside an otherwise generic FO symbol family. -/
structure NativeSymbols (symbols : FO.SymbolFamily.{u}) {arity : Nat}
    (block : Block arity) where
  ctor : {data : DataRef block} → {decl : CtorDecl arity} →
    CtorRef block data decl → symbols (decl.fo block data)
  sel : {data : DataRef block} → {ctor : CtorDecl arity} →
    CtorRef block data ctor → {field : FieldDecl arity} →
    FieldRef ctor field → symbols (field.sel block data)
  test : {data : DataRef block} → {ctor : CtorDecl arity} →
    CtorRef block data ctor → symbols (ctor.test block data)

/-- A proof that a family symbol is owned by one native datatype component. -/
inductive NativeRef {symbols : FO.SymbolFamily.{u}} {arity : Nat}
    {block : Block arity} (native : NativeSymbols symbols block) :
    {decl : FO.SymbolDecl} → symbols decl → Type u where
  | ctor {data : DataRef block} {decl : CtorDecl arity}
      (ref : CtorRef block data decl) : NativeRef native (native.ctor ref)
  | sel {data : DataRef block} {ctor : CtorDecl arity}
      (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
      (fieldRef : FieldRef ctor field) :
      NativeRef native (native.sel ctorRef fieldRef)
  | test {data : DataRef block} {ctor : CtorDecl arity}
      (ref : CtorRef block data ctor) : NativeRef native (native.test ref)

/-- No family symbol has two datatype roles in the same block. -/
def NativeSymbols.Exclusive {symbols : FO.SymbolFamily.{u}} {arity : Nat}
    {block : Block arity} (native : NativeSymbols symbols block) : Prop :=
  ∀ {decl : FO.SymbolDecl} (symbol : symbols decl),
    Subsingleton (NativeRef native symbol)

/-- Source-model laws for one typed native ownership map. Selectors retain
their intentionally unspecified behavior away from their own constructor. -/
structure FamilyLawful {symbols : FO.SymbolFamily.{u}} {arity : Nat}
    {block : Block arity} (native : NativeSymbols symbols block)
    (source : FO.FamilyModel symbols) where
  carrier : ∀ data : DataRef block,
    Iso (source.carriers.Base data.decl.sort)
      (Val block source.carriers.Base data)
  ctor_denote : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor),
    source.symbol (native.ctor ref) =
      BaseLift.sourceCtor source.carriers carrier ref
  sel_ctor : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor)
    {field : FieldDecl arity} (fieldRef : FieldRef ctor field)
    (args : Args block source.carriers.Base ctor.fields),
    source.symbol (native.sel ctorRef fieldRef)
        ((carrier data).«from» (.ctor ctorRef args)) =
      BaseLift.sourceField carrier field (args.get fieldRef)
  test_denote : ∀ {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor)
    (value : source.carriers.Base data.decl.sort),
    source.symbol (native.test ref) value ↔
      IsCtor ref ((carrier data).to value)

namespace NativeRef

/-- Full target denotation selected by one native ownership witness. -/
noncomputable def denote {symbols : FO.SymbolFamily.{u}} {arity : Nat}
    {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers) :
    {decl : FO.SymbolDecl} → {symbol : symbols decl} →
      NativeRef native symbol →
      FO.SymbolDenote (BaseLift.carriers productive prior.carriers)
        decl.args decl.result
  | _, _, .ctor ref =>
      BaseLift.targetCtor wf productive prior.carriers ref
  | _, _, .sel ctorRef fieldRef =>
      BaseLift.targetSel wf productive priorRel law.carrier ctorRef fieldRef
        (source.symbol (native.sel ctorRef fieldRef))
  | _, _, .test ref =>
      BaseLift.targetTest wf productive prior.carriers ref

end NativeRef

/-! ## Dependency-ordered extension -/

/-- Extend a previously related target model by one later datatype block.
Symbols whose complete declaration is external to the new block are carried
from the prior model; symbols mentioning a newly owned sort are lifted afresh.
This preserves native interpretations installed by earlier dependency blocks
without adding a parallel ownership registry. -/
noncomputable def FamilyLawful.extend {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel) :
    FO.FamilyModel symbols := by
  classical
  exact {
    carriers := BaseLift.carriers productive prior.carriers
    symbol := fun {decl} symbol =>
      if owned : Nonempty (NativeRef native symbol) then
        (Classical.choice owned).denote law wf productive prior priorRel
      else if external : BaseLift.ExternalDecl block decl then
        BaseLift.carry productive external.1 external.2 (prior.symbol symbol)
      else
        FO.liftSymbol
          (BaseLift.carrierRel wf productive priorRel law.carrier)
          (source.symbol symbol) }

theorem FamilyLawful.extend_symbol_owned {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {decl : FO.SymbolDecl} (symbol : symbols decl)
    (owned : Nonempty (NativeRef native symbol)) :
    (law.extend wf productive prior priorRel priorModels).symbol symbol =
      (Classical.choice owned).denote law wf productive prior priorRel := by
  classical
  simp [FamilyLawful.extend, owned]

theorem FamilyLawful.extend_symbol_external {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {decl : FO.SymbolDecl} (symbol : symbols decl)
    (unowned : ¬Nonempty (NativeRef native symbol))
    (external : BaseLift.ExternalDecl block decl) :
    (law.extend wf productive prior priorRel priorModels).symbol symbol =
      BaseLift.carry productive external.1 external.2
        (prior.symbol symbol) := by
  classical
  simp [FamilyLawful.extend, unowned, external]

theorem FamilyLawful.extend_symbol_fresh {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (wf : block.WF) (productive : Productive block)
    (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {decl : FO.SymbolDecl} (symbol : symbols decl)
    (unowned : ¬Nonempty (NativeRef native symbol))
    (fresh : ¬BaseLift.ExternalDecl block decl) :
    (law.extend wf productive prior priorRel priorModels).symbol symbol =
      FO.liftSymbol
        (BaseLift.carrierRel wf productive priorRel law.carrier)
        (source.symbol symbol) := by
  classical
  simp [FamilyLawful.extend, unowned, fresh]

/-- One dependency step preserves every source symbol. Earlier external
interpretations use `carry_rel`; current or forward-looking symbols use the
ordinary canonical lift. -/
theorem FamilyLawful.extend_rel {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
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
    by_cases owned : Nonempty (NativeRef native symbol)
    · rw [law.extend_symbol_owned wf productive prior priorRel priorModels
          symbol owned]
      let ref := Classical.choice owned
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
            priorModels symbol owned external]
        exact BaseLift.carry_rel wf productive priorRel law.carrier
          external.1 external.2 (source.symbol symbol) (prior.symbol symbol)
          (priorModels.symbol symbol)
      · rw [law.extend_symbol_fresh wf productive prior priorRel priorModels
            symbol owned external]
        exact FO.liftSymbol_rel
          (BaseLift.carrierRel wf productive priorRel law.carrier)
          (source.symbol symbol)

/-- Exclusive ownership selects the exact current-block native operation in a
dependency extension. -/
theorem FamilyLawful.extend_native {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (exclusive : native.Exclusive) (wf : block.WF)
    (productive : Productive block) (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {decl : FO.SymbolDecl} {symbol : symbols decl}
    (ref : NativeRef native symbol) :
    (law.extend wf productive prior priorRel priorModels).symbol symbol =
      ref.denote law wf productive prior priorRel := by
  rw [law.extend_symbol_owned wf productive prior priorRel priorModels
    symbol ⟨ref⟩]
  have chosen : Classical.choice
      (show Nonempty (NativeRef native symbol) from ⟨ref⟩) = ref :=
    exclusive _ |>.elim _ _
  rw [chosen]

theorem FamilyLawful.extend_ctor {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (exclusive : native.Exclusive) (wf : block.WF)
    (productive : Productive block) (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) :
    (law.extend wf productive prior priorRel priorModels).symbol
        (native.ctor ref) =
      BaseLift.targetCtor wf productive prior.carriers ref := by
  simpa [NativeRef.denote, CtorDecl.fo] using
    law.extend_native exclusive wf productive prior priorRel priorModels
      (NativeRef.ctor ref)

theorem FamilyLawful.extend_sel {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (exclusive : native.Exclusive) (wf : block.WF)
    (productive : Productive block) (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) :
    (law.extend wf productive prior priorRel priorModels).symbol
        (native.sel ctorRef fieldRef) =
      BaseLift.targetSel wf productive priorRel law.carrier ctorRef fieldRef
        (source.symbol (native.sel ctorRef fieldRef)) := by
  simpa [NativeRef.denote, FieldDecl.sel] using
    law.extend_native exclusive wf productive prior priorRel priorModels
      (NativeRef.sel ctorRef fieldRef)

theorem FamilyLawful.extend_test {symbols : FO.SymbolFamily.{u}}
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    {source : FO.FamilyModel symbols} (law : FamilyLawful native source)
    (exclusive : native.Exclusive) (wf : block.WF)
    (productive : Productive block) (prior : FO.FamilyModel symbols)
    (priorRel : FO.CarrierRel source.carriers prior.carriers)
    (priorModels : FO.ModelRel source prior priorRel)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) :
    (law.extend wf productive prior priorRel priorModels).symbol
        (native.test ref) =
      BaseLift.targetTest wf productive prior.carriers ref := by
  simpa [NativeRef.denote, CtorDecl.test] using
    law.extend_native exclusive wf productive prior priorRel priorModels
      (NativeRef.test ref)

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

/-- Canonically enlarge only the opaque base carriers of a family model. The
defunctionalized function-value carriers stay unchanged; every source symbol is
totalized through the supplied guarded base relations. This is the initial
model used, for example, when `Nat` is represented by guarded `Int`. -/
noncomputable def ofBase {symbols : FO.SymbolFamily.{u}}
    (source : FO.FamilyModel symbols) {Target : BaseSort → Type}
    (base : ∀ sort, SubsetRepresentation (source.carriers.Base sort) (Target sort)) :
    Lifted source := by
  let carriers : FO.Carriers := {
    Base := Target
    Fn := source.carriers.Fn
    baseNonempty := fun sort => (base sort).targetNonempty
    fnNonempty := source.carriers.fnNonempty }
  let relation : FO.CarrierRel source.carriers carriers :=
    FO.CarrierRel.ofBase base fun domain codomain =>
      @SubsetRepresentation.refl (source.carriers.Fn domain codomain)
        (source.carriers.fnNonempty domain codomain)
  exact {
    target := source.lift carriers relation
    relation
    models := source.lift_rel carriers relation }

/-- Add one dependency block while retaining one source-to-current-model
relation for the complete symbol family. -/
noncomputable def extend {symbols : FO.SymbolFamily.{u}}
    {source : FO.FamilyModel symbols} (prior : Lifted source)
    {arity : Nat} {block : Block arity} {native : NativeSymbols symbols block}
    (law : FamilyLawful native source) (wf : block.WF)
    (productive : Productive block) : Lifted source where
  target := law.extend wf productive prior.target prior.relation prior.models
  relation := BaseLift.carrierRel wf productive prior.relation law.carrier
  models := law.extend_rel wf productive prior.target prior.relation prior.models

end Lifted

end Crush.Metatheory.Datatype
