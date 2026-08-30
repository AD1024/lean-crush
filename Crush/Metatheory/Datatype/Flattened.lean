import Crush.Metatheory.Datatype.FamilyModel
import Crush.Metatheory.Defunctionalization.Flattened.Symbol

/-!
# Datatype ownership in the flattened symbol family

The generic native-component model is instantiated here for the actual
flattened symbols produced by defunctionalization.
-/

namespace Crush.Metatheory.Datatype

open Crush.Metatheory.Defunctionalization.Flattened

/-- Erasing one datatype field type agrees with its intrinsic FO sort. -/
@[simp] theorem ofTy_field {arity : Nat} {block : Block arity}
    (field : FieldDecl arity) :
    FO.FOSort.ofTy (field.ty block) = field.fo block := by
  cases field with
  | mk name sort => cases sort <;> rfl

/-- Arrow flattening preserves a constructor field telescope exactly. -/
@[simp] theorem flatten_fields {arity : Nat} {block : Block arity}
    (fields : List (FieldDecl arity)) (result : BaseSort) :
    FO.flattenArrow
      (fields.foldr (fun field rest => .arrow (field.ty block) rest)
        (.base result)) =
      (fields.map fun field => field.ty block, .base result) := by
  induction fields with
  | nil => rfl
  | cons field fields ih => simp [ih]

/-- A constructor's ordinary flattened declaration is its intrinsic datatype
declaration. -/
theorem sourceDecl_ctor {arity : Nat} {block : Block arity}
    (fields : List (FieldDecl arity)) (result : BaseSort) :
    Defunctionalization.sourceDecl
      (fields.foldr (fun field rest => .arrow (field.ty block) rest)
        (.base result)) =
      { args := fields.map fun field => field.fo block
        result := .base result } := by
  simp [Defunctionalization.sourceDecl]

@[simp] theorem sourceDecl_sel {arity : Nat} {block : Block arity}
    (data : DataRef block) (field : FieldDecl arity) :
    Defunctionalization.sourceDecl
      (.arrow (.base data.decl.sort) (field.ty block)) =
      field.sel block data := by
  cases field with
  | mk name sort => cases sort <;>
      rfl

@[simp] theorem sourceDecl_test {arity : Nat} {block : Block arity}
    (data : DataRef block) (ctor : CtorDecl arity) :
    Defunctionalization.sourceDecl
      (.arrow (.base data.decl.sort) .bool) = ctor.test block data := rfl

/-- Transport a family symbol along an equality of its declarations. -/
def castSymbol {symbols : FO.SymbolFamily} {actual expected : FO.SymbolDecl}
    (equal : actual = expected) (symbol : symbols actual) : symbols expected :=
  equal ▸ symbol

@[simp] theorem castSymbol_rfl {symbols : FO.SymbolFamily}
    {decl : FO.SymbolDecl} (symbol : symbols decl) :
    castSymbol rfl symbol = symbol := rfl

theorem FO.FamilyModel.symbol_cast {symbols : FO.SymbolFamily}
    (model : FO.FamilyModel symbols) {actual expected : FO.SymbolDecl}
    (equal : actual = expected) (symbol : symbols actual) :
    model.symbol (castSymbol equal symbol) = equal ▸ model.symbol symbol := by
  cases equal
  rfl

/-- Casting a flattened source symbol changes only its declaration index. -/
theorem canonicalModel_cast_source {signature : Signature}
    (source : Model signature) {ty : Ty} (constant : Const signature ty)
    {expected : FO.SymbolDecl}
    (equal : Defunctionalization.sourceDecl ty = expected) :
    HEq ((canonicalModel source).symbol
      (castSymbol equal (Symbol.sourceConstant constant)))
      (flattenedDenote source ty (source.const constant)) := by
  cases equal
  rfl

private theorem heq_fun {α β γ : Type} (inhabited : Nonempty α)
    (left : α → β) (right : α → γ)
    (pointwise : ∀ value, HEq (left value) (right value)) :
    HEq left right := by
  let value := Classical.choice inhabited
  have equal : β = γ := type_eq_of_heq (pointwise value)
  subst γ
  apply heq_of_eq
  funext value
  exact eq_of_heq (pointwise value)

/-- The flattened source-constant symbols owned by one datatype block. -/
def Symbols.native {signature : Signature} {arity : Nat}
    {block : Block arity} (symbols : Symbols signature block) :
    NativeSymbols (Symbol signature) block where
  ctor := fun {data} {decl} ref => by
    exact castSymbol (by
      simpa [CtorDecl.fo, CtorDecl.ty] using
        sourceDecl_ctor (block := block) decl.fields data.decl.sort)
      (Symbol.sourceConstant (symbols.ctor ref))
  sel := fun {_data} {_ctor} ctorRef {_field} fieldRef => by
    cases _field with
    | mk name sort =>
        cases sort <;>
          exact Symbol.sourceConstant (symbols.sel ctorRef fieldRef)
  test := fun {_data} {_ctor} ref =>
    Symbol.sourceConstant (symbols.test ref)

/-- Flattening a canonical constructor telescope is exactly FO constructor
currying over the canonical carriers. -/
theorem flattenedDenote_curry {signature : Signature} {arity : Nat}
    {block : Block arity} (source : Model signature)
    (carrier : ∀ data : DataRef block,
      Iso (source.Base data.decl.sort) (Val block source.Base data)) :
    (fields : List (FieldDecl arity)) → (result : BaseSort) →
    (build : Args block source.Base fields → source.Base result) →
    HEq (flattenedDenote source
        (fields.foldr (fun field rest => .arrow (field.ty block) rest)
          (.base result))
        (Args.curry carrier fields (.base result) build))
      (BaseLift.sourceCurry (Defunctionalization.canonicalCarriers source)
        carrier fields result build)
  | [], _, _ => by
      simp [flattenedDenote, Args.curry, BaseLift.sourceCurry,
        Defunctionalization.toCanonical]
  | field :: rest, result, build => by
      cases field with
      | mk name sort =>
          cases sort with
          | base base =>
              simp only [List.foldr, FieldDecl.ty, FieldSort.ty,
                Args.curry, flattenedDenote, BaseLift.sourceCurry,
                Defunctionalization.fromCanonical]
              apply heq_fun (source.baseNonempty base)
              intro value
              exact flattenedDenote_curry source carrier rest result
                (fun tail => build (.base value tail))
          | data child =>
              simp only [List.foldr, FieldDecl.ty, FieldSort.ty,
                Args.curry, flattenedDenote, BaseLift.sourceCurry,
                Defunctionalization.fromCanonical]
              apply heq_fun (source.baseNonempty
                (DataRef.decl (block := block) child).sort)
              intro value
              exact flattenedDenote_curry source carrier rest result
                (fun tail => build (.data ((carrier child).to value) tail))

/-- A lawful HO datatype source model supplies the corresponding laws for the
ordinary flattened FO family model. -/
noncomputable def Lawful.flattened {signature : Signature} {arity : Nat}
    {block : Block arity} {symbols : Symbols signature block}
    {source : Model signature} (law : Lawful symbols source) :
    FamilyLawful symbols.native (canonicalModel source) where
  carrier := law.carrier
  ctor_denote := by
    intro data ctor ref
    simp only [Symbols.native]
    apply eq_of_heq
    let equal : Defunctionalization.sourceDecl (ctor.ty block data) =
        ctor.fo block data := by
      simpa [CtorDecl.fo, CtorDecl.ty] using
        sourceDecl_ctor (block := block) ctor.fields data.decl.sort
    have casted := canonicalModel_cast_source source
      (symbols.ctor ref) equal
    have sourceEq := congrArg
      (flattenedDenote source (ctor.ty block data))
      (law.ctor_denote ref)
    exact casted.trans ((heq_of_eq sourceEq).trans
      (flattenedDenote_curry source law.carrier ctor.fields
        data.decl.sort (fun args =>
          (law.carrier data).«from» (.ctor ref args))))
  sel_ctor := by
    intro data ctor ctorRef field fieldRef args
    cases field with
    | mk name sort =>
        cases sort with
        | base base =>
            simpa [Symbols.native, canonicalModel_sourceConstant, flattenedDenote,
              Defunctionalization.fromCanonical,
              Defunctionalization.toCanonical,
              BaseLift.sourceField, FieldDecl.fromVal,
              FieldDecl.ty, FieldSort.ty, FieldDecl.fo, FieldSort.fo,
              FO.SymbolDenote]
              using law.sel_ctor ctorRef fieldRef args
        | data child =>
            simpa [Symbols.native, canonicalModel_sourceConstant, flattenedDenote,
              Defunctionalization.fromCanonical,
              Defunctionalization.toCanonical,
              BaseLift.sourceField, FieldDecl.fromVal,
              FieldDecl.ty, FieldSort.ty, FieldDecl.fo, FieldSort.fo,
              FO.SymbolDenote]
              using law.sel_ctor ctorRef fieldRef args
  test_denote := by
    intro data ctor ref value
    simpa [Symbols.native, flattenedDenote,
      Defunctionalization.fromCanonical] using
      law.test_denote ref value

namespace Env

/-- Structural well-formedness for every dependency block. Cross-block
ownership and dependency order are retained by `Native.Step.Ordered`. -/
inductive BlocksWF {signature : Signature} : Env signature → Type where
  | nil : BlocksWF []
  | cons {entry : Entry signature} {rest : Env signature} :
      entry.block.WF → BlocksWF rest → BlocksWF (entry :: rest)

private noncomputable def liftAux {signature : Signature}
    (source : Model signature) :
    (env : Env signature) → Lawful source env → BlocksWF env →
      Lifted (canonicalModel source) → Lifted (canonicalModel source)
  | [], .nil, .nil, prior => prior
  | _ :: _, .cons headLaw tailLaw, .cons headWF tailWF, prior =>
      liftAux source _ tailLaw tailWF
        (prior.extend headLaw.flattened headWF headLaw.productive)

/-- Extend an arbitrary already-related base model with every dependency block.
This is the entry point for interpreted carriers such as `Nat → Int`; datatype
lifting itself is independent of which guarded base representation came first. -/
noncomputable def liftFrom {signature : Signature} (source : Model signature)
    (env : Env signature) (lawful : Lawful source env)
    (wf : BlocksWF env) (prior : Lifted (canonicalModel source)) :
    Lifted (canonicalModel source) :=
  liftAux source env lawful wf prior

/-- Compose every dependency block over the identity base representation. -/
noncomputable def lift {signature : Signature} (source : Model signature)
    (env : Env signature) (lawful : Lawful source env)
    (wf : BlocksWF env) : Lifted (canonicalModel source) :=
  liftFrom source env lawful wf (Lifted.refl (canonicalModel source))

end Env

end Crush.Metatheory.Datatype
