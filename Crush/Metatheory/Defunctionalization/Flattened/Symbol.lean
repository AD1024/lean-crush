import Crush.Metatheory.Defunctionalization.ModelExtension

/-!
# Symbols for flattened defunctionalization

The flattened transformation uses an abstract typed symbol family so recursive
translation can allocate symbols structurally before choosing concrete SMT names.
Constructors are classified by semantic role: source constants, flattened
application, and exact-capture closures.

`canonicalModel` gives every such symbol its intended interpretation in a model
constructed from an HO source model. Interpreted production hooks use the
separate semantic contracts in `Hooks.lean`; they are not extra identities in
the total structural translator's symbol family.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

variable {signature : Signature}

/-- Apply a source value to every argument in its leading arrow telescope and
coerce the final non-arrow result into the canonical target carrier. -/
@[reducible] def flattenedDenote (source : Model signature) :
    (ty : Ty) → ty.Denote source.Base →
      FO.SymbolDenote (canonicalCarriers source)
        ((FO.flattenArrow ty).1.map FO.FOSort.ofTy)
        (FO.FOSort.ofTy (FO.flattenArrow ty).2)
  | .bool, value => toCanonical source .bool value
  | .base sort, value => toCanonical source (.base sort) value
  | .arrow domain codomain, fn => fun argument =>
      flattenedDenote source codomain
        (fn (fromCanonical source domain argument))

@[simp] theorem flattenedDenote_bool (source : Model signature)
    (value : Prop) : flattenedDenote source .bool value = value := rfl

@[simp] theorem flattenedDenote_base (source : Model signature)
    (sort : BaseSort) (value : source.Base sort) :
    flattenedDenote source (.base sort) value = value := rfl

@[simp] theorem flattenedDenote_arrow (source : Model signature)
    (domain codomain : Ty)
    (fn : (Ty.arrow domain codomain).Denote source.Base)
    (argument : (FO.FOSort.ofTy domain).Denote (canonicalCarriers source)) :
    flattenedDenote source (.arrow domain codomain) fn argument =
      flattenedDenote source codomain
        (fn (fromCanonical source domain argument)) := rfl

/-- Typed FO symbols used by the flattened transformation. -/
inductive Symbol (signature : Signature) : FO.SymbolDecl → Type 1 where
  | sourceConstant {ty : Ty} (constant : Const signature ty) :
      Symbol signature (sourceDecl ty)
  | application (arrow : Arrow) :
      Symbol signature (FO.appDecl arrow.domain arrow.codomain)
  | closure (closure : Closure signature) :
      Symbol signature
        (FO.closureDecl closure.captureTypes closure.domain closure.codomain)

/-- Canonical semantics of the flattened symbol family.  Flattened application
is repeated source application, while closure symbols reconstruct the exact
captured environment. -/
@[reducible] noncomputable def canonicalModel
    (source : Model signature) : FO.FamilyModel (Symbol signature) where
  carriers := canonicalCarriers source
  symbol := fun symbol =>
    match symbol with
    | Symbol.sourceConstant (ty := ty) constant =>
        flattenedDenote source ty (source.const constant)
    | Symbol.application arrow =>
        flattenedDenote source (.arrow arrow.domain arrow.codomain)
    | Symbol.closure closure => interpretClosure source closure

/-! ## Target-language shorthands -/

/-- A flattened target term, indexed by its source signature, context, and type. -/
abbrev TargetTerm (σ : Signature) (Γ : Context) (τ : Ty) :=
  FO.FamilyTerm (Symbol σ) (targetContext Γ) (FO.FOSort.ofTy τ)

/-- A Boolean flattened target term in an erased source context. -/
abbrev TargetFormula (σ : Signature) (Γ : Context) :=
  FO.FamilyFormula (Symbol σ) (targetContext Γ)

/-- A closed flattened target formula. -/
abbrev TargetSentence (σ : Signature) := FO.FamilySentence (Symbol σ)

/-- A flattened target theory. -/
abbrev TargetTheory (σ : Signature) := FO.FamilyTheory (Symbol σ)

/-- A valuation for the canonical flattened model over an erased source context. -/
abbrev TargetValuation {σ : Signature} (M : Model σ) (Γ : Context) :=
  FO.FamilyValuation (canonicalModel M) (targetContext Γ)

@[simp] theorem canonicalModel_sourceConstant (source : Model signature)
    {ty : Ty} (constant : Const signature ty) :
    (canonicalModel source).symbol (Symbol.sourceConstant constant) =
      flattenedDenote source ty (source.const constant) := rfl

@[simp] theorem canonicalModel_application (source : Model signature)
    (arrow : Arrow) :
    (canonicalModel source).symbol (Symbol.application arrow) =
      flattenedDenote source (.arrow arrow.domain arrow.codomain) := rfl

@[simp] theorem canonicalModel_closure (source : Model signature)
    (closure : Closure signature) :
    (canonicalModel source).symbol (Symbol.closure closure) =
      interpretClosure source closure := rfl

end Crush.Metatheory.Defunctionalization.Flattened
