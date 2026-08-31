import Crush.Metatheory.Reification.Capture

/-!
# Typed term-reification substrate

This module supplies the dependent data structures used by the executable Lean
`Expr` reifier. A successful lookup or smart constructor cannot return an
ill-typed core term: the source signature, local context, and result type are all
indices of the returned value.

Parsing elaborated Lean logical constants is intentionally separated from these
pure constructors. That parser is the remaining metaprogramming layer; it will
produce `PackedTerm`s rather than reconstructing typing invariants independently.
-/

namespace Crush.Metatheory.Reification

open Lean

variable {signature : Signature} {context : Context}

/-- A position-preserving reification of a typed constant
signature. As for `ReifiedContext`, each typed source index is definitionally derived
from its `ReifiedType`. -/
inductive ReifiedSignature : Signature → Type where
  | nil : ReifiedSignature []
  | cons {signature : Signature}
      (expression : Expr) (type : ReifiedType)
      (tail : ReifiedSignature signature) : ReifiedSignature (type.ty :: signature)
  /-- A typed source constant supplied by a structural component rather than by
  ordinary expression lookup. Datatype reification selects these slots through
  its exact constructor/selector/tester references. -/
  | hidden {signature : Signature} (type : Ty)
      (tail : ReifiedSignature signature) : ReifiedSignature (type :: signature)

/-- An existentially typed constant lookup result. -/
inductive FoundConst (signature : Signature) where
  | pack (type : ReifiedType) (ref : Const signature type.ty) : FoundConst signature

namespace ReifiedSignature

/-- Exact-expression lookup, matching the translator structural signature's
identity criterion. Definitional-equality normalization is deliberately not
hidden in this pure operation. -/
def find? : {signature : Signature} → ReifiedSignature signature → Expr →
    Option (FoundConst signature)
  | [], .nil, _ => none
  | _ :: _, .cons head type tail, expression =>
      if head == expression then
        some (.pack type .here)
      else
        (tail.find? expression).map fun
          | .pack foundType ref => .pack foundType (.there ref)
  | _ :: _, .hidden _ tail, expression =>
      (tail.find? expression).map fun
        | .pack foundType ref => .pack foundType (.there ref)

def expressions : {signature : Signature} → ReifiedSignature signature → List Expr
  | [], .nil => []
  | _ :: _, .cons expression _ tail => expression :: tail.expressions
  | _ :: _, .hidden _ tail => tail.expressions

/-- Reserve a typed structural prefix while preserving ordinary expression
lookup in the tail. -/
def prepend (head : Signature) {signature : Signature}
    (reified : ReifiedSignature signature) : ReifiedSignature (head ++ signature) :=
  match head with
  | [] => reified
  | type :: head => .hidden type (reified.prepend head)

end ReifiedSignature

/-- An existentially typed local-variable lookup result. -/
inductive FoundVar (context : Context) where
  | pack (type : ReifiedType) (ref : Var context type.ty) : FoundVar context

namespace ReifiedContext

/-- Lookup of an SMT-local Lean free variable in reified context order. -/
def find? : {context : Context} → ReifiedContext context → FVarId → Option (FoundVar context)
  | [], .nil, _ => none
  | _ :: _, .cons head type tail, fvar =>
      if head == fvar then
        some (.pack type .here)
      else
        (tail.find? fvar).map fun
          | .pack foundType ref => .pack foundType (.there ref)

end ReifiedContext

/-- A successfully reified, intrinsically typed source term with its elaborated type
reified retained. -/
inductive PackedTerm (signature : Signature) (context : Context) where
  | pack (type : ReifiedType) (term : Term signature context type.ty) :
      PackedTerm signature context

namespace PackedTerm

def type : PackedTerm signature context → ReifiedType
  | .pack type _ => type

def core : (term : PackedTerm signature context) →
    Term signature context term.type.ty
  | .pack _ term => term

def ofVar : FoundVar context → PackedTerm signature context
  | .pack type ref => .pack type (.var ref)

def ofConst : FoundConst signature → PackedTerm signature context
  | .pack type ref => .pack type (.const ref)

/-- Package a datatype constant after checking that its elaborated Lean type
reified computes the declaration type carried by the typed reference. -/
def ofTypedConst? (type : ReifiedType) {expected : Ty}
    (ref : Const signature expected) : Option (PackedTerm signature context) :=
  if equal : type.ty = expected then
    some (.pack type (.const (equal.symm ▸ ref)))
  else
    none

/-- Canonical reified for the proposition/formula type. -/
def propositionType : ReifiedType := .bool (.sort .zero)

def boolLit (value : Bool) : PackedTerm signature context :=
  .pack propositionType (.boolLit value)

def not? : PackedTerm signature context → Option (PackedTerm signature context)
  | .pack (.bool _) body => some (.pack propositionType (.not body))
  | _ => none

def and? : PackedTerm signature context → PackedTerm signature context →
    Option (PackedTerm signature context)
  | .pack (.bool _) left, .pack (.bool _) right =>
      some (.pack propositionType (.and left right))
  | _, _ => none

def or? : PackedTerm signature context → PackedTerm signature context →
    Option (PackedTerm signature context)
  | .pack (.bool _) left, .pack (.bool _) right =>
      some (.pack propositionType (.or left right))
  | _, _ => none

def imp? : PackedTerm signature context → PackedTerm signature context →
    Option (PackedTerm signature context)
  | .pack (.bool _) left, .pack (.bool _) right =>
      some (.pack propositionType (.imp left right))
  | _, _ => none

def iff? : PackedTerm signature context → PackedTerm signature context →
    Option (PackedTerm signature context)
  | .pack (.bool _) left, .pack (.bool _) right =>
      some (.pack propositionType (.iff left right))
  | _, _ => none

/-- Typed equality construction; unlike the Crush translator, this cannot pair
terms merely because their emitted SMT sorts happen to coincide. -/
def eq? : PackedTerm signature context → PackedTerm signature context →
    Option (PackedTerm signature context)
  | .pack leftType left, .pack rightType right =>
      if equality : rightType.ty = leftType.ty then
        some (.pack propositionType (.eq left (equality ▸ right)))
      else
        none

/-- Typed application construction. The returned reified is the actual codomain
stored in the `ReifiedType` for the function. -/
def app? : PackedTerm signature context → PackedTerm signature context →
    Option (PackedTerm signature context)
  | .pack (.arrow _ domain codomain) fn, .pack argumentType argument =>
      if equality : argumentType.ty = domain.ty then
        some (.pack codomain (.app fn (equality ▸ argument)))
      else
        none
  | _, _ => none

/-- Construct a lambda after its body has been reified under the extended
reified/elaborated context. -/
def lam (arrowExpr : Expr) (domain : ReifiedType)
    (body : PackedTerm signature (domain.ty :: context)) :
    PackedTerm signature context :=
  match body with
  | .pack codomain term => .pack (.arrow arrowExpr domain codomain) (.lam term)

def forallE? (domain : ReifiedType) :
    PackedTerm signature (domain.ty :: context) → Option (PackedTerm signature context)
  | .pack (.bool _) body => some (.pack propositionType (.forallE body))
  | _ => none

def existsE? (domain : ReifiedType) :
    PackedTerm signature (domain.ty :: context) → Option (PackedTerm signature context)
  | .pack (.bool _) body => some (.pack propositionType (.existsE body))
  | _ => none

end PackedTerm

end Crush.Metatheory.Reification
