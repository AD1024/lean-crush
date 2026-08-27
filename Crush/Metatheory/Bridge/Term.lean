import Crush.Metatheory.Bridge.Capture

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

namespace Crush.Metatheory.Bridge

open Lean

variable {signature : Signature} {context : Context}

/-- A position-preserving live representation of the intrinsic constant
signature. As for `ContextBridge`, each intrinsic type is definitionally derived
from its `TypeBridge`. -/
inductive SignatureBridge : Signature → Type where
  | nil : SignatureBridge []
  | cons {signature : Signature}
      (expression : Expr) (type : TypeBridge)
      (tail : SignatureBridge signature) : SignatureBridge (type.ty :: signature)

/-- An existentially typed constant lookup result. -/
inductive FoundConst (signature : Signature) where
  | pack (type : TypeBridge) (ref : Const signature type.ty) : FoundConst signature

namespace SignatureBridge

/-- Exact-expression lookup, matching the production structural signature's
identity criterion. Definitional-equality normalization is deliberately not
hidden in this pure operation. -/
def find? : {signature : Signature} → SignatureBridge signature → Expr →
    Option (FoundConst signature)
  | [], .nil, _ => none
  | _ :: _, .cons head type tail, expression =>
      if head == expression then
        some (.pack type .here)
      else
        (tail.find? expression).map fun
          | .pack foundType ref => .pack foundType (.there ref)

def expressions : {signature : Signature} → SignatureBridge signature → List Expr
  | [], .nil => []
  | _ :: _, .cons expression _ tail => expression :: tail.expressions

end SignatureBridge

/-- An existentially typed local-variable lookup result. -/
inductive FoundVar (context : Context) where
  | pack (type : TypeBridge) (ref : Var context type.ty) : FoundVar context

namespace ContextBridge

/-- Lookup of an SMT-local Lean free variable in intrinsic context order. -/
def find? : {context : Context} → ContextBridge context → FVarId → Option (FoundVar context)
  | [], .nil, _ => none
  | _ :: _, .cons head type tail, fvar =>
      if head == fvar then
        some (.pack type .here)
      else
        (tail.find? fvar).map fun
          | .pack foundType ref => .pack foundType (.there ref)

end ContextBridge

/-- A successfully reified, intrinsically typed source term with its live type
bridge retained. -/
inductive PackedTerm (signature : Signature) (context : Context) where
  | pack (type : TypeBridge) (term : Term signature context type.ty) :
      PackedTerm signature context

namespace PackedTerm

def type : PackedTerm signature context → TypeBridge
  | .pack type _ => type

def core : (term : PackedTerm signature context) →
    Term signature context term.type.ty
  | .pack _ term => term

def ofVar : FoundVar context → PackedTerm signature context
  | .pack type ref => .pack type (.var ref)

def ofConst : FoundConst signature → PackedTerm signature context
  | .pack type ref => .pack type (.const ref)

/-- Canonical bridge for the proposition/formula type. -/
def propositionType : TypeBridge := .bool (.sort .zero)

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

/-- Typed equality construction; unlike the live translator, this cannot pair
terms merely because their emitted SMT sorts happen to coincide. -/
def eq? : PackedTerm signature context → PackedTerm signature context →
    Option (PackedTerm signature context)
  | .pack leftType left, .pack rightType right =>
      if equality : rightType.ty = leftType.ty then
        some (.pack propositionType (.eq left (equality ▸ right)))
      else
        none

/-- Typed application construction. The returned bridge is the actual codomain
stored in the reified function type. -/
def app? : PackedTerm signature context → PackedTerm signature context →
    Option (PackedTerm signature context)
  | .pack (.arrow _ domain codomain) fn, .pack argumentType argument =>
      if equality : argumentType.ty = domain.ty then
        some (.pack codomain (.app fn (equality ▸ argument)))
      else
        none
  | _, _ => none

/-- Construct a lambda after its body has been reified under the extended
intrinsic/live context. -/
def lam (arrowExpr : Expr) (domain : TypeBridge)
    (body : PackedTerm signature (domain.ty :: context)) :
    PackedTerm signature context :=
  match body with
  | .pack codomain term => .pack (.arrow arrowExpr domain codomain) (.lam term)

def forallE? (domain : TypeBridge) :
    PackedTerm signature (domain.ty :: context) → Option (PackedTerm signature context)
  | .pack (.bool _) body => some (.pack propositionType (.forallE body))
  | _ => none

def existsE? (domain : TypeBridge) :
    PackedTerm signature (domain.ty :: context) → Option (PackedTerm signature context)
  | .pack (.bool _) body => some (.pack propositionType (.existsE body))
  | _ => none

end PackedTerm

end Crush.Metatheory.Bridge
