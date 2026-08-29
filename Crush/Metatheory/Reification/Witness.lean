import Crush.Metatheory.Reification.Reify

/-!
# Structural Lean-to-HO reification witnesses

The executable reifier already returns an intrinsically typed `PackedTerm` and
checks its retained Lean type with `isDefEqGuarded`.  This module retains that
check together with a recursive constructor-shape correspondence.  It does not
define a denotation for arbitrary `Lean.Expr`; semantic statements can later be
made relative to explicit interpretations of the retained constants.
-/

namespace Crush.Metatheory.Reification

open Lean Meta

/-- Recursive constructor shape of the supported Lean source fragment. -/
inductive ExprShape where
  | variable
  | constant
  | boolLit
  | not (body : ExprShape)
  | and (left right : ExprShape)
  | or (left right : ExprShape)
  | iff (left right : ExprShape)
  | eq (left right : ExprShape)
  | lam (body : ExprShape)
  | app (fn argument : ExprShape)
  | forallE (domain body : ExprShape)
  | existsE (body : Option ExprShape)
  | metadata (body : ExprShape)
  | unsupported
  deriving BEq, Repr

/-- Recursive constructor shape of an intrinsically typed reification result. -/
inductive TermShape where
  | variable
  | constant
  | boolLit
  | not (body : TermShape)
  | and (left right : TermShape)
  | or (left right : TermShape)
  | imp (left right : TermShape)
  | iff (left right : TermShape)
  | eq (left right : TermShape)
  | lam (body : TermShape)
  | app (fn argument : TermShape)
  | forallE (body : TermShape)
  | existsE (body : TermShape)
  deriving BEq, Repr

/-- Pure structural view of a Lean expression. Logical applications discard
their erased type arguments in exactly the same places as `reifyTerm?`. -/
def exprShape : Expr → ExprShape
  | .bvar _ | .fvar _ => .variable
  | .const name _ =>
      if name == ``True || name == ``False then .boolLit else .constant
  | .lam _ _ body _ => .lam (exprShape body)
  | .forallE _ domain body _ => .forallE (exprShape domain) (exprShape body)
  | .app fn argument =>
      let fnShape := exprShape fn
      let argumentShape := exprShape argument
      match fn with
      | .const name _ =>
          if name == ``Not then .not argumentShape
          else .app fnShape argumentShape
      | .app (.const name _) left =>
          let leftShape := exprShape left
          if name == ``And then .and leftShape argumentShape
          else if name == ``Or then .or leftShape argumentShape
          else if name == ``Iff then .iff leftShape argumentShape
          else if name == ``Exists then
            match argument with
            | .lam _ _ body _ => .existsE (some (exprShape body))
            | _ => .existsE none
          else .app fnShape argumentShape
      | .app (.app (.const name _) _) left =>
          if name == ``Eq then .eq (exprShape left) argumentShape
          else .app fnShape argumentShape
      | _ => .app fnShape argumentShape
  | .mdata _ body => .metadata (exprShape body)
  | _ => .unsupported

/-- Pure recursive structural view of an intrinsic HO term. -/
def termShape {signature : Signature} :
    {context : Context} → {type : Ty} →
      Term signature context type → TermShape
  | _, _, .var _ => .variable
  | _, _, .const _ => .constant
  | _, _, .boolLit _ => .boolLit
  | _, _, .not body => .not (termShape body)
  | _, _, .and left right => .and (termShape left) (termShape right)
  | _, _, .or left right => .or (termShape left) (termShape right)
  | _, _, .imp left right => .imp (termShape left) (termShape right)
  | _, _, .iff left right => .iff (termShape left) (termShape right)
  | _, _, .eq left right => .eq (termShape left) (termShape right)
  | _, _, .lam body => .lam (termShape body)
  | _, _, .app fn argument => .app (termShape fn) (termShape argument)
  | _, _, .forallE body => .forallE (termShape body)
  | _, _, .existsE body => .existsE (termShape body)

def PackedTerm.shape {signature : Signature} {context : Context} :
    PackedTerm signature context → TermShape
  | .pack _ term => termShape term

/-- Recursive compatibility of the source and intrinsic constructor trees.
A Lean `forallE` may reify either as implication or as quantification, depending
on whether its nondependent domain is a proposition. Metadata is transparent. -/
def shapesMatch : ExprShape → TermShape → Bool
  | .variable, .variable | .constant, .constant | .boolLit, .boolLit => true
  | .not source, .not target | .lam source, .lam target =>
      shapesMatch source target
  | .and sourceLeft sourceRight, .and targetLeft targetRight
  | .or sourceLeft sourceRight, .or targetLeft targetRight
  | .iff sourceLeft sourceRight, .iff targetLeft targetRight
  | .eq sourceLeft sourceRight, .eq targetLeft targetRight
  | .app sourceLeft sourceRight, .app targetLeft targetRight =>
      shapesMatch sourceLeft targetLeft && shapesMatch sourceRight targetRight
  | .forallE sourceDomain sourceBody, .imp targetDomain targetBody =>
      shapesMatch sourceDomain targetDomain && shapesMatch sourceBody targetBody
  | .forallE _ sourceBody, .forallE targetBody =>
      shapesMatch sourceBody targetBody
  | .existsE none, .existsE _ => true
  | .existsE (some sourceBody), .existsE targetBody =>
      shapesMatch sourceBody targetBody
  | .metadata source, target => shapesMatch source target
  | _, _ => false

/-- The live type inferred for a source expression after the executable reifier
accepted it as definitionally equal to `expected`.  This records the checked
metaprogramming boundary; it is not a kernel theorem about `Lean.Expr`. -/
structure TypeCorrespondence (expression expected : Expr) where
  inferred : Expr

/-- Exact recursive constructor correspondence for one reification result. -/
def ConstructorCorrespondence {signature : Signature} {context : Context}
    (expression : Expr) (term : PackedTerm signature context) : Prop :=
  shapesMatch (exprShape expression) term.shape = true

/-- Structural witness from one live Lean expression to one intrinsic HO term. -/
structure ReificationWitness {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr)
    (term : PackedTerm signature context) where
  typeCorrespondence : TypeCorrespondence expression term.type.expr
  contextCorrespondence : ContextBridge context
  context_eq : contextCorrespondence = contextBridge
  constructorCorrespondence : ConstructorCorrespondence expression term
  constantsCorrespond : SignatureBridge signature
  constants_eq : constantsCorrespond = signatureBridge

/-- Existential typed result of proof-facing reification. -/
structure Reified {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr) where
  term : PackedTerm signature context
  witness : ReificationWitness signatureBridge contextBridge expression term

/-- Proposition-level spelling used by later composition theorems. -/
def Reifies {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr)
    (term : PackedTerm signature context) : Prop :=
  Nonempty (ReificationWitness signatureBridge contextBridge expression term)

/-- Run the existing typed reifier and retain its structural witness. -/
partial def reify? {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr) :
    MetaM (Option (Reified signatureBridge contextBridge expression)) := do
  let some term ← reifyTerm? signatureBridge contextBridge expression | return none
  let inferred ← inferType expression
  if correspondence :
      shapesMatch (exprShape expression) term.shape = true then
    return some {
      term
      witness := {
        typeCorrespondence := { inferred }
        contextCorrespondence := contextBridge
        context_eq := rfl
        constructorCorrespondence := correspondence
        constantsCorrespond := signatureBridge
        constants_eq := rfl } }
  return none

/-- Existential intrinsic sentence obtained from a closed supported Lean
proposition. The exact finite constant signature and structural witness remain
available after unpacking. -/
inductive ReifiedSentence (expression : Expr) where
  | pack {signature : Signature} (signatureBridge : SignatureBridge signature)
      (typeExpr : Expr) (source : Sentence signature)
      (witness : ReificationWitness signatureBridge ContextBridge.nil expression
        (.pack (.bool typeExpr) source)) : ReifiedSentence expression

/-- Reify a closed Lean proposition into the typed HO sentence consumed by the
proved VCG route. Non-formulas and unsupported syntax are rejected. -/
partial def reifySentence? (expression : Expr) :
    MetaM (Option (ReifiedSentence expression)) := do
  let .pack signatureBridge ← reifyTermSignature expression
  let some reified ← reify? signatureBridge ContextBridge.nil expression | return none
  match reified with
  | ⟨.pack (.bool typeExpr) source, witness⟩ =>
      return some (.pack signatureBridge typeExpr source witness)
  | ⟨.pack (.base _ _) _, _⟩ | ⟨.pack (.arrow _ _ _) _, _⟩ => return none

end Crush.Metatheory.Reification
