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
open Crush.Metatheory.Datatype

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

/-- One exact datatype-owned declaration used by a reified term. -/
inductive DataUse (env : DatatypeEnv) where
  | ctor (found : DatatypeEnv.FoundBlock env.blocks.toList)
      (ctor : found.Ctor)
  | sel (found : DatatypeEnv.FoundBlock env.blocks.toList)
      (ctor : found.Ctor) (field : ctor.Field)

/-- Erase only certified datatype type parameters while retaining exact typed
ownership references for every constructor and selector encountered. -/
partial def eraseData (env : DatatypeEnv) (expression : Expr) :
    MetaM (Expr × List (DataUse env)) := do
  if let some app ← env.ctorApp? expression then
    let mut erased : Array Expr := #[]
    let mut uses : List (DataUse env) := [.ctor app.found app.ctor]
    for argument in app.values do
      let (term, nested) ← eraseData env argument
      erased := erased.push term
      uses := uses ++ nested
    return (mkAppN app.head erased, uses)
  if let some app ← env.projApp? expression then
    let (target, nested) ← eraseData env app.target
    return (mkApp app.head target, .sel app.found app.ctor app.field :: nested)
  match expression with
  | .app fn argument =>
      let (fn, fnUses) ← eraseData env fn
      let (argument, argumentUses) ← eraseData env argument
      return (.app fn argument, fnUses ++ argumentUses)
  | .lam name type body info =>
      let (body, uses) ← eraseData env body
      return (.lam name type body info, uses)
  | .forallE name type body info =>
      let (type, typeUses) ← eraseData env type
      let (body, bodyUses) ← eraseData env body
      return (.forallE name type body info, typeUses ++ bodyUses)
  | .letE name type value body nondep =>
      let (value, valueUses) ← eraseData env value
      let (body, bodyUses) ← eraseData env body
      return (.letE name type value body nondep, valueUses ++ bodyUses)
  | .mdata data body =>
      let (body, uses) ← eraseData env body
      return (.mdata data body, uses)
  | .proj name index body =>
      let (body, uses) ← eraseData env body
      return (.proj name index body, uses)
  | _ => return (expression, [])

/-- Datatype declaration evidence retained at the metaprogramming refinement
boundary. `none` is the original uninterpreted-only route. -/
inductive DataTrace {signature : Signature} :
    Option (DataBridge signature) → Type where
  | none : DataTrace none
  | certified (bridge : DataBridge signature)
      (uses : List (DataUse bridge.env)) : DataTrace (some bridge)

structure ShapeResult {signature : Signature}
    (datatypes : Option (DataBridge signature)) where
  shape : ExprShape
  trace : DataTrace datatypes

private partial def sourceShape {signature : Signature} (expression : Expr) :
    (datatypes : Option (DataBridge signature)) → MetaM (ShapeResult datatypes)
  | none => return ⟨exprShape expression, .none⟩
  | some bridge => do
      let (erased, uses) ← eraseData bridge.env expression
      return ⟨exprShape erased, .certified bridge uses⟩

/-- Exact recursive constructor correspondence after erasing only the certified
datatype parameters recorded in the witness. -/
def ConstructorCorrespondence {signature : Signature} {context : Context}
    (source : ExprShape) (term : PackedTerm signature context) : Prop :=
  shapesMatch source term.shape = true

/-- Structural witness from one live Lean expression to one intrinsic HO term. -/
structure ReificationWitness {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr)
    (term : PackedTerm signature context)
    (datatypes : Option (DataBridge signature) := none) where
  typeCorrespondence : TypeCorrespondence expression term.type.expr
  contextCorrespondence : ContextBridge context
  context_eq : contextCorrespondence = contextBridge
  sourceShape : ExprShape
  constructorCorrespondence : ConstructorCorrespondence sourceShape term
  dataTrace : DataTrace datatypes
  constantsCorrespond : SignatureBridge signature
  constants_eq : constantsCorrespond = signatureBridge

/-- Existential typed result of proof-facing reification. -/
structure Reified {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr)
    (datatypes : Option (DataBridge signature) := none) where
  term : PackedTerm signature context
  witness : ReificationWitness signatureBridge contextBridge expression term datatypes

/-- Proposition-level spelling used by later composition theorems. -/
def Reifies {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr)
    (term : PackedTerm signature context)
    (datatypes : Option (DataBridge signature) := none) : Prop :=
  Nonempty (ReificationWitness signatureBridge contextBridge expression term datatypes)

/-- Run the existing typed reifier and retain its structural witness. -/
partial def reify? {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr)
    (datatypes : Option (DataBridge signature) := none) :
    MetaM (Option (Reified signatureBridge contextBridge expression datatypes)) := do
  let some term ← reifyTerm? signatureBridge contextBridge expression datatypes
    | return none
  let inferred ← inferType expression
  let shape ← sourceShape expression datatypes
  if correspondence :
      shapesMatch shape.shape term.shape = true then
    return some {
      term
      witness := {
        typeCorrespondence := { inferred }
        contextCorrespondence := contextBridge
        context_eq := rfl
        sourceShape := shape.shape
        constructorCorrespondence := correspondence
        dataTrace := shape.trace
        constantsCorrespond := signatureBridge
        constants_eq := rfl } }
  return none

/-- Existential intrinsic sentence obtained from a closed supported Lean
proposition. The exact finite constant signature and structural witness remain
available after unpacking. -/
inductive ReifiedSentence (expression : Expr) where
  | pack {signature : Signature} (signatureBridge : SignatureBridge signature)
      (datatypes : DataBridge signature)
      (typeExpr : Expr) (source : Sentence signature)
      (witness : ReificationWitness signatureBridge ContextBridge.nil expression
        (.pack (.bool typeExpr) source) (some datatypes)) : ReifiedSentence expression

/-- Reify a closed Lean proposition into the typed HO sentence consumed by the
proved VCG route. Non-formulas and unsupported syntax are rejected. -/
partial def reifySentence? (expression : Expr) :
    MetaM (Option (ReifiedSentence expression)) := do
  match ← reifyDataSignature expression with
  | .error _ => return none
  | .ok (.pack env tail) =>
      let signatureBridge := tail.prepend env.signature
      let datatypes := DataBridge.of env _
      let some reified ← reify? signatureBridge ContextBridge.nil expression
          (some datatypes)
        | return none
      match reified with
      | ⟨.pack (.bool typeExpr) source, witness⟩ =>
          return some (.pack signatureBridge datatypes typeExpr source witness)
      | ⟨.pack (.base _ _) _, _⟩ | ⟨.pack (.arrow _ _ _) _, _⟩ => return none

end Crush.Metatheory.Reification
