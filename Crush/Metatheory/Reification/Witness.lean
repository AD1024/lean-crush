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

/-- Erase only certified datatype type parameters before comparing the source
and intrinsic constructor trees. Exact ownership remains in the intrinsically
typed term and its `DataBridge`; a second, unused occurrence trace added no
soundness evidence. -/
partial def eraseData (env : DatatypeEnv) (expression : Expr) :
    MetaM Expr := do
  if let some app ← env.ctorApp? expression then
    let mut erased : Array Expr := #[]
    for argument in app.values do
      erased := erased.push (← eraseData env argument)
    return mkAppN app.head erased
  if let some app ← env.projApp? expression then
    return mkApp app.head (← eraseData env app.target)
  match expression with
  | .app fn argument =>
      return .app (← eraseData env fn) (← eraseData env argument)
  | .lam name type body info =>
      return .lam name type (← eraseData env body) info
  | .forallE name type body info =>
      return .forallE name (← eraseData env type) (← eraseData env body) info
  | .letE name type value body nondep =>
      return .letE name type (← eraseData env value) (← eraseData env body) nondep
  | .mdata data body =>
      return .mdata data (← eraseData env body)
  | .proj name index body =>
      return .proj name index (← eraseData env body)
  | _ => return expression

private partial def sourceShape {signature : Signature} (expression : Expr) :
    Option (DataBridge signature) → MetaM ExprShape
  | none => return exprShape expression
  | some bridge => do
      return exprShape (← eraseData bridge.env expression)

/-- Recursive shape correspondence after erasing only the certified
datatype parameters recorded in the witness. -/
def ShapeCorrespondence {signature : Signature} {context : Context}
    (source : ExprShape) (term : PackedTerm signature context) : Prop :=
  shapesMatch source term.shape = true

/-- Structural witness from one live Lean expression to one intrinsic HO term. -/
structure ReificationWitness {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (expression : Expr)
    (term : PackedTerm signature context)
    (datatypes : Option (DataBridge signature) := none) where
  sourceShape : ExprShape
  shapeCorrespondence : ShapeCorrespondence sourceShape term

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
  let shape ← sourceShape expression datatypes
  if correspondence :
      shapesMatch shape term.shape = true then
    return some {
      term
      witness := {
        sourceShape := shape
        shapeCorrespondence := correspondence } }
  return none

/-- One closed intrinsic sentence reified against an already selected exact
datatype prefix and ordinary signature tail. This is the production-facing
form: its indices prevent a retained fact witness from drifting to a different
datatype environment or constant bridge. -/
structure ReifiedSentenceFor (expression : Expr) (env : DatatypeEnv)
    {tail : Signature} (bridge : SignatureBridge tail) where
  typeExpr : Expr
  source : Sentence (env.signature ++ tail)
  witness : ReificationWitness (bridge.prepend env.signature) ContextBridge.nil
    expression (.pack (.bool typeExpr) source) (some (DataBridge.of env tail))

/-- Reify a closed proposition using an exact datatype/signature selection
already made by production. -/
partial def reifySentenceFor? (expression : Expr) (env : DatatypeEnv)
    {tail : Signature} (bridge : SignatureBridge tail) :
    MetaM (Option (ReifiedSentenceFor expression env bridge)) := do
  let signatureBridge := bridge.prepend env.signature
  let datatypes := DataBridge.of env tail
  let some reified ← reify? signatureBridge ContextBridge.nil expression
      (some datatypes)
    | return none
  match reified with
  | ⟨.pack (.bool typeExpr) source, witness⟩ =>
      return some { typeExpr, source, witness }
  | ⟨.pack (.base _ _) _, _⟩ | ⟨.pack (.arrow _ _ _) _, _⟩ => return none

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
      let some reified ← reifySentenceFor? expression env tail
        | return none
      return some (.pack (tail.prepend env.signature) (DataBridge.of env _)
        reified.typeExpr reified.source reified.witness)

end Crush.Metatheory.Reification
