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

/-- Pure recursive structural view of a reified higher-order term. -/
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

/-- Recursive compatibility of the source and typed constructor trees.
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
and reified constructor trees. Exact datatype-symbol positions remain in the
intrinsically typed term and its `DatatypeSignaturePrefix`; recording the same
constructor occurrences a second time added no soundness evidence. -/
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
    Option (DatatypeSignaturePrefix signature) → MetaM ExprShape
  | none => return exprShape expression
  | some reified => do
      return exprShape (← eraseData reified.env expression)

/-- Recursive shape correspondence after erasing only the certified
datatype parameters recorded in the witness. -/
def ShapeCorrespondence {signature : Signature} {context : Context}
    (source : ExprShape) (term : PackedTerm signature context) : Prop :=
  shapesMatch source term.shape = true

/-- Structural witness from one elaborated Lean expression to one reified higher-order term. -/
structure ReificationWitness {signature : Signature} {context : Context}
    (reifiedSignature : ReifiedSignature signature)
    (reifiedContext : ReifiedContext context) (expression : Expr)
    (term : PackedTerm signature context)
    (datatypes : Option (DatatypeSignaturePrefix signature) := none) where
  sourceShape : ExprShape
  shapeCorrespondence : ShapeCorrespondence sourceShape term

/-- Existential typed result of proof-facing reification. -/
structure Reified {signature : Signature} {context : Context}
    (reifiedSignature : ReifiedSignature signature)
    (reifiedContext : ReifiedContext context) (expression : Expr)
    (datatypes : Option (DatatypeSignaturePrefix signature) := none) where
  term : PackedTerm signature context
  witness : ReificationWitness reifiedSignature reifiedContext expression term datatypes

/-- Proposition-level spelling used by later composition theorems. -/
def Reifies {signature : Signature} {context : Context}
    (reifiedSignature : ReifiedSignature signature)
    (reifiedContext : ReifiedContext context) (expression : Expr)
    (term : PackedTerm signature context)
    (datatypes : Option (DatatypeSignaturePrefix signature) := none) : Prop :=
  Nonempty (ReificationWitness reifiedSignature reifiedContext expression term datatypes)

/-- Run the existing typed reifier and retain its structural witness. -/
partial def reify? {signature : Signature} {context : Context}
    (reifiedSignature : ReifiedSignature signature)
    (reifiedContext : ReifiedContext context) (expression : Expr)
    (datatypes : Option (DatatypeSignaturePrefix signature) := none) :
    MetaM (Option (Reified reifiedSignature reifiedContext expression datatypes)) := do
  let some term ← reifyTerm? reifiedSignature reifiedContext expression datatypes
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

/-- One closed higher-order sentence reified against an already selected exact
datatype prefix and ordinary signature tail. This is the translator-facing
form: its indices prevent a retained fact witness from drifting to a different
datatype environment or constant reification. -/
structure ReifiedSentenceFor (expression : Expr) (env : DatatypeEnv)
    {tail : Signature} (reified : ReifiedSignature tail) where
  typeExpr : Expr
  source : Sentence (env.signature ++ tail)
  witness : ReificationWitness (reified.prepend env.signature) ReifiedContext.nil
    expression (.pack (.bool typeExpr) source) (some (DatatypeSignaturePrefix.of env tail))

/-- Reify a closed proposition using an exact datatype/signature selection
already made by the Crush translator. -/
partial def reifySentenceFor? (expression : Expr) (env : DatatypeEnv)
    {tail : Signature} (reified : ReifiedSignature tail) :
    MetaM (Option (ReifiedSentenceFor expression env reified)) := do
  let reifiedSignature := reified.prepend env.signature
  let datatypes := DatatypeSignaturePrefix.of env tail
  let some reified ← reify? reifiedSignature ReifiedContext.nil expression
      (some datatypes)
    | return none
  match reified with
  | ⟨.pack (.bool typeExpr) source, witness⟩ =>
      return some { typeExpr, source, witness }
  | ⟨.pack (.base _ _) _, _⟩ | ⟨.pack (.arrow _ _ _) _, _⟩ => return none

/-- Exact pointwise reification of an ordered expression list against one
datatype environment and ordinary signature reified. The index records the
source list, so successful construction cannot reorder or omit a fact. -/
inductive ReifiedSentencesFor (env : DatatypeEnv) {tail : Signature}
    (reified : ReifiedSignature tail) : List Expr → Type where
  | nil : ReifiedSentencesFor env reified []
  | cons {expression : Expr} {expressions : List Expr}
      (head : ReifiedSentenceFor expression env reified)
      (tail : ReifiedSentencesFor env reified expressions) :
      ReifiedSentencesFor env reified (expression :: expressions)

namespace ReifiedSentencesFor

/-- Reified higher-order theory retained by an exact ordered reification witness. -/
def sources {env : DatatypeEnv} {tail : Signature}
    {reified : ReifiedSignature tail} : {expressions : List Expr} →
    ReifiedSentencesFor env reified expressions →
      Theory (env.signature ++ tail)
  | [], .nil => []
  | _ :: _, .cons head rest => head.source :: sources rest

end ReifiedSentencesFor

/-- Reify an exact expression list against an already selected common
datatype/signature environment. -/
partial def reifySentencesFor? (env : DatatypeEnv) {tail : Signature}
    (reified : ReifiedSignature tail) : (expressions : List Expr) →
    MetaM (Option (ReifiedSentencesFor env reified expressions))
  | [] => return some .nil
  | expression :: rest => do
      let some head ← reifySentenceFor? expression env reified | return none
      let some tail ← reifySentencesFor? env reified rest | return none
      return some (.cons head tail)

/-- Existential common environment and exact pointwise witness for a finite
array of closed Lean propositions. -/
inductive ReifiedTheory (expressions : Array Expr) where
  | pack (env : DatatypeEnv) {tail : Signature}
      (reified : ReifiedSignature tail)
      (sentences : ReifiedSentencesFor env reified expressions.toList) :
      ReifiedTheory expressions

/-- Reify several closed propositions into one reified higher-order theory. All terms
share the datatype prefix and ordinary constant signature selected from the
entire input array. -/
partial def reifyTheory? (expressions : Array Expr) :
    MetaM (Option (ReifiedTheory expressions)) := do
  match ← reifyDataSignatureMany expressions with
  | .error _ => return none
  | .ok (.pack env reified) =>
      let some sentences ← reifySentencesFor? env reified expressions.toList
        | return none
      return some (.pack env reified sentences)

/-- Existential reified higher-order sentence obtained from a closed supported Lean
proposition. The exact finite constant signature and structural witness remain
available after unpacking. -/
inductive ReifiedSentence (expression : Expr) where
  | pack {signature : Signature} (reifiedSignature : ReifiedSignature signature)
      (datatypes : DatatypeSignaturePrefix signature)
      (typeExpr : Expr) (source : Sentence signature)
      (witness : ReificationWitness reifiedSignature ReifiedContext.nil expression
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
      return some (.pack (tail.prepend env.signature) (DatatypeSignaturePrefix.of env _)
        reified.typeExpr reified.source reified.witness)

end Crush.Metatheory.Reification
