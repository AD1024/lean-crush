import Crush.Metatheory.Bridge.Term
import Crush.Metatheory.Hooks

/-!
# Executable reification of the modeled Lean fragment

`reifyTerm?` recognizes precisely the constructs represented by the intrinsic
source language. It is intentionally partial at the fragment boundary, but every
successful result is an intrinsically typed `PackedTerm`. Unsupported built-ins,
dependent functions, lets, projections, metavariables, and extension handlers
return `none` and remain on the documented trusted/extension path.

Every successful node is checked against Lean's inferred type. This check and
weak-head normalization are the metaprogramming refinement boundary; all term
construction after it uses the total typed smart constructors in `Term.lean`.
-/

namespace Crush.Metatheory.Bridge

open Lean Meta
open Crush.Metatheory.Defunctionalization

variable {signature : Signature} {context : Context}

private def checked? (expression : Expr)
    (term : PackedTerm signature context) : MetaM (Option (PackedTerm signature context)) := do
  let inferred ← inferType expression
  if ← isDefEqGuarded inferred term.type.expr then
    return some term
  return none

/-! The recursive parser is declared together with its small binder helpers. -/
mutual

  partial def reifyTerm? {signature : Signature} {context : Context}
      (signatureBridge : SignatureBridge signature)
      (contextBridge : ContextBridge context) (expression : Expr) :
      MetaM (Option (PackedTerm signature context)) := do
    let result ←
      match expression with
      | .fvar fvar =>
          return (contextBridge.find? fvar).map PackedTerm.ofVar
      | .const name _ =>
          if name == ``True then return some (PackedTerm.boolLit true)
          if name == ``False then return some (PackedTerm.boolLit false)
          return (signatureBridge.find? expression).map PackedTerm.ofConst
      | .lam name domain body binderInfo =>
          reifyLambda? signatureBridge contextBridge expression name domain body binderInfo
      | .forallE name domain body binderInfo =>
          reifyForallOrImp? signatureBridge contextBridge name domain body binderInfo
      | .app .. =>
          reifyApplication? signatureBridge contextBridge expression
      | .mdata _ body => reifyTerm? signatureBridge contextBridge body
      | _ => return none
    let some term := result | return none
    checked? expression term

  partial def reifyLambda? {signature : Signature} {context : Context}
      (signatureBridge : SignatureBridge signature)
      (contextBridge : ContextBridge context) (lambda : Expr) (name : Name)
      (domain body : Expr) (binderInfo : BinderInfo) :
      MetaM (Option (PackedTerm signature context)) := do
    let domainBridge ← reifyType domain (preserveExpr := true)
    withLocalDecl name binderInfo domain fun localVar => do
      let instantiatedBody := body.instantiate1 localVar
      let bodyType ← inferType instantiatedBody
      if bodyType.containsFVar localVar.fvarId! then return none
      let extended := ContextBridge.cons localVar.fvarId! domainBridge contextBridge
      let some reifiedBody ← reifyTerm?
          (context := domainBridge.ty :: context) signatureBridge extended instantiatedBody
        | return none
      let arrowType ← inferType lambda
      return some (PackedTerm.lam arrowType domainBridge reifiedBody)

  partial def reifyForallOrImp? {signature : Signature} {context : Context}
      (signatureBridge : SignatureBridge signature)
      (contextBridge : ContextBridge context) (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo) : MetaM (Option (PackedTerm signature context)) := do
    let domainType ← whnf (← inferType domain)
    if !body.hasLooseBVars && domainType == .sort .zero then
      let some premise ← reifyTerm? signatureBridge contextBridge domain | return none
      let some conclusion ← reifyTerm? signatureBridge contextBridge body | return none
      return PackedTerm.imp? premise conclusion
    let domainBridge ← reifyType domain (preserveExpr := true)
    withLocalDecl name binderInfo domain fun localVar => do
      let extended := ContextBridge.cons localVar.fvarId! domainBridge contextBridge
      let some reifiedBody ←
          reifyTerm? (context := domainBridge.ty :: context)
            signatureBridge extended (body.instantiate1 localVar)
        | return none
      return PackedTerm.forallE? domainBridge reifiedBody

  partial def reifyApplication? {signature : Signature} {context : Context}
      (signatureBridge : SignatureBridge signature)
      (contextBridge : ContextBridge context) (expression : Expr) :
      MetaM (Option (PackedTerm signature context)) := do
    let head := expression.getAppFn
    let arguments := expression.getAppArgs
    let reifyBinary (constructor : PackedTerm signature context →
        PackedTerm signature context → Option (PackedTerm signature context)) := do
      let some leftExpr := arguments[0]? | return none
      let some rightExpr := arguments[1]? | return none
      let some left ← reifyTerm? signatureBridge contextBridge leftExpr | return none
      let some right ← reifyTerm? signatureBridge contextBridge rightExpr | return none
      return constructor left right
    if head.isConstOf ``Not && arguments.size == 1 then
      let some body ← reifyTerm? signatureBridge contextBridge arguments[0]!
        | return none
      return PackedTerm.not? body
    if head.isConstOf ``And && arguments.size == 2 then
      return ← reifyBinary PackedTerm.and?
    if head.isConstOf ``Or && arguments.size == 2 then
      return ← reifyBinary PackedTerm.or?
    if head.isConstOf ``Iff && arguments.size == 2 then
      return ← reifyBinary PackedTerm.iff?
    if head.isConstOf ``Eq && arguments.size == 3 then
      let some left ← reifyTerm? signatureBridge contextBridge arguments[1]!
        | return none
      let some right ← reifyTerm? signatureBridge contextBridge arguments[2]!
        | return none
      return PackedTerm.eq? left right
    if head.isConstOf ``Exists && arguments.size == 2 then
      return ← reifyExists? signatureBridge contextBridge arguments[0]! arguments[1]!
    match expression with
    | .app fn argument =>
        let some reifiedFn ← reifyTerm? signatureBridge contextBridge fn | return none
        let some reifiedArgument ← reifyTerm? signatureBridge contextBridge argument
          | return none
        return PackedTerm.app? reifiedFn reifiedArgument
    | _ => return none

  partial def reifyExists? {signature : Signature} {context : Context}
      (signatureBridge : SignatureBridge signature)
      (contextBridge : ContextBridge context) (domain predicate : Expr) :
      MetaM (Option (PackedTerm signature context)) := do
    let predicate ← whnf predicate
    let .lam name predicateDomain body binderInfo := predicate | return none
    unless ← isDefEqGuarded domain predicateDomain do return none
    let domainBridge ← reifyType domain (preserveExpr := true)
    withLocalDecl name binderInfo domain fun localVar => do
      let extended := ContextBridge.cons localVar.fvarId! domainBridge contextBridge
      let some reifiedBody ←
          reifyTerm? (context := domainBridge.ty :: context)
            signatureBridge extended (body.instantiate1 localVar)
        | return none
      return PackedTerm.existsE? domainBridge reifiedBody

end

/-- A live lambda together with its intrinsic body and an exact certificate that
production and the core choose the same ordered closure environment. -/
inductive CertifiedClosure (signature : Signature) (context : Context) where
  | pack {domain codomain : Ty}
      (body : Term signature (domain :: context) codomain)
      (certificate : ClosureCaptureCertificate (Closure.ofBody body)) :
      CertifiedClosure signature context

/-- Reify and certify a closure for a caller-supplied production eligibility
predicate. This executable check is deliberately proof-producing: success
returns the equality consumed by later declaration/axiom refinement, while a
mismatch leaves the expression on the unverified translator path. -/
partial def certifyClosure? {signature : Signature} {context : Context}
    (signatureBridge : SignatureBridge signature)
    (contextBridge : ContextBridge context) (eligible : FVarId → Bool)
    (lambda : Expr) : MetaM (Option (CertifiedClosure signature context)) := do
  let some reified ← reifyTerm? signatureBridge contextBridge lambda | return none
  match reified with
  | .pack (.arrow _ _ _) (.lam body) =>
      let closure := Closure.ofBody body
      if contextNodup : contextBridge.fvars.Nodup then
        if capturesEq :
            (selectClosureCaptures lambda eligible).toList =
              closure.captureRefs.map contextBridge.fvar then
          return some (.pack body {
            lambda
            context := contextBridge
            eligible
            contextNodup := contextNodup
            captures_eq := capturesEq })
      return none
  | _ => return none

/-- Existential package produced while reconstructing the intrinsic context from
the live capture order. -/
inductive SomeContextBridge where
  | pack {context : Context} (bridge : ContextBridge context) : SomeContextBridge

/-- Reify the actual ordered production capture array into an intrinsic context.
The list is consumed from right to left so its head remains de Bruijn position
zero, matching `Closure.captureRefs`. -/
partial def reifyCaptureContext (captures : List FVarId) : MetaM SomeContextBridge := do
  match captures with
  | [] => return .pack .nil
  | fvar :: rest =>
      let .pack tail ← reifyCaptureContext rest
      let type ← reifyType (← fvar.getType) (preserveExpr := true)
      return .pack (.cons fvar type tail)

/-- Constants in deterministic first-occurrence order. This deliberately
collects syntactic constants first; the metaprogramming filter below removes
logical constructors and type-level constants handled structurally. -/
def collectConstsOrdered (expression : Expr) : Array Expr :=
  go expression #[]
where
  go (expression : Expr) (accumulator : Array Expr) : Array Expr :=
    match expression with
    | constant@(.const _ _) =>
        if accumulator.contains constant then accumulator else accumulator.push constant
    | .app fn argument => go argument (go fn accumulator)
    | .lam _ type body _ => go body (go type accumulator)
    | .forallE _ type body _ => go body (go type accumulator)
    | .letE _ type value body _ => go body (go value (go type accumulator))
    | .mdata _ body => go body accumulator
    | .proj _ _ body => go body accumulator
    | _ => accumulator

def isLogicalConstant : Expr → Bool
  | .const name _ => name == ``True || name == ``False || name == ``Not ||
      name == ``And || name == ``Or || name == ``Iff || name == ``Eq ||
      name == ``Exists
  | _ => false

inductive SomeSignatureBridge where
  | pack {signature : Signature} (bridge : SignatureBridge signature) :
      SomeSignatureBridge

partial def reifySignature (constants : List Expr) : MetaM SomeSignatureBridge := do
  match constants with
  | [] => return .pack .nil
  | constant :: rest =>
      let .pack tail ← reifySignature rest
      let type ← reifyType (← inferType constant) (preserveExpr := true)
      return .pack (.cons constant type tail)

/-- Construct the finite intrinsic signature needed by the modeled fragment.
Logical constants are core constructors; constants whose type is a universe are
type names represented by `TypeBridge`, not source term constants. -/
partial def reifyTermSignature (expression : Expr) : MetaM SomeSignatureBridge := do
  let constants ← (collectConstsOrdered expression).filterM fun constant => do
    if isLogicalConstant constant then return false
    return !(← whnf (← inferType constant)).isSort
  reifySignature constants.toList

/-- A proof-carrying live closure from the finite modeled fragment.
`context` is retained explicitly so production can derive its capture telescope
without unpacking or duplicating the certificate's dependent indices. -/
inductive LiveCertifiedClosure where
  | pack {signature : Signature} {context : Context}
      (signatureBridge : SignatureBridge signature)
      (contextBridge : ContextBridge context)
      (closure : CertifiedClosure signature context) : LiveCertifiedClosure

instance : TypeName LiveCertifiedClosure := unsafe
  (TypeName.mk _ ``LiveCertifiedClosure)

namespace LiveCertifiedClosure

def captureTypes : LiveCertifiedClosure → Array TypeBridge
  | .pack _ contextBridge _ => contextBridge.types.toArray

end LiveCertifiedClosure

/-- Attempt certification directly from the data available in production's
`emitClosure`. It supports modeled syntax, SMT-bound locals, and a finite
signature of nondependent uninterpreted constants. Failure is explicit and does
not manufacture a certificate. -/
partial def certifyLocalClosure? (lambda : Expr) (captures : Array FVarId) :
    MetaM (Option LiveCertifiedClosure) := do
  let .pack contextBridge ← reifyCaptureContext captures.toList
  let .pack signatureBridge ← reifyTermSignature lambda
  let eligible := fun fvar => captures.contains fvar
  let some closure ← certifyClosure? signatureBridge contextBridge eligible lambda
    | return none
  return some (.pack signatureBridge contextBridge closure)

/-! ## Identity-bearing live constant certificates -/

/-- A live Lean constant lookup tied to its exact intrinsic signature position
and the canonical semantic hook certificate for that position. -/
inductive LiveCertifiedConstant where
  | pack {signature : Signature}
      (expression : Expr)
      (signatureBridge : SignatureBridge signature)
      (type : TypeBridge)
      (constant : Const signature type.ty)
      (lookup_eq : signatureBridge.find? expression = some (.pack type constant))
      (semantic : Nonempty (CanonicalConstantHookCertificate constant)) :
      LiveCertifiedConstant

instance : TypeName LiveCertifiedConstant := unsafe
  (TypeName.mk _ ``LiveCertifiedConstant)

/-- Runtime-storable link from an emitted production symbol name to the exact
reified constant and its erased canonical semantic proof. -/
structure LiveCertifiedConstantEmission where
  symbol : String
  constant : LiveCertifiedConstant

instance : TypeName LiveCertifiedConstantEmission := unsafe
  (TypeName.mk _ ``LiveCertifiedConstantEmission)

/-- Certify the exact signature position selected for a live constant. Success
cannot attach a theorem about another same-typed constant: the semantic
certificate is indexed by the `Const` reference returned by lookup. -/
def certifyConstantIn? {signature : Signature}
    (signatureBridge : SignatureBridge signature) (expression : Expr) :
    Option LiveCertifiedConstant :=
  match equality : signatureBridge.find? expression with
  | none => none
  | some (.pack type constant) =>
      some (.pack expression signatureBridge type constant equality
        ⟨CanonicalConstantHookCertificate.production constant⟩)

end Crush.Metatheory.Bridge
