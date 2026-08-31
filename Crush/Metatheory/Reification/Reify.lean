import Crush.Metatheory.Reification.Datatype
import Crush.Metatheory.Hooks

/-!
# Executable reification of the modeled Lean fragment

`reifyTerm?` recognizes precisely the constructs represented by the typed
source language. It is intentionally partial at the fragment boundary, but every
successful result is an intrinsically typed `PackedTerm`. Unsupported built-ins,
dependent functions, lets, projections, metavariables, and extension handlers
return `none` and remain on the documented trusted/extension path.

Every successful node is checked against Lean's inferred type. This check and
weak-head normalization are the metaprogramming refinement boundary; all term
construction after it uses the total typed smart constructors in `Term.lean`.
-/

namespace Crush.Metatheory.Reification

open Lean Meta
open Crush.Metatheory.Defunctionalization
open Crush.Metatheory.Datatype

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
      (reifiedSignature : ReifiedSignature signature)
      (reifiedContext : ReifiedContext context) (expression : Expr)
      (datatypes : Option (DatatypeSignaturePrefix signature) := none) :
      MetaM (Option (PackedTerm signature context)) := do
    let result ←
      match expression with
      | .fvar fvar =>
          return (reifiedContext.find? fvar).map PackedTerm.ofVar
      | .const name _ =>
          if name == ``True then return some (PackedTerm.boolLit true)
          if name == ``False then return some (PackedTerm.boolLit false)
          return (reifiedSignature.find? expression).map PackedTerm.ofConst
      | .lam name domain body binderInfo =>
          reifyLambda? reifiedSignature reifiedContext expression name domain body binderInfo
            datatypes
      | .forallE name domain body binderInfo =>
          reifyForallOrImp? reifiedSignature reifiedContext name domain body binderInfo
            datatypes
      | .app .. =>
          reifyApplication? reifiedSignature reifiedContext expression datatypes
      | .mdata _ body => reifyTerm? reifiedSignature reifiedContext body datatypes
      | _ => return none
    let some term := result | return none
    checked? expression term

  partial def reifyLambda? {signature : Signature} {context : Context}
      (reifiedSignature : ReifiedSignature signature)
      (reifiedContext : ReifiedContext context) (lambda : Expr) (name : Name)
      (domain body : Expr) (binderInfo : BinderInfo)
      (datatypes : Option (DatatypeSignaturePrefix signature)) :
      MetaM (Option (PackedTerm signature context)) := do
    let reifiedDomain ← reifyType domain (preserveExpr := true)
    withLocalDecl name binderInfo domain fun localVar => do
      let instantiatedBody := body.instantiate1 localVar
      let bodyType ← inferType instantiatedBody
      if bodyType.containsFVar localVar.fvarId! then return none
      let extended := ReifiedContext.cons localVar.fvarId! reifiedDomain reifiedContext
      let some reifiedBody ← reifyTerm?
          (context := reifiedDomain.ty :: context) reifiedSignature extended instantiatedBody
            datatypes
        | return none
      let arrowType ← inferType lambda
      return some (PackedTerm.lam arrowType reifiedDomain reifiedBody)

  partial def reifyForallOrImp? {signature : Signature} {context : Context}
      (reifiedSignature : ReifiedSignature signature)
      (reifiedContext : ReifiedContext context) (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (datatypes : Option (DatatypeSignaturePrefix signature)) :
      MetaM (Option (PackedTerm signature context)) := do
    let domainType ← whnf (← inferType domain)
    if !body.hasLooseBVars && domainType == .sort .zero then
      let some premise ← reifyTerm? reifiedSignature reifiedContext domain datatypes | return none
      let some conclusion ← reifyTerm? reifiedSignature reifiedContext body datatypes | return none
      return PackedTerm.imp? premise conclusion
    let reifiedDomain ← reifyType domain (preserveExpr := true)
    withLocalDecl name binderInfo domain fun localVar => do
      let extended := ReifiedContext.cons localVar.fvarId! reifiedDomain reifiedContext
      let some reifiedBody ←
          reifyTerm? (context := reifiedDomain.ty :: context)
            reifiedSignature extended (body.instantiate1 localVar) datatypes
        | return none
      return PackedTerm.forallE? reifiedDomain reifiedBody

  partial def reifyApplication? {signature : Signature} {context : Context}
      (reifiedSignature : ReifiedSignature signature)
      (reifiedContext : ReifiedContext context) (expression : Expr)
      (datatypes : Option (DatatypeSignaturePrefix signature)) :
      MetaM (Option (PackedTerm signature context)) := do
    let head := expression.getAppFn
    let arguments := expression.getAppArgs
    let reifyBinary (constructor : PackedTerm signature context →
        PackedTerm signature context → Option (PackedTerm signature context)) := do
      let some leftExpr := arguments[0]? | return none
      let some rightExpr := arguments[1]? | return none
      let some left ← reifyTerm? reifiedSignature reifiedContext leftExpr datatypes | return none
      let some right ← reifyTerm? reifiedSignature reifiedContext rightExpr datatypes | return none
      return constructor left right
    if let some reified := datatypes then
      if let some term ← reifyCtorApp? reifiedSignature reifiedContext expression reified then
        return some term
      if let some term ← reifyProjApp? reifiedSignature reifiedContext expression reified then
        return some term
    if head.isConstOf ``Not && arguments.size == 1 then
      let some body ← reifyTerm? reifiedSignature reifiedContext arguments[0]! datatypes
        | return none
      return PackedTerm.not? body
    if head.isConstOf ``And && arguments.size == 2 then
      return ← reifyBinary PackedTerm.and?
    if head.isConstOf ``Or && arguments.size == 2 then
      return ← reifyBinary PackedTerm.or?
    if head.isConstOf ``Iff && arguments.size == 2 then
      return ← reifyBinary PackedTerm.iff?
    if head.isConstOf ``Eq && arguments.size == 3 then
      let some left ← reifyTerm? reifiedSignature reifiedContext arguments[1]! datatypes
        | return none
      let some right ← reifyTerm? reifiedSignature reifiedContext arguments[2]! datatypes
        | return none
      return PackedTerm.eq? left right
    if head.isConstOf ``Exists && arguments.size == 2 then
      return ← reifyExists? reifiedSignature reifiedContext arguments[0]! arguments[1]!
        datatypes
    match expression with
    | .app fn argument =>
        let some reifiedFn ← reifyTerm? reifiedSignature reifiedContext fn datatypes | return none
        let some reifiedArgument ← reifyTerm? reifiedSignature reifiedContext argument datatypes
          | return none
        return PackedTerm.app? reifiedFn reifiedArgument
    | _ => return none

  /-- Reify a fully applied Lean constructor using its exact block and
  constructor positions. Type parameters select the monomorphic block and are
  erased; only constructor fields become typed applications. -/
  partial def reifyCtorApp? {signature : Signature} {context : Context}
      (reifiedSignature : ReifiedSignature signature)
      (reifiedContext : ReifiedContext context) (expression : Expr)
      (datatypes : DatatypeSignaturePrefix signature) :
      MetaM (Option (PackedTerm signature context)) := do
    let some app ← datatypes.env.ctorApp? expression | return none
    let symbols := datatypes.symbols app.found
    let specialized := mkAppN app.head app.typeArgs
    let type ← reifyType (← inferType specialized) (preserveExpr := true)
    let some packed := PackedTerm.ofTypedConst? type (symbols.ctor app.ctor.ref)
      | return none
    let mut result := packed
    for argument in app.values do
      let some reified ← reifyTerm? reifiedSignature reifiedContext argument
          (some datatypes)
        | return none
      let some applied := PackedTerm.app? result reified | return none
      result := applied
    return some result

  /-- Reify a supported structure projection as the exact selector declared by its
  constructor. Certified datatypes reject function-valued fields, so a valid
  projection has no additional value applications here. -/
  partial def reifyProjApp? {signature : Signature} {context : Context}
      (reifiedSignature : ReifiedSignature signature)
      (reifiedContext : ReifiedContext context) (expression : Expr)
      (datatypes : DatatypeSignaturePrefix signature) :
      MetaM (Option (PackedTerm signature context)) := do
    let some app ← datatypes.env.projApp? expression | return none
    let symbols := datatypes.symbols app.found
    let specialized := mkAppN app.head app.typeArgs
    let type ← reifyType (← inferType specialized) (preserveExpr := true)
    let some packed := PackedTerm.ofTypedConst? type
        (symbols.sel app.ctor.ref app.field.ref)
      | return none
    let some argument ← reifyTerm? reifiedSignature reifiedContext app.target
        (some datatypes)
      | return none
    return PackedTerm.app? packed argument

  partial def reifyExists? {signature : Signature} {context : Context}
      (reifiedSignature : ReifiedSignature signature)
      (reifiedContext : ReifiedContext context) (domain predicate : Expr)
      (datatypes : Option (DatatypeSignaturePrefix signature)) :
      MetaM (Option (PackedTerm signature context)) := do
    let predicate ← whnf predicate
    let .lam name predicateDomain body binderInfo := predicate | return none
    unless ← isDefEqGuarded domain predicateDomain do return none
    let reifiedDomain ← reifyType domain (preserveExpr := true)
    withLocalDecl name binderInfo domain fun localVar => do
      let extended := ReifiedContext.cons localVar.fvarId! reifiedDomain reifiedContext
      let some reifiedBody ←
          reifyTerm? (context := reifiedDomain.ty :: context)
            reifiedSignature extended (body.instantiate1 localVar) datatypes
        | return none
      return PackedTerm.existsE? reifiedDomain reifiedBody

end

/-- An elaborated lambda together with its reified body and an exact certificate that
the Crush translator and the core choose the same ordered closure environment. -/
inductive CertifiedClosure (signature : Signature) (context : Context) where
  | pack {domain codomain : Ty}
      (body : Term signature (domain :: context) codomain)
      (certificate : ClosureCaptureCertificate (Closure.ofBody body)) :
      CertifiedClosure signature context

/-- Reify and certify a closure for a caller-supplied translator eligibility
predicate. This executable check is deliberately proof-producing: success
returns the equality consumed by later declaration/axiom refinement, while a
mismatch leaves the expression on the unverified translator path. -/
partial def certifyClosure? {signature : Signature} {context : Context}
    (reifiedSignature : ReifiedSignature signature)
    (reifiedContext : ReifiedContext context) (eligible : FVarId → Bool)
    (lambda : Expr) : MetaM (Option (CertifiedClosure signature context)) := do
  let some reified ← reifyTerm? reifiedSignature reifiedContext lambda | return none
  match reified with
  | .pack (.arrow _ _ _) (.lam body) =>
      let closure := Closure.ofBody body
      if contextNodup : reifiedContext.fvars.Nodup then
        if capturesEq :
            (selectClosureCaptures lambda eligible).toList =
              closure.captureRefs.map reifiedContext.fvar then
          return some (.pack body {
            lambda
            context := reifiedContext
            eligible
            contextNodup := contextNodup
            captures_eq := capturesEq })
      return none
  | _ => return none

/-- Existential package produced while reconstructing the reified context from
the translator capture order. -/
inductive SomeReifiedContext where
  | pack {context : Context} (reified : ReifiedContext context) : SomeReifiedContext

/-- Reify the translator's actual ordered capture array into a typed context.
The list is consumed from right to left so its head remains de Bruijn position
zero, matching `Closure.captureRefs`. -/
partial def reifyCaptureContext (captures : List FVarId) : MetaM SomeReifiedContext := do
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

/-- Constants from several expressions in deterministic global
first-occurrence order. -/
def collectConstsOrderedMany (expressions : Array Expr) : Array Expr := Id.run do
  let mut constants := #[]
  for expression in expressions do
    for constant in collectConstsOrdered expression do
      unless constants.contains constant do
        constants := constants.push constant
  return constants

def isLogicalConstant : Expr → Bool
  | .const name _ => name == ``True || name == ``False || name == ``Not ||
      name == ``And || name == ``Or || name == ``Iff || name == ``Eq ||
      name == ``Exists
  | _ => false

inductive SomeReifiedSignature where
  | pack {signature : Signature} (reified : ReifiedSignature signature) :
      SomeReifiedSignature

/-- Certified datatype prefix paired with the ordinary expression-indexed
signature tail needed by one Lean term. -/
inductive SomeDataSignature where
  | pack (env : DatatypeEnv) {tail : Signature}
      (reified : ReifiedSignature tail) : SomeDataSignature

/-- Add ground datatype applications from elaborated type and
constructor/projection syntax to a stable occurrence set. This traversal does
not infer the type of loose de Bruijn bodies, so binders remain safe to inspect
before opening them. -/
private partial def collectDatatypeRootsInto (expression : Expr)
    (initial : Array Expr) : MetaM (Array Expr) := do
  let environment ← getEnv
  let push (roots : Array Expr) (root : Expr) :=
    if roots.contains root then roots else roots.push root
  let rec visit (expression : Expr) (roots : Array Expr) : MetaM (Array Expr) := do
    let head := expression.getAppFn
    let arguments := expression.getAppArgs
    let mut roots := roots
    if let .const name _ := head then
      match environment.find? name with
      | some (.inductInfo info) =>
          let dataValued := match info.type.getForallBody with
            | .sort level => !level.isZero
            | _ => false
          if dataValued && arguments.size >= info.numParams then
            roots := push roots (mkAppN head (arguments.extract 0 info.numParams))
      | some (.ctorInfo info) =>
          if arguments.size >= info.numParams then
            let constant ← mkConstWithFreshMVarLevels info.induct
            roots := push roots
              (mkAppN constant (arguments.extract 0 info.numParams))
      | _ =>
          if let some info ← getProjectionFnInfo? name then
            if arguments.size >= info.numParams then
              let constant ← mkConstWithFreshMVarLevels info.ctorName.getPrefix
              roots := push roots
                (mkAppN constant (arguments.extract 0 info.numParams))
    match expression with
    | .app fn argument => visit argument (← visit fn roots)
    | .lam _ type body _ | .forallE _ type body _ =>
        visit body (← visit type roots)
    | .letE _ type value body _ =>
        visit body (← visit value (← visit type roots))
    | .mdata _ body | .proj _ _ body => visit body roots
    | _ => return roots
  visit expression initial

/-- Ground datatype applications in one expression, in first-occurrence
order. -/
partial def collectDatatypeRoots (expression : Expr) : MetaM (Array Expr) :=
  collectDatatypeRootsInto expression #[]

/-- Ground datatype applications shared by several expressions, in global
first-occurrence order. -/
partial def collectDatatypeRootsMany (expressions : Array Expr) :
    MetaM (Array Expr) := do
  let mut roots := #[]
  for expression in expressions do
    roots ← collectDatatypeRootsInto expression roots
  return roots

private def isDatatypeConstant (env : DatatypeEnv) (constant : Expr) : MetaM Bool := do
  let .const name _ := constant | return false
  match (← getEnv).find? name with
  | some (.ctorInfo info) => return env.containsHead info.induct
  | _ =>
      let some info ← getProjectionFnInfo? name | return false
      return env.containsHead info.ctorName.getPrefix

/-- Term forms deliberately outside the first certified datatype fragment.
Recursors need a separate correctness theorem for elimination, while quotient
primitives do not have free-datatype semantics. Their occurrence is checked
before ordinary-constant collection can erase that distinction. -/
private partial def dataTermReject? (env : DatatypeEnv) (expression : Expr) :
    MetaM (Option DatatypeReject) := do
  if let .const name _ := expression.getAppFn then
    let leanEnv ← getEnv
    if Lean.isAuxRecursor leanEnv name && env.containsHead name.getPrefix then
      return some (.recursor name)
    match leanEnv.find? name with
    | some (.recInfo info) =>
        if info.all.any env.containsHead then return some (.recursor name)
    | some (.quotInfo _) => return some (.quotient name)
    | _ => pure ()
  match expression with
  | .app fn argument =>
      if let some reason ← dataTermReject? env fn then return some reason
      dataTermReject? env argument
  | .lam _ type body _ | .forallE _ type body _ =>
      if let some reason ← dataTermReject? env type then return some reason
      dataTermReject? env body
  | .letE _ type value body _ =>
      if let some reason ← dataTermReject? env type then return some reason
      if let some reason ← dataTermReject? env value then return some reason
      dataTermReject? env body
  | .mdata _ body | .proj _ _ body => dataTermReject? env body
  | _ => return none

partial def reifySignature (constants : List Expr) : MetaM SomeReifiedSignature := do
  match constants with
  | [] => return .pack .nil
  | constant :: rest =>
      let .pack tail ← reifySignature rest
      let type ← reifyType (← inferType constant) (preserveExpr := true)
      return .pack (.cons constant type tail)

/-- Construct one certified datatype prefix and ordinary constant tail shared
by several terms. Datatype declarations occur exactly once and are reached only
through their typed symbol references. -/
partial def reifyDataSignatureMany (expressions : Array Expr) :
    MetaM (Except DatatypeReject SomeDataSignature) := do
  let roots ← collectDatatypeRootsMany expressions
  match ← reifyDatatypeEnv roots with
  | .error reason => return .error reason
  | .ok env =>
      for expression in expressions do
        if let some reason ← dataTermReject? env expression then
          return .error reason
      let constants ← (collectConstsOrderedMany expressions).filterM fun constant => do
        if isLogicalConstant constant then return false
        if ← isDatatypeConstant env constant then return false
        return !(← whnf (← inferType constant)).isSort
      let .pack reified ← reifySignature constants.toList
      return .ok (.pack env reified)

/-- Single-expression specialization of the common-signature collector. -/
partial def reifyDataSignature (expression : Expr) :
    MetaM (Except DatatypeReject SomeDataSignature) :=
  reifyDataSignatureMany #[expression]

/-- Construct the finite reified signature needed by the modeled fragment.
Logical constants are core constructors; constants whose type is a universe are
type names represented by `ReifiedType`, not source term constants. -/
partial def reifyTermSignature (expression : Expr) : MetaM SomeReifiedSignature := do
  let constants ← (collectConstsOrdered expression).filterM fun constant => do
    if isLogicalConstant constant then return false
    return !(← whnf (← inferType constant)).isSort
  reifySignature constants.toList

/-- A proof-carrying elaborated closure from the finite modeled fragment.
`context` is retained explicitly so the Crush translator can derive its capture telescope
without unpacking or duplicating the certificate's dependent indices. -/
inductive SomeCertifiedClosure where
  | pack {signature : Signature} {context : Context}
      (reifiedSignature : ReifiedSignature signature)
      (reifiedContext : ReifiedContext context)
      (closure : CertifiedClosure signature context) : SomeCertifiedClosure

instance : TypeName SomeCertifiedClosure := unsafe
  (TypeName.mk _ ``SomeCertifiedClosure)

namespace SomeCertifiedClosure

def captureTypes : SomeCertifiedClosure → Array ReifiedType
  | .pack _ reifiedContext _ => reifiedContext.types.toArray

end SomeCertifiedClosure

/-- Attempt certification directly from the data available in the Crush translator's
`emitClosure`. It supports modeled syntax, SMT-bound locals, and a finite
signature of nondependent uninterpreted constants. Failure is explicit and does
not manufacture a certificate. -/
partial def certifyLocalClosure? (lambda : Expr) (captures : Array FVarId) :
    MetaM (Option SomeCertifiedClosure) := do
  let .pack reifiedContext ← reifyCaptureContext captures.toList
  let .pack reifiedSignature ← reifyTermSignature lambda
  let eligible := fun fvar => captures.contains fvar
  let some closure ← certifyClosure? reifiedSignature reifiedContext eligible lambda
    | return none
  return some (.pack reifiedSignature reifiedContext closure)

/-! ## Identity-bearing elaborated-constant certificates -/

/-- An elaborated Lean constant lookup tied to its exact reified signature position
and the canonical semantic hook certificate for that position. -/
inductive CertifiedConstantLookup where
  | pack {signature : Signature}
      (expression : Expr)
      (reifiedSignature : ReifiedSignature signature)
      (type : ReifiedType)
      (constant : Const signature type.ty)
      (lookup_eq : reifiedSignature.find? expression = some (.pack type constant))
      (semantic : Nonempty (CanonicalConstantHookCertificate constant)) :
      CertifiedConstantLookup

instance : TypeName CertifiedConstantLookup := unsafe
  (TypeName.mk _ ``CertifiedConstantLookup)

/-- Runtime-storable link from an emitted emitted symbol name to the exact
reified constant and its erased canonical semantic proof. -/
structure CertifiedSymbolBinding where
  symbol : String
  constant : CertifiedConstantLookup

instance : TypeName CertifiedSymbolBinding := unsafe
  (TypeName.mk _ ``CertifiedSymbolBinding)

/-- Certify the exact signature position selected for an elaborated constant. Success
cannot attach a theorem about another same-typed constant: the semantic
certificate is indexed by the `Const` reference returned by lookup. -/
def certifyConstantIn? {signature : Signature}
    (reifiedSignature : ReifiedSignature signature) (expression : Expr) :
    Option CertifiedConstantLookup :=
  match equality : reifiedSignature.find? expression with
  | none => none
  | some (.pack type constant) =>
      some (.pack expression reifiedSignature type constant equality
        ⟨CanonicalConstantHookCertificate.canonical constant⟩)

end Crush.Metatheory.Reification
