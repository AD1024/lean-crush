import Crush.Metatheory.Defunctionalization.Translate
import Crush.Metatheory.FO.Family

/-!
# Total unary reference defunctionalization core

This pass uses unary application symbols.  It is the proof-friendly unary
defunctionalization encoding and currently carries the complete typed
soundness theorem.  The flattened development reuses it as a semantic reference,
but the total flattened transformation and its generated-theory theorem remain
to be constructed.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature} {context : Context} {ty : Ty}

/-- In the unary reference translation, every source constant is a first-class value. -/
@[reducible] def coreSourceDecl (ty : Ty) : FO.SymbolDecl :=
  { args := [], result := FO.FOSort.ofTy ty }

/-- Finite signature used when reifying the unary reference translation encoding. -/
def Plan.coreTargetSignature (sourceSignature : Signature)
    (plan : Plan sourceSignature) : FO.Signature :=
  sourceSignature.map coreSourceDecl ++ plan.unaryAppDecls ++ plan.closureDecls

/-- Generated symbol keys, intrinsically indexed by their FO declarations. -/
inductive CoreSymbol (signature : Signature) : FO.SymbolDecl → Type where
  | source {ty : Ty} : Const signature ty → CoreSymbol signature (coreSourceDecl ty)
  | app (arrow : Arrow) : CoreSymbol signature (unaryAppDecl arrow)
  | closure (closure : Closure signature) :
      CoreSymbol signature
        (FO.closureDecl closure.captureTypes closure.domain closure.codomain)

/-- Translate a list of typed captured variables into constructor arguments. -/
@[reducible] def translateCaptureRefs :
    (captures : List (PackedVar context)) →
      FO.FamilyArgs (CoreSymbol signature) (targetContext context)
        ((captures.map PackedVar.type).map FO.FOSort.ofTy)
  | [] => .nil
  | .pack ref :: captures =>
      .cons (.var (targetVar ref)) (translateCaptureRefs captures)

/-- Captured outer variables referenced underneath the lambda argument binder. -/
@[reducible] def translateCaptureRefsUnder {domain : Ty} :
    (captures : List (PackedVar context)) →
      FO.FamilyArgs (CoreSymbol signature)
        (FO.FOSort.ofTy domain :: targetContext context)
        ((captures.map PackedVar.type).map FO.FOSort.ofTy)
  | [] => .nil
  | .pack ref :: captures =>
      .cons (.var (.there (targetVar ref))) (translateCaptureRefsUnder captures)

/-- Total, intrinsically typed, unary defunctionalization of a source term. -/
def defunctionalizeCore {signature : Signature} {context : Context} :
    {ty : Ty} → Term signature context ty →
    FO.FamilyTerm (CoreSymbol signature) (targetContext context) (FO.FOSort.ofTy ty)
  | _, .var ref => .var (targetVar ref)
  | _, .const ref => .symbol (CoreSymbol.source ref) .nil
  | _, .boolLit value => .boolLit value
  | _, .not body => .not (defunctionalizeCore body)
  | _, .and left right =>
      .and (defunctionalizeCore left) (defunctionalizeCore right)
  | _, .or left right =>
      .or (defunctionalizeCore left) (defunctionalizeCore right)
  | _, .imp left right =>
      .imp (defunctionalizeCore left) (defunctionalizeCore right)
  | _, .iff left right =>
      .iff (defunctionalizeCore left) (defunctionalizeCore right)
  | _, .eq left right =>
      .eq (defunctionalizeCore left) (defunctionalizeCore right)
  | _, .lam (domain := domain) (codomain := codomain) body =>
      let closure := Closure.ofBody body
      .symbol (CoreSymbol.closure closure) (translateCaptureRefs closure.captureRefs)
  | _, .app (domain := domain) (codomain := codomain) fn argument =>
      .symbol (CoreSymbol.app { domain, codomain })
        (.cons (defunctionalizeCore fn)
          (.cons (defunctionalizeCore argument) .nil))
  | _, .forallE body => .forallE (defunctionalizeCore body)
  | _, .existsE body => .existsE (defunctionalizeCore body)

/-- Defining equation for one closure.  All variables from the lambda's original
context are quantified, while the constructor receives only variables that the
body actually captures. -/
def closureEquation (closure : Closure signature) :
    FO.FamilySentence (CoreSymbol signature) :=
  let closureValue :
      FO.FamilyTerm (CoreSymbol signature)
        (FO.FOSort.ofTy closure.domain :: targetContext closure.context)
        (.fn closure.domain closure.codomain) :=
    .symbol (CoreSymbol.closure closure)
      (translateCaptureRefsUnder closure.captureRefs)
  let applied :
      FO.FamilyTerm (CoreSymbol signature)
        (FO.FOSort.ofTy closure.domain :: targetContext closure.context)
        (FO.FOSort.ofTy closure.codomain) :=
    .symbol (CoreSymbol.app { domain := closure.domain, codomain := closure.codomain })
      (.cons closureValue (.cons (.var .here) .nil))
  FO.FamilyFormula.closeForall (.eq applied (defunctionalizeCore closure.body))

/-- All closure equations required by a source term. -/
def closureEquations (term : Term signature context ty) :
    FO.FamilyTheory (CoreSymbol signature) :=
  (closures term).map closureEquation

/-- Complete result of the total unary reference defunctionalization core. -/
structure CoreResult (signature : Signature) (context : Context) (ty : Ty) where
  term : FO.FamilyTerm (CoreSymbol signature)
    (targetContext context) (FO.FOSort.ofTy ty)
  equations : FO.FamilyTheory (CoreSymbol signature)

def defunctionalize (term : Term signature context ty) :
    CoreResult signature context ty :=
  { term := defunctionalizeCore term
    equations := closureEquations term }

@[simp] theorem closureEquations_length (term : Term signature context ty) :
    (closureEquations term).length = (closures term).length := by
  simp [closureEquations]

end Crush.Metatheory.Defunctionalization
