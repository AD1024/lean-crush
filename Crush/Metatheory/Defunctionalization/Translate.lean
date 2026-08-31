import Crush.Metatheory.Defunctionalization.Annotate
import Crush.Metatheory.Defunctionalization.Eta
import Crush.Metatheory.FO.Symbols

/-!
# Typed references for defunctionalization

This module relates the reference translation to the generated target
signature.  It maps source variables, source constants, arrow-plan positions,
and closure IDs to FO references with the declaration type checked by Lean.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature} {context : Context} {ty : Ty}

/-- The total proof-facing preprocessing pipeline.  Target collection happens
*after* eta-long normalization, just as the Crush translator materializes
function values before declaring closures. -/
structure AnnotatedEtaLongTerm (signature : Signature) (context : Context) (ty : Ty) where
  source : Term signature context ty
  normalized : Term signature context ty
  annotated : AnnotatedTerm signature context ty
  annotationErases : annotated.erase = normalized

/-- Eta-normalize and assign stable closure IDs. -/
def prepare (source : Term signature context ty) : AnnotatedEtaLongTerm signature context ty :=
  let normalized := etaLong source
  { source
    normalized
    annotated := annotate normalized
    annotationErases := annotate_erase normalized }

/-- Collection is definitionally tied to the normalized term. -/
def AnnotatedEtaLongTerm.plan (prepared : AnnotatedEtaLongTerm signature context ty) : Plan signature :=
  collect prepared.normalized

/-- The finite target signature selected by a prepared term. -/
def AnnotatedEtaLongTerm.targetSignature (prepared : AnnotatedEtaLongTerm signature context ty) : FO.Signature :=
  prepared.plan.targetSignature signature

@[simp] theorem prepare_normalized (source : Term signature context ty) :
    (prepare source).normalized = etaLong source := rfl

@[simp] theorem prepare_annotation_erase (source : Term signature context ty) :
    (prepare source).annotated.erase = (prepare source).normalized :=
  (prepare source).annotationErases

/-- Erasure of a source local context to target sorts. -/
@[reducible] def targetContext (context : Context) : FO.Context :=
  context.map FO.FOSort.ofTy

/-- Typed source variables become typed target variables. -/
def targetVar {context : Context} {ty : Ty} (ref : Var context ty) :
    FO.Var (targetContext context) (FO.FOSort.ofTy ty) :=
  match ref with
  | .here => .here
  | .there ref => .there (targetVar ref)

/-- Source constants occupy the first mapped segment of every generated target
signature. -/
def sourceSymbol {signature : Signature} {ty : Ty} (generated : FO.Signature) :
    (ref : Const signature ty) →
      FO.Symbol (signature.map sourceDecl ++ generated) (sourceDecl ty)
  | .here => .here
  | .there ref => .there (sourceSymbol generated ref)

/-- The generated declarations following translated source symbols. -/
def Plan.generatedSignature (plan : Plan signature) : FO.Signature :=
  plan.appDecls ++ plan.closureDecls

/-- A collected arrow position selects its unique flattened `app` symbol. -/
def Plan.appSymbol (plan : Plan signature) (index : Fin plan.arrows.length) :
    FO.Symbol (plan.targetSignature signature)
      (FO.appDecl plan.arrows[index].domain plan.arrows[index].codomain) := by
  unfold Plan.targetSignature Plan.appDecls Plan.closureDecls
  exact FO.Symbol.inMappedSegment
    (signature.map sourceDecl)
    (fun arrow => FO.appDecl arrow.domain arrow.codomain)
    (plan.closures.map fun closure =>
      FO.closureDecl closure.captureTypes closure.domain closure.codomain)
    plan.arrows index

/-- A closure ID selects the corresponding generated constructor symbol. -/
def Plan.closureSymbol (plan : Plan signature) (closureId : Fin plan.closures.length) :
    FO.Symbol (plan.targetSignature signature)
      (let closure := plan.closures[closureId]
       FO.closureDecl closure.captureTypes closure.domain closure.codomain) := by
  unfold Plan.targetSignature Plan.appDecls Plan.closureDecls
  simpa only [List.append_nil, List.append_assoc] using
    (FO.Symbol.inMappedSegment
      (signature.map sourceDecl ++
        plan.arrows.map fun arrow => FO.appDecl arrow.domain arrow.codomain)
      (fun closure =>
        FO.closureDecl closure.captureTypes closure.domain closure.codomain)
      [] plan.closures closureId)

@[simp] theorem targetContext_cons (head : Ty) (tail : Context) :
    targetContext (head :: tail) = FO.FOSort.ofTy head :: targetContext tail := rfl

end Crush.Metatheory.Defunctionalization
