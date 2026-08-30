import Crush.Metatheory.Defunctionalization.Flattened.Lambda
import Crush.Metatheory.Defunctionalization.ProductionClosure

/-!
# Total flattened intrinsic translation

This is the mathematical flattened transformation.  It is total over every
constructor of the intrinsically typed HO language and returns both the FO term
and all recursively generated output.

The recursion has three modes.  Ordinary term translation may hand the same
function-valued syntax to spine translation; lambda-body translation may do the
same for a residual non-lambda function.  A numeric mode tag below the structural
term size makes those handoffs well founded without `partial` definitions.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

variable {signature : Signature}

/-- Constructor count independent of intrinsic context and type indices.  This
is the structural measure used by the mutually recursive translator modes. -/
def termSize {context : Context} {ty : Ty} :
    Term signature context ty → Nat
  | .var _ | .const _ | .boolLit _ => 1
  | .not body => termSize body + 1
  | .and left right | .or left right | .imp left right | .iff left right |
      .eq left right | .app left right =>
      termSize left + termSize right + 1
  | .lam body | .forallE body | .existsE body => termSize body + 1

/-- A complete-spine head is either an FO function value or a source constant
whose flattened declaration consumes the arguments directly. -/
inductive FunctionHead (signature : Signature) (context : Context) :
    Ty → Ty → Type 1 where
  | value {domain codomain : Ty}
      (term : TargetTerm signature context (.arrow domain codomain)) :
      FunctionHead signature context domain codomain
  | sourceConstant {domain codomain : Ty}
      (constant : Const signature (.arrow domain codomain)) :
      FunctionHead signature context domain codomain

namespace FunctionHead

def weaken {context : Context} {domain codomain binder : Ty}
    (head : FunctionHead signature context domain codomain) :
    FunctionHead signature (binder :: context) domain codomain :=
  match head with
  | .value term => .value (term.weaken (domain := FO.FOSort.ofTy binder))
  | .sourceConstant constant => .sourceConstant constant

end FunctionHead

/-- A translated application prefix ending at `result`.  The existential head
arrow records the unique flattened symbol selected when the spine is completed. -/
structure SpineResult (signature : Signature) (context : Context) (result : Ty) where
  headDomain : Ty
  headCodomain : Ty
  head : FunctionHead signature context headDomain headCodomain
  arguments : TargetArguments signature context
    (.arrow headDomain headCodomain) result
  generated : GeneratedOutput signature := {}

namespace SpineResult

def weaken {context : Context} {result binder : Ty}
    (spine : SpineResult signature context result) :
    SpineResult signature (binder :: context) result where
  headDomain := spine.headDomain
  headCodomain := spine.headCodomain
  head := spine.head.weaken (binder := binder)
  arguments := spine.arguments.weaken (domain := binder)
  generated := spine.generated

def snoc {context : Context} {domain codomain : Ty}
    (spine : SpineResult signature context (.arrow domain codomain))
    (argument : TargetTerm signature context domain)
    (generated : GeneratedOutput signature := {}) :
    SpineResult signature context codomain where
  headDomain := spine.headDomain
  headCodomain := spine.headCodomain
  head := spine.head
  arguments := .snoc spine.arguments argument
  generated := spine.generated.append generated

/-- Finish a complete ground spine, choosing direct source-symbol application or
the generated flattened application symbol according to its head. -/
def finish {context : Context} {result : Ty}
    (spine : SpineResult signature context result)
    (ground : GroundResult result) :
    TranslationResult signature context result :=
  match spine.head with
  | .value term =>
      TranslationResult.ofGenerated
        (spine.arguments.completeApplication term ground)
        (spine.generated.declare
          (.of (Symbol.application
            { domain := spine.headDomain, codomain := spine.headCodomain })))
  | .sourceConstant constant =>
      TranslationResult.ofGenerated
        (spine.arguments.sourceApplication constant ground)
        (spine.generated.declare
          (.of (Symbol.sourceConstant constant)))

end SpineResult

/-- A closed closure equation plus all output generated while translating its
right-hand side. -/
structure EquationResult (signature : Signature) where
  equation : TargetSentence signature
  generated : GeneratedOutput signature := {}

/-- Saturate a residual translated function spine with fresh variables and make
it the right-hand side of a closure equation. -/
def saturateEquation {context : Context}
    {closureDomain closureCodomain current : Ty}
    (closureHead : TargetTerm signature context
      (.arrow closureDomain closureCodomain))
    (closureArguments : TargetArguments signature context
      (.arrow closureDomain closureCodomain) current)
    (right : SpineResult signature context current) :
    EquationResult signature :=
  match current with
  | .bool =>
      let translatedRight := right.finish GroundResult.bool
      { equation := FO.FamilyFormula.closeForall
          (.eq
            (closureArguments.completeApplication closureHead .bool)
            translatedRight.term)
        generated := translatedRight.generated }
  | .base sort =>
      let translatedRight := right.finish (GroundResult.base sort)
      { equation := FO.FamilyFormula.closeForall
          (.eq
            (closureArguments.completeApplication closureHead (.base sort))
            translatedRight.term)
        generated := translatedRight.generated }
  | .arrow domain codomain =>
      let weakenedHead : TargetTerm signature (domain :: context)
          (.arrow closureDomain closureCodomain) :=
        closureHead.weaken (domain := FO.FOSort.ofTy domain)
      let weakenedArguments : TargetArguments signature (domain :: context)
          (.arrow closureDomain closureCodomain) codomain :=
        .snoc (closureArguments.weaken (domain := domain)) (.var .here)
      let weakenedRight : SpineResult signature (domain :: context) codomain :=
        (right.weaken (binder := domain)).snoc (.var .here)
      saturateEquation weakenedHead weakenedArguments weakenedRight
termination_by sizeOf current

/-- Pointwise equality of two function values, universally quantified over the
complete flattened argument telescope. -/
def pointwiseEquality {context : Context}
    {functionDomain functionCodomain current : Ty}
    (leftHead rightHead : TargetTerm signature context
      (.arrow functionDomain functionCodomain))
    (leftArguments rightArguments : TargetArguments signature context
      (.arrow functionDomain functionCodomain) current) :
    TargetFormula signature context :=
  match current with
  | .bool =>
      .eq
        (leftArguments.completeApplication leftHead .bool)
        (rightArguments.completeApplication rightHead .bool)
  | .base sort =>
      .eq
        (leftArguments.completeApplication leftHead (.base sort))
        (rightArguments.completeApplication rightHead (.base sort))
  | .arrow domain codomain =>
      let weakenedLeft : TargetTerm signature (domain :: context)
          (.arrow functionDomain functionCodomain) :=
        leftHead.weaken (domain := FO.FOSort.ofTy domain)
      let weakenedRight : TargetTerm signature (domain :: context)
          (.arrow functionDomain functionCodomain) :=
        rightHead.weaken (domain := FO.FOSort.ofTy domain)
      let leftArguments' : TargetArguments signature (domain :: context)
          (.arrow functionDomain functionCodomain) codomain :=
        .snoc (leftArguments.weaken (domain := domain)) (.var .here)
      let rightArguments' : TargetArguments signature (domain :: context)
          (.arrow functionDomain functionCodomain) codomain :=
        .snoc (rightArguments.weaken (domain := domain)) (.var .here)
      .forallE (pointwiseEquality weakenedLeft weakenedRight
        leftArguments' rightArguments')
termination_by sizeOf current

/-- Extensionality for one complete source arrow sort.  Only function equality
requests this formula; ordinary function application does not. -/
def extensionalityFormula (domain codomain : Ty) :
    TargetSentence signature :=
  let functionContext : Context := [.arrow domain codomain, .arrow domain codomain]
  let left : TargetTerm signature functionContext (.arrow domain codomain) :=
    .var (.there .here)
  let right : TargetTerm signature functionContext (.arrow domain codomain) :=
    .var .here
  let pointwise := pointwiseEquality left right
    (TargetArguments.nil (.arrow domain codomain))
    (TargetArguments.nil (.arrow domain codomain))
  FO.FamilyFormula.closeForall (.imp pointwise (.eq left right))

/-- Append one closure's declarations and defining equation around the output
generated by its translated body. -/
def finishClosure {context : Context} {domain codomain : Ty}
    (closure : Closure signature)
    (context_eq : closure.context = context)
    (domain_eq : closure.domain = domain)
    (codomain_eq : closure.codomain = codomain)
    (closureTerm : TargetTerm signature context (.arrow domain codomain))
    (equation : EquationResult signature) :
    TranslationResult signature context (.arrow domain codomain) := by
  subst context_eq
  subst domain_eq
  subst codomain_eq
  let declarations :=
    (GeneratedOutput.empty (signature := signature))
      |>.declare (.of (Symbol.application
        { domain := closure.domain, codomain := closure.codomain }))
      |>.declare (.of (Symbol.closure closure))
  let generated := declarations.append equation.generated
  exact TranslationResult.ofGenerated closureTerm
    { generated with equations := generated.equations ++ [equation.equation] }

mutual
  /-- Translate a source term through an arbitrary typed source-context renaming. -/
  def translateWith {source target : Context}
      (r : Renaming source target) : {ty : Ty} →
      Term signature source ty → TranslationResult signature target ty
    | ty, .var ref =>
        match ty with
        | .bool => TranslationResult.ofGenerated (.var (targetVar (r ref)))
        | .base _ => TranslationResult.ofGenerated (.var (targetVar (r ref)))
        | .arrow domain codomain =>
            let renamed : Term signature target (.arrow domain codomain) :=
              .var (r ref)
            let closure : Closure signature :=
              Closure.ofBody (LambdaBody.etaBody renamed)
            let closureTerm : TargetTerm signature target (.arrow domain codomain) :=
              .symbol (Symbol.closure closure) (captureArgs closure.captureRefs)
            let right := translateSpineWith r (.var ref)
            finishClosure closure rfl rfl rfl closureTerm
              (saturateEquation closureTerm (.nil _) right)

    | ty, .const constant =>
        match ty with
        | .bool =>
            TranslationResult.ofGenerated
              ((TargetArguments.nil .bool).sourceApplication constant .bool)
              ((GeneratedOutput.empty (signature := signature)).declare
                (.of (Symbol.sourceConstant constant)))
        | .base sort =>
            TranslationResult.ofGenerated
              ((TargetArguments.nil (.base sort)).sourceApplication constant (.base sort))
              ((GeneratedOutput.empty (signature := signature)).declare
                (.of (Symbol.sourceConstant constant)))
        | .arrow domain codomain =>
            let renamed : Term signature target (.arrow domain codomain) :=
              .const constant
            let closure : Closure signature :=
              Closure.ofBody (LambdaBody.etaBody renamed)
            let closureTerm : TargetTerm signature target (.arrow domain codomain) :=
              .symbol (Symbol.closure closure) (captureArgs closure.captureRefs)
            let right := translateSpineWith r (.const constant)
            finishClosure closure rfl rfl rfl closureTerm
              (saturateEquation closureTerm (.nil _) right)

    | _, .boolLit value => TranslationResult.ofGenerated (.boolLit value)
    | _, .not body =>
        let translated := translateWith r body
        translated.replaceTerm (.not translated.term)
    | _, .and left right =>
        let translatedLeft := translateWith r left
        let translatedRight := translateWith r right
        translatedLeft.combine translatedRight
          (.and translatedLeft.term translatedRight.term)
    | _, .or left right =>
        let translatedLeft := translateWith r left
        let translatedRight := translateWith r right
        translatedLeft.combine translatedRight
          (.or translatedLeft.term translatedRight.term)
    | _, .imp left right =>
        let translatedLeft := translateWith r left
        let translatedRight := translateWith r right
        translatedLeft.combine translatedRight
          (.imp translatedLeft.term translatedRight.term)
    | _, .iff left right =>
        let translatedLeft := translateWith r left
        let translatedRight := translateWith r right
        translatedLeft.combine translatedRight
          (.iff translatedLeft.term translatedRight.term)
    | _, .eq (ty := operandType) left right =>
        let translatedLeft := translateWith r left
        let translatedRight := translateWith r right
        let combined : TranslationResult signature target .bool :=
          translatedLeft.combine translatedRight
            (.eq translatedLeft.term translatedRight.term)
        match operandType with
        | .arrow domain codomain =>
            combined.appendOutput
              (extensionality := [extensionalityFormula domain codomain])
        | .bool | .base _ => combined
    | _, .lam (domain := domain) (codomain := codomain) body =>
        let renamedBody := body.rename (Renaming.lift r)
        let closure : Closure signature :=
          Closure.ofBody (LambdaBody.etaBody (.lam renamedBody))
        let closureTerm : TargetTerm signature target (.arrow domain codomain) :=
          .symbol (Symbol.closure closure) (captureArgs closure.captureRefs)
        let weakenedHead :=
          closureTerm.weaken (domain := FO.FOSort.ofTy domain)
        let openedArguments : TargetArguments signature (domain :: target)
            (.arrow domain codomain) codomain :=
          .snoc ((TargetArguments.nil (.arrow domain codomain)).weaken
            (domain := domain)) (.var .here)
        let equation := translateLambdaBodyWith (Renaming.lift r) body
          weakenedHead openedArguments
        finishClosure closure rfl rfl rfl closureTerm equation
    | _, .app (domain := domain) (codomain := codomain) fn argument =>
        match codomain with
        | .bool =>
            let spine := translateSpineWith r fn
            let translatedArgument := translateWith r argument
            (spine.snoc translatedArgument.term translatedArgument.generated).finish .bool
        | .base sort =>
            let spine := translateSpineWith r fn
            let translatedArgument := translateWith r argument
            (spine.snoc translatedArgument.term translatedArgument.generated).finish
              (.base sort)
        | .arrow residualDomain residualCodomain =>
            let renamed : Term signature target
                (.arrow residualDomain residualCodomain) :=
              .app (fn.rename r) (argument.rename r)
            let closure : Closure signature :=
              Closure.ofBody (LambdaBody.etaBody renamed)
            let closureTerm : TargetTerm signature target
                (.arrow residualDomain residualCodomain) :=
              .symbol (Symbol.closure closure) (captureArgs closure.captureRefs)
            let right := translateSpineWith r (.app fn argument)
            finishClosure closure rfl rfl rfl closureTerm
              (saturateEquation closureTerm (.nil _) right)
    | _, .forallE (domain := domain) body =>
        let translated := translateWith (Renaming.lift r) body
        TranslationResult.ofGenerated (.forallE translated.term)
          translated.generated
    | _, .existsE (domain := domain) body =>
        let translated := translateWith (Renaming.lift r) body
        TranslationResult.ofGenerated (.existsE translated.term)
          translated.generated
  termination_by ty term => 4 * termSize term + 2
  decreasing_by all_goals simp_wf <;> simp [termSize] <;> omega

  /-- Collect and translate the entire application prefix of a function term. -/
  def translateSpineWith {source target : Context}
      (r : Renaming source target) : {domain codomain : Ty} →
      Term signature source (.arrow domain codomain) →
        SpineResult signature target (.arrow domain codomain)
    | domain, codomain, .var ref =>
        { headDomain := domain
          headCodomain := codomain
          head := .value (.var (targetVar (r ref)))
          arguments := .nil _ }
    | domain, codomain, .const constant =>
        { headDomain := domain
          headCodomain := codomain
          head := .sourceConstant constant
          arguments := .nil _ }
    | domain, codomain, .lam body =>
        let renamedBody := body.rename (Renaming.lift r)
        let closure : Closure signature :=
          Closure.ofBody (LambdaBody.etaBody (.lam renamedBody))
        let closureTerm : TargetTerm signature target (.arrow domain codomain) :=
          .symbol (Symbol.closure closure) (captureArgs closure.captureRefs)
        let weakenedHead :=
          closureTerm.weaken (domain := FO.FOSort.ofTy domain)
        let openedArguments : TargetArguments signature (domain :: target)
            (.arrow domain codomain) codomain :=
          .snoc ((TargetArguments.nil (.arrow domain codomain)).weaken
            (domain := domain)) (.var .here)
        let equation := translateLambdaBodyWith (Renaming.lift r) body
          weakenedHead openedArguments
        let translated := finishClosure closure rfl rfl rfl closureTerm equation
        { headDomain := domain
          headCodomain := codomain
          head := .value translated.term
          arguments := .nil _
          generated := translated.generated }
    | domain, codomain, .app fn argument =>
        let spine := translateSpineWith r fn
        let translatedArgument := translateWith r argument
        spine.snoc translatedArgument.term translatedArgument.generated
  termination_by domain codomain term => 4 * termSize term + 1
  decreasing_by all_goals simp_wf <;> simp [termSize] <;> omega

  /-- Translate the terminal body of one flattened lambda closure, opening
  existing nested lambdas without allocating intermediate closures. -/
  def translateLambdaBodyWith {source target : Context}
      (r : Renaming source target)
      {closureDomain closureCodomain current : Ty}
      (term : Term signature source current)
      (closureHead : TargetTerm signature target
        (.arrow closureDomain closureCodomain))
      (closureArguments : TargetArguments signature target
        (.arrow closureDomain closureCodomain) current) :
      EquationResult signature :=
    match current with
    | .bool =>
        let translated := translateWith r term
        { equation := FO.FamilyFormula.closeForall
            (.eq
              (closureArguments.completeApplication closureHead .bool)
              translated.term)
          generated := translated.generated }
    | .base sort =>
        let translated := translateWith r term
        { equation := FO.FamilyFormula.closeForall
            (.eq
              (closureArguments.completeApplication closureHead (.base sort))
              translated.term)
          generated := translated.generated }
    | .arrow domain codomain =>
        match term with
        | .lam body =>
            translateLambdaBodyWith (Renaming.lift r) body
              (closureHead.weaken (domain := FO.FOSort.ofTy domain))
              (.snoc (closureArguments.weaken (domain := domain)) (.var .here))
        | .var ref =>
            saturateEquation closureHead closureArguments
              (translateSpineWith r (.var ref))
        | .const constant =>
            saturateEquation closureHead closureArguments
              (translateSpineWith r (.const constant))
        | .app fn argument =>
            saturateEquation closureHead closureArguments
              (translateSpineWith r (.app fn argument))
  termination_by 4 * termSize term + 3
  decreasing_by all_goals simp_wf <;> simp [termSize] <;> omega
end

/-- Total flattened translation of an intrinsically typed HO term. -/
def translate {context : Context} {ty : Ty}
    (term : Term signature context ty) :
    TranslationResult signature context ty :=
  translateWith Renaming.id term

end Crush.Metatheory.Defunctionalization.Flattened

namespace Crush.Metatheory

/-- `𝓕⟦e⟧` is the result of total flattened defunctionalization of `e`. -/
scoped notation:max "𝓕⟦" term "⟧" =>
  Defunctionalization.Flattened.translate term

end Crush.Metatheory
