import Crush.Metatheory.Defunctionalization.TermTranslation
import Crush.Metatheory.FO.Renaming

/-!
# Typed application spines

An application spine records the non-application head together with its arguments
in source order.  The indices state exactly how each argument consumes one arrow.
For a Boolean or base result, the argument types are therefore definitionally the
complete leading telescope of the head type.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

variable {signature : Signature} {context : Context}
variable {start result domain codomain : Ty}

/-- Arguments that turn a value of `start` into a value of `result`. -/
inductive AppliedArguments (signature : Signature) (context : Context) : Ty → Ty → Type where
  | nil (ty : Ty) : AppliedArguments signature context ty ty
  | snoc {start domain codomain : Ty}
      (previous : AppliedArguments signature context start (.arrow domain codomain))
      (argument : Term signature context domain) :
      AppliedArguments signature context start codomain

namespace AppliedArguments

/-- Source types of arguments in application order. -/
  def types : {start result : Ty} →
    AppliedArguments signature context start result → List Ty
  | _, _, .nil _ => []
  | _, _, .snoc (domain := domain) previous _ => previous.types ++ [domain]

/-- Rebuild the left-associated application represented by the argument spine. -/
  def applyTerm : {start result : Ty} →
    AppliedArguments signature context start result →
      Term signature context start → Term signature context result
  | _, _, .nil _, head => head
  | _, _, .snoc previous argument, head => .app (previous.applyTerm head) argument

@[simp] theorem applyTerm_snoc
    (previous : AppliedArguments signature context start (.arrow domain codomain))
    (argument : Term signature context domain)
    (head : Term signature context start) :
    (AppliedArguments.snoc previous argument).applyTerm head =
      .app (previous.applyTerm head) argument := by
  simp [applyTerm]

@[simp] theorem types_snoc
    (previous : AppliedArguments signature context start (.arrow domain codomain))
    (argument : Term signature context domain) :
    (AppliedArguments.snoc previous argument).types = previous.types ++ [domain] := by
  simp [types]

end AppliedArguments

/-- Computational evidence that a type is a non-function result sort.  This
lives in `Type` because the total translator uses it to construct a typed FO
argument vector, not merely to prove a proposition. -/
inductive GroundResult : Ty → Type where
  | bool : GroundResult .bool
  | base (sort : BaseSort) : GroundResult (.base sort)

/-! ## Target argument spines -/

/-- Translated target arguments indexed by the source type before and after
their application.  This is the binder-building counterpart of
`AppliedArguments`: its terms can be weakened while a closure equation opens
the remaining lambda telescope. -/
inductive TargetArguments (signature : Signature) (context : Context) :
    Ty → Ty → Type 1 where
  | nil (ty : Ty) : TargetArguments signature context ty ty
  | cons {domain codomain result : Ty}
      (argument : TargetTerm signature context domain)
      (rest : TargetArguments signature context codomain result) :
      TargetArguments signature context (.arrow domain codomain) result

namespace TargetArguments

/-- Append one final target argument while preserving application order. -/
def snoc : {start domain codomain : Ty} →
    TargetArguments signature context start (.arrow domain codomain) →
    TargetTerm signature context domain →
    TargetArguments signature context start codomain
  | _, _, _, .nil _, argument => .cons argument (.nil _)
  | _, _, _, .cons first rest, argument => .cons first (rest.snoc argument)

/-- Source types of translated arguments in application order. -/
def types : {start result : Ty} →
    TargetArguments signature context start result → List Ty
  | _, _, .nil _ => []
  | _, _, .cons (domain := domain) _ rest => domain :: rest.types

/-- Forget the source application indices and retain the FO argument telescope. -/
def toFamilyArgs : {start result : Ty} →
    (arguments : TargetArguments signature context start result) →
      FO.FamilyArgs (Symbol signature) (targetContext context)
        (arguments.types.map FO.FOSort.ofTy)
  | _, _, .nil _ => by
      simpa [types] using
        (.nil : FO.FamilyArgs (Symbol signature) (targetContext context) [])
  | _, _, .cons argument rest =>
      .cons argument rest.toFamilyArgs

/-- Rename every translated argument into another erased source context. -/
def rename {sourceContext targetContext' : Context}
    (r : FO.FamilyRenaming (targetContext sourceContext)
      (targetContext targetContext')) :
    {start result : Ty} →
      TargetArguments signature sourceContext start result →
        TargetArguments signature targetContext' start result
  | _, _, .nil ty => .nil ty
  | _, _, .cons argument rest =>
      .cons (argument.rename r) (rest.rename r)

/-- Move translated arguments beneath one fresh source binder. -/
def weaken {start result : Ty}
    (arguments : TargetArguments signature context start result) :
    TargetArguments signature (domain :: context) start result :=
  arguments.rename (FO.FamilyRenaming.weaken (domain := FO.FOSort.ofTy domain))

/-- Target argument indices decompose the same flattened arrow telescope as
their source-side counterparts. -/
theorem flattenArrow_eq
    {start result : Ty}
    (arguments : TargetArguments signature context start result) :
    (FO.flattenArrow start).1 =
        arguments.types ++ (FO.flattenArrow result).1 ∧
      (FO.flattenArrow start).2 = (FO.flattenArrow result).2 := by
  induction arguments with
  | nil => simp [TargetArguments.types]
  | cons argument rest inductionHypothesis =>
      constructor
      · simp only [TargetArguments.types,
          List.cons_append, List.cons.injEq]
        grind
      · exact inductionHypothesis.2

theorem types_eq_flattenArrow
    {start result : Ty}
    (arguments : TargetArguments signature context start result)
    (ground : GroundResult result) :
    arguments.types = (FO.flattenArrow start).1 := by
  have shape := (flattenArrow_eq arguments).1
  cases ground <;> simpa using shape.symm

theorem result_eq_flattenArrow
    {start result : Ty}
    (arguments : TargetArguments signature context start result)
    (ground : GroundResult result) :
    result = (FO.flattenArrow start).2 := by
  have shape := (flattenArrow_eq arguments).2
  cases ground <;> simpa using shape.symm

/-- Forget the source before/after indices of a complete spine without an
equality cast.  Ground-result evidence makes structural recursion expose exactly
the full flattened argument telescope. -/
def completeFamilyArgs : {start result : Ty} →
    (arguments : TargetArguments signature context start result) →
    GroundResult result →
    FO.FamilyArgs (Symbol signature) (targetContext context)
      ((FO.flattenArrow start).1.map FO.FOSort.ofTy)
  | _, _, .nil _, .bool => .nil
  | _, _, .nil _, .base _ => .nil
  | _, _, .cons argument rest, ground =>
      .cons argument (rest.completeFamilyArgs ground)

/-- Apply a flattened source constant to a complete argument telescope.  This
also covers a nullary Boolean or base constant. -/
def sourceApplication {start result : Ty}
    (constant : Const signature start)
    (arguments : TargetArguments signature context start result)
    (ground : GroundResult result) :
    TargetTerm signature context result := by
  have resultType := arguments.result_eq_flattenArrow ground
  have translatedArguments :
      FO.FamilyArgs (Symbol signature) (targetContext context)
        ((FO.flattenArrow start).1.map FO.FOSort.ofTy) :=
    arguments.completeFamilyArgs ground
  have application : TargetTerm signature context (FO.flattenArrow start).2 :=
    .symbol (Symbol.sourceConstant constant) translatedArguments
  exact application.castSort
    (congrArg FO.FOSort.ofTy resultType.symm)

/-- Emit the single flattened application selected by a complete target spine.
The ground-result evidence rules out under-applying the n-ary symbol. -/
def completeApplication {domain codomain result : Ty}
    (head : TargetTerm signature context (.arrow domain codomain))
    (arguments : TargetArguments signature context
      (.arrow domain codomain) result)
    (ground : GroundResult result) :
    TargetTerm signature context result := by
  have resultType := arguments.result_eq_flattenArrow ground
  have translatedArguments :
      FO.FamilyArgs (Symbol signature) (targetContext context)
        ((FO.flattenArrow (.arrow domain codomain)).1.map FO.FOSort.ofTy) :=
    arguments.completeFamilyArgs ground
  have application : TargetTerm signature context
      (FO.flattenArrow (.arrow domain codomain)).2 :=
    .symbol (Symbol.application { domain, codomain })
      (.cons head translatedArguments)
  exact application.castSort
    (congrArg FO.FOSort.ofTy resultType.symm)

end TargetArguments

/-! ## Translation of heterogeneous argument telescopes -/

/-- Translated FO arguments and the recursively generated output accumulated
while translating them. -/
structure ArgumentsResult (signature : Signature) (context : Context)
    (types : List Ty) where
  terms : FO.FamilyArgs (Symbol signature) (targetContext context)
    (types.map FO.FOSort.ofTy)
  generated : AuxiliaryTheory signature := {}

namespace AppliedArguments

/-- Translate every source argument in order and compose all recursive output.
The caller supplies the term translator, so this telescope fold can be reused by
the total translation without introducing a separate correctness assumption. -/
def translate
    (translateTerm : {ty : Ty} → Term signature context ty →
      TermTranslation signature context ty) :
    {start result : Ty} →
      (arguments : AppliedArguments signature context start result) →
        ArgumentsResult signature context arguments.types
  | _, _, .nil _ =>
      { terms := by simpa [types] using
          (.nil : FO.FamilyArgs (Symbol signature) (targetContext context) [])
        generated := .empty }
  | _, _, .snoc previous argument =>
      let translatedPrevious := previous.translate translateTerm
      let translatedArgument := translateTerm argument
      { terms := by
          simpa [types, List.map_append] using
            translatedPrevious.terms.append
              (.cons translatedArgument.term .nil)
        generated := translatedPrevious.generated.append
          translatedArgument.generated }

end AppliedArguments

/-- A source term decomposed into a non-application head and typed arguments. -/
structure ApplicationSpine (signature : Signature) (context : Context) (result : Ty) where
  headType : Ty
  head : Term signature context headType
  arguments : AppliedArguments signature context headType result

namespace ApplicationSpine

def toTerm {result : Ty} (spine : ApplicationSpine signature context result) :
    Term signature context result :=
  spine.arguments.applyTerm spine.head

/-- Collect the complete left-associated application spine of a term. -/
def collect : {result : Ty} → (term : Term signature context result) →
    ApplicationSpine signature context result
  | _, .app fn argument =>
      let spine := collect fn
      { headType := spine.headType
        head := spine.head
        arguments := .snoc spine.arguments argument }
  | result, term =>
      { headType := result
        head := term
        arguments := .nil result }

@[simp] theorem toTerm_collect (term : Term signature context result) :
    (collect term).toTerm = term := by
  induction term with
  | app fn argument fnIH argumentIH =>
      simp only [collect, toTerm, AppliedArguments.applyTerm_snoc]
      exact congrArg (fun applied => Term.app applied argument) fnIH
  | var | const | boolLit | not | and | or | imp | iff | eq | lam | forallE | existsE =>
      simp [collect, toTerm, AppliedArguments.applyTerm]

end ApplicationSpine

namespace AppliedArguments

/-- Flattening the head consists of the applied prefix followed by the residual
result telescope.  This statement also covers partial spines. -/
theorem flattenArrow_eq
    {start result : Ty}
    (arguments : AppliedArguments signature context start result) :
    (FO.flattenArrow start).1 =
        arguments.types ++ (FO.flattenArrow result).1 ∧
      (FO.flattenArrow start).2 = (FO.flattenArrow result).2 := by
  induction arguments with
  | nil => simp [types]
  | snoc previous argument inductionHypothesis =>
      constructor
      · rw [inductionHypothesis.1]
        simp [List.append_assoc]
      · simpa using inductionHypothesis.2

/-- A spine ending in a ground result consumes the complete leading arrow
telescope of its head type. -/
theorem types_eq_flattenArrow
    {start result : Ty}
    (arguments : AppliedArguments signature context start result)
    (ground : GroundResult result) :
    arguments.types = (FO.flattenArrow start).1 := by
  have shape := (flattenArrow_eq arguments).1
  cases ground <;> simpa using shape.symm

/-- The result of a ground spine is the final result selected by flattening its
head type. -/
theorem result_eq_flattenArrow
    {start result : Ty}
    (arguments : AppliedArguments signature context start result)
    (ground : GroundResult result) :
    result = (FO.flattenArrow start).2 := by
  have shape := (flattenArrow_eq arguments).2
  cases ground <;> simpa using shape.symm

end AppliedArguments

end Crush.Metatheory.Defunctionalization.Flattened
