import Crush.Metatheory.Defunctionalization.FlattenedApplication

/-!
# Production-shaped flattened closure equations

The classic verified core emits a unary `app` equation for each lambda. The live
translator instead emits one equation using the completely flattened application
telescope. This module closes that semantic gap directly for arbitrary arity.

The theorem below uses the exact-capture constructor interpretation from model
extension and the n-ary application theorem from `FlattenedApplication`. Thus it
does not identify the unary and flattened syntaxes; it proves the actual
production-shaped equation semantically.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

variable {signature : Signature}

/-- Captured variables supplied to a production-family closure constructor. -/
@[reducible] def captureArgs {context : Context} :
    (captures : List (PackedVar context)) →
      FO.FamilyArgs (Symbol signature) (targetContext context)
        ((captures.map PackedVar.type).map FO.FOSort.ofTy)
  | [] => .nil
  | .pack ref :: captures =>
      .cons (.var (targetVar ref)) (captureArgs captures)

/-- Read a source valuation from a production target valuation. Canonical
production carriers use source functions at function-value sorts. -/
def sourceValuation (source : Model signature) {context : Context}
    (targetValuation : TargetValuation source context) :
    Valuation source.Base context :=
  fun {_} ref => fromCanonical source _ (targetValuation (targetVar ref))

/-- Feeding production capture arguments to the exact-capture interpretation is
the same valuation reconstruction used in the classic model-extension proof. -/
theorem apply_captureArgs_interpretClosure
    (source : Model signature) (closure : Closure signature)
    (captures : List (PackedVar closure.context))
    (targetValuation : TargetValuation source closure.context)
    (reconstructed : Valuation source.Base closure.context) :
    FO.FamilyArgs.apply (captureArgs captures)
        (canonicalModel source) targetValuation
        (interpretClosureCaptures source closure captures reconstructed) =
      Term.denote source (.lam closure.body)
        (installCaptured source captures
          (sourceValuation source targetValuation) reconstructed) := by
  induction captures generalizing reconstructed with
  | nil =>
      simp [captureArgs, FO.FamilyArgs.apply,
        interpretClosureCaptures, installCaptured]
  | cons capture captures inductionHypothesis =>
      cases capture with
      | pack ref =>
          unfold captureArgs
          simp only [List.map_cons, FO.FamilyArgs.apply.eq_2,
            FO.FamilyTerm.denote.eq_1]
          unfold interpretClosureCaptures installCaptured
          exact inductionHypothesis _

/-- The production closure term denotes the original source lambda under the
valuation reconstructed from target variables. -/
theorem denote_closure (source : Model signature)
    (closure : Closure signature)
    (targetValuation : TargetValuation source closure.context) :
    FO.FamilyTerm.denote (canonicalModel source)
        (.symbol (Symbol.closure closure)
          (captureArgs closure.captureRefs)) targetValuation =
      toCanonical source (.arrow closure.domain closure.codomain)
        (Term.denote source (.lam closure.body)
          (sourceValuation source targetValuation)) := by
  simp only [FO.FamilyTerm.denote.eq_2]
  change
    FO.FamilyArgs.apply (captureArgs closure.captureRefs)
        (canonicalModel source) targetValuation
        (interpretClosureCaptures source closure closure.captureRefs
          (SourceValuation.default source closure.context)) =
      Term.denote source (.lam closure.body)
        (sourceValuation source targetValuation)
  rw [apply_captureArgs_interpretClosure source closure
    closure.captureRefs targetValuation
    (SourceValuation.default source closure.context)]
  exact (closure_denote_installCaptured source closure
    (sourceValuation source targetValuation)
    (SourceValuation.default source closure.context)).symm

/-- The fully flattened production equation for a closure is semantically
correct at arbitrary arity.

The left side is precisely one application of production's n-ary `app` symbol to
the exact-capture closure constructor and a complete typed argument spine. The
right side is the same arguments applied to the source lambda. -/
theorem flattenedClosureApplication_correct
    (source : Model signature) (closure : Closure signature)
    (translate : {ty : Ty} → Term signature closure.context ty →
      TargetTerm signature closure.context ty)
    (arguments : SourceArgs signature closure.context
      (FO.flattenArrow (.arrow closure.domain closure.codomain)).1)
    (targetValuation : TargetValuation source closure.context)
    (translateCorrect : ∀ {argTy : Ty}
      (term : Term signature closure.context argTy),
      FO.FamilyTerm.denote (canonicalModel source)
          (translate term) targetValuation =
        toCanonical source argTy
          (Term.denote source term
            (sourceValuation source targetValuation))) :
    FO.FamilyTerm.denote (canonicalModel source)
        (flattenedApplicationTerm closure.domain closure.codomain
          (.symbol (Symbol.closure closure)
            (captureArgs closure.captureRefs))
          translate arguments) targetValuation =
      toCanonical source
        (FO.flattenArrow (.arrow closure.domain closure.codomain)).2
        (arguments.applyDenote source
          (sourceValuation source targetValuation)
          (.arrow closure.domain closure.codomain)
          (Term.denote source (.lam closure.body)
            (sourceValuation source targetValuation))) := by
  apply flattenedApplicationTerm_correct source closure.domain closure.codomain
    (Term.denote source (.lam closure.body)
      (sourceValuation source targetValuation))
    (.symbol (Symbol.closure closure)
      (captureArgs closure.captureRefs))
    translate arguments
    (sourceValuation source targetValuation) targetValuation
  · exact denote_closure source closure targetValuation
  · exact translateCorrect

end Crush.Metatheory.Defunctionalization.Flattened
