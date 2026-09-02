import Crush.Metatheory.Defunctionalization.Symbol

/-!
# Emitted flattened closure equations

This module proves that a closure constructor supplied with its exact captured
variables denotes the original higher-order lambda under the corresponding
source valuation.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature}

/-- Captured variables supplied to a flattened-symbol-family closure constructor. -/
@[reducible] def captureArgs {context : Context} :
    (captures : List (PackedVar context)) →
      FO.FamilyArgs (Symbol signature) (targetContext context)
        ((captures.map PackedVar.type).map FO.FOSort.ofTy)
  | [] => .nil
  | .pack ref :: captures =>
      .cons (.var (targetVar ref)) (captureArgs captures)

/-- Read a source valuation from a target valuation. Canonical target carriers use
source functions at function-value sorts. -/
def sourceValuation (source : Model signature) {context : Context}
    (targetValuation : TargetValuation source context) :
    Valuation source.Base context :=
  fun {_} ref => fromCanonical source _ (targetValuation (targetVar ref))

/-- Feeding the translator capture arguments to the exact-capture interpretation is
the same valuation reconstruction used in the reference model-extension proof. -/
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

/-- The emitted closure term denotes the original source lambda under the
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

end Crush.Metatheory.Defunctionalization
