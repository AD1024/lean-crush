import Crush.Metatheory.VCG.Stateful

/-!
# End-to-end VCG soundness

The final theorem composes a structural Lean-to-HO witness with exact stateful
FO-to-SMT representation.  Its conclusion is deliberately about the reified HO
sentence: the metatheory does not postulate a denotation for arbitrary
`Lean.Expr`.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened Reification

/-- Unsatisfiability of the exact commands represented by a state reflects to
the intrinsic source sentence. -/
theorem StateRepresents.unsat_source {signature : Signature}
    {encoding : SMT.Encoding (Symbol signature)} {source : Sentence signature}
    {state : TranslateState} (represented : StateRepresents encoding source state)
    (unsat : Crush.SMT.CommandsUnsatisfiable state.commands) :
    Unsatisfiable source := by
  exact target_unsat_implies_source_unsat source
    (SMT.commands_unsat_implies_theory_unsat encoding
      represented.representation unsat)

/-- End-to-end theorem for the supported Lean fragment and proved VCG route.
The reification witness connects the live Lean expression structurally to the
intrinsic sentence; exact command unsatisfiability then reflects to that
sentence. -/
theorem encoded_unsat_implies_source_unsat
    {expression typeExpr : Lean.Expr} {signature : Signature}
    {signatureBridge : SignatureBridge signature}
    {source : Sentence signature} {encoding : SMT.Encoding (Symbol signature)}
    {state : TranslateState}
    (_reified : Reifies signatureBridge ContextBridge.nil expression
      (.pack (.bool typeExpr) source))
    (represented : StateRepresents encoding source state)
    (unsat : Crush.SMT.CommandsUnsatisfiable state.commands) :
    Unsatisfiable source := by
  exact represented.unsat_source unsat

/-- Executable specialization for the exact state returned by total VCG. -/
theorem run_unsat_implies_source_unsat
    {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature)) (source : Sentence signature)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (run cfg encoding source).2.commands) :
    Unsatisfiable source := by
  exact (run_represents cfg encoding source).unsat_source unsat

end Crush.Metatheory.VCG
