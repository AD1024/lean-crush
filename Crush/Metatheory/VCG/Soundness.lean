import Crush.Metatheory.VCG.Stateful
import Crush.Metatheory.SMT.DatatypeCanonical

/-!
# End-to-end VCG soundness

The final theorem composes a structural Lean-to-HO witness with exact stateful
FO-to-SMT representation.  Its conclusion is deliberately about the reified HO
sentence: the metatheory does not postulate a denotation for arbitrary
`Lean.Expr`.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened Reification SMT.Datatype
open scoped Crush.Metatheory Crush.SMT

/-- Unsatisfiability of the exact commands represented by a state reflects to
the intrinsic source sentence. -/
theorem StateRepresents.unsat_source {signature : Signature}
    {encoding : SMT.Encoding (Symbol signature)} {source : Sentence signature}
    {state : TranslateState} (represented : StateRepresents encoding source state)
    {env : Datatype.Env signature} (native : EnvRepresentation encoding env)
    (unsat : Crush.SMT.CommandsUnsatisfiable state.commands) :
    Datatype.Env.Unsatisfiable env source := by
  exact SMT.commands_unsat_implies_source_unsat encoding native source
    represented.representation unsat

/-- End-to-end theorem for the supported Lean fragment and proved VCG route.
The reification witness connects the live Lean expression structurally to the
intrinsic sentence; exact command unsatisfiability then reflects to that
sentence. -/
theorem encoded_unsat_implies_source_unsat
    {expression typeExpr : Lean.Expr} {signature : Signature}
    {signatureBridge : SignatureBridge signature}
    {source : Sentence signature} {encoding : SMT.Encoding (Symbol signature)}
    {state : TranslateState} {datatypes : DataBridge signature}
    (_reified : Reifies signatureBridge ContextBridge.nil expression
      (.pack (.bool typeExpr) source) (some datatypes))
    (represented : StateRepresents encoding source state)
    (native : EnvRepresentation encoding datatypes.core)
    (unsat : Crush.SMT.CommandsUnsatisfiable state.commands) :
    Datatype.Env.Unsatisfiable datatypes.core source := by
  exact represented.unsat_source native unsat

/-- Executable specialization for the exact state returned by total VCG. -/
theorem run_unsat_implies_source_unsat
    {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature)) (source : Sentence signature)
    (datatypes : DataBridge signature)
    (native : EnvRepresentation encoding datatypes.core)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (run cfg encoding source).2.commands) :
    Datatype.Env.Unsatisfiable datatypes.core source := by
  exact (run_represents cfg encoding source).unsat_source native unsat

/-- End-to-end reflection for the guarded certified route. The semantic
contract combines datatype lawfulness with the interpreted-base/guard model
used by this exact command array. -/
theorem runGuarded_unsat {certificate : CertifiedDataEnv} (cfg : Config)
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented)
    (formula : Sentence
      (certificate.env.signature ++ certificate.tail))
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (runGuarded cfg guarding certificate.guardCommands formula).commands) :
    UnsatisfiableUnder
      (fun source =>
        Σ lawful : Datatype.Env.Lawful source certificate.data.core,
          certificate.GuardModel guarding represented guarded source lawful)
      formula := by
  exact represented.unsat_under guarded formula
    (runGuarded_represents cfg guarding certificate.guardCommands formula) unsat

end Crush.Metatheory.VCG
