import Crush.Metatheory.VCG.Stateful
import Crush.Metatheory.SMT.DatatypeCanonical

/-!
# Intrinsic VCG soundness

These theorems start at the intrinsically typed HO sentence returned by
reification and compose exact stateful FO-to-SMT representation. The separate
structural reification witness does not supply a denotation for arbitrary
`Lean.Expr`, so it is not an unused premise of a misleading "Lean-to-SMT"
theorem here.
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

/-- Executable specialization for the exact state returned by total VCG. -/
theorem run_unsat_implies_source_unsat
    {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature)) (source : Sentence signature)
    (datatypes : DataBridge signature)
    (native : EnvRepresentation encoding datatypes.toModelEnv)
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (run cfg encoding source).2.commands) :
    Datatype.Env.Unsatisfiable datatypes.toModelEnv source := by
  exact (run_represents cfg encoding source).unsat_source native unsat

/-- End-to-end reflection for the guarded certified route. The semantic
contract combines datatype lawfulness with the interpreted-base/guard model
used by this exact command array. -/
theorem runGuarded_unsat_under {certificate : CertifiedDataEnv} (cfg : Config)
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
        Σ lawful : Datatype.Env.Lawful source certificate.data.toModelEnv,
          certificate.GuardModel guarding represented guarded source lawful)
      formula := by
  exact represented.unsat_under guarded formula
    (runGuarded_represents cfg guarding certificate.guardCommands formula) unsat

/-- Guarded reflection over every datatype-lawful source model. The uniform
guard interpretation is a property of the production encoding, rather than
target-model evidence nested inside the quantified source-model contract. -/
theorem runGuarded_unsat_implies_source_unsat
    {certificate : CertifiedDataEnv} (cfg : Config)
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented)
    (interpretation : certificate.GuardInterpretation guarding represented guarded)
    (formula : Sentence
      (certificate.env.signature ++ certificate.tail))
    (unsat : Crush.SMT.CommandsUnsatisfiable
      (runGuarded cfg guarding certificate.guardCommands formula).commands) :
    Datatype.Env.Unsatisfiable certificate.data.toModelEnv formula := by
  exact represented.unsat guarded interpretation formula
    (runGuarded_represents cfg guarding certificate.guardCommands formula) unsat

end Crush.Metatheory.VCG
