import Crush.Metatheory.VCG.Trust
import Crush.SMT.Syntax

/-!
# Syntax witnesses for emitted defunctionalization commands

These encodings retain an intrinsic type witness, its ordered SMT sort images,
and the exact command emitted by the stateful translator.  They establish
syntactic correspondence only.  In particular, they do not assign semantics to
arbitrary `SMT.SSort`, prove that an emitted term represents an intrinsic FO
term, or show that the whole command sequence preserves satisfiability.  Those
are later representation obligations; sort handlers remain governed by
`SortHookCertificate` or the explicit trusted boundary.
-/

namespace Crush.Metatheory.VCG

open Crush.Metatheory.Reification

/-- One intrinsic type paired with the concrete SMT sort selected by the stateful
translator. -/
structure SortImage where
  bridge : TypeBridge
  smt : SMT.SSort

/-- Traverse bridges while retaining a proof that a monadic sort emitter did not
reorder, duplicate, or drop intrinsic types. -/
def mapSortImagesM {m : Type → Type} [Monad m]
    (emit : TypeBridge → m SMT.SSort) :
    (bridges : List TypeBridge) →
      m { images : List SortImage // images.map (·.bridge) = bridges }
  | [] => pure ⟨[], rfl⟩
  | bridge :: bridges => do
      let smt ← emit bridge
      let ⟨images, equality⟩ ← mapSortImagesM emit bridges
      return ⟨{ bridge, smt } :: images, congrArg (bridge :: ·) equality⟩

/-- Syntactic encoding of a flattened n-ary `app` declaration. -/
structure AppDeclarationEncoding where
  arrow : ArrowBridge
  name : String
  functionSort : SMT.SSort
  arguments : List SortImage
  result : SortImage
  argumentBridges : arguments.map (·.bridge) = arrow.flatten.1
  resultBridge : result.bridge = arrow.flatten.2
  command : SMT.Command
  command_eq : command = .declFun name
    (#[functionSort] ++ (arguments.map (·.smt)).toArray) result.smt

/-- Syntactic encoding of an exact-capture closure constructor declaration. -/
structure ClosureDeclarationEncoding where
  arrow : ArrowBridge
  name : String
  captures : List SortImage
  captureTypes : List TypeBridge
  captureBridges : captures.map (·.bridge) = captureTypes
  functionSort : SMT.SSort
  command : SMT.Command
  command_eq : command = .declFun name (captures.map (·.smt)).toArray functionSort

/-- Syntactic encoding of the defining assertion emitted for a closure. The
optional guard records subtype well-formedness separately from the raw equation;
the record does not by itself prove that either SMT term has the intended
semantics. -/
structure ClosureEquationEncoding where
  arrow : ArrowBridge
  appName : String
  closure : SMT.Term
  parameters : Array SMT.Term
  body : SMT.Term
  rawEquation : SMT.Term
  rawEquation_eq : rawEquation = SMT.Term.symbApp "=" #[
    SMT.Term.app (.symb appName) (#[closure] ++ parameters), body]
  guard : Option SMT.Term
  guardedEquation : SMT.Term
  guardedEquation_eq : guardedEquation =
    match guard with
    | none => rawEquation
    | some condition => SMT.Term.symbApp "=>" #[condition, rawEquation]
  binders : Array (String × SMT.SSort)
  /-- Typed proof for the modeled path, or an explicit trusted-boundary reason. -/
  evidence : ClosureEvidence
  command : SMT.Command
  command_eq : command = .assert
    (if binders.isEmpty then guardedEquation else .forallE binders guardedEquation)

/-- Syntax witnesses retained by the stateful translation in emission order. -/
inductive CommandEncoding where
  | app : AppDeclarationEncoding → CommandEncoding
  | closure : ClosureDeclarationEncoding → CommandEncoding
  | closureEquation : ClosureEquationEncoding → CommandEncoding

namespace CommandEncoding

def command : CommandEncoding → SMT.Command
  | .app encoding => encoding.command
  | .closure encoding => encoding.command
  | .closureEquation encoding => encoding.command

private def sortHead? : SMT.SSort → Option String
  | .app (.symb name) _ => some name
  | _ => none

private def termHead? : SMT.Term → Option String
  | .const name => some name
  | .app (.symb name) _ => some name
  | _ => none

/-- Principal structural symbols determined by the encoding itself. Keeping
this projection here prevents a stateful call site from supplying unrelated names
while claiming command/allocation correspondence. -/
def structuralSymbols : CommandEncoding → Array String
  | .app encoding =>
      match sortHead? encoding.functionSort with
      | some functionSort => #[functionSort, encoding.name]
      | none => #[encoding.name]
  | .closure encoding =>
      match sortHead? encoding.functionSort with
      | some functionSort => #[functionSort, encoding.name]
      | none => #[encoding.name]
  | .closureEquation encoding =>
      match termHead? encoding.closure with
      | some closureName => #[closureName, encoding.appName]
      | none => #[encoding.appName]

end CommandEncoding

end Crush.Metatheory.VCG
