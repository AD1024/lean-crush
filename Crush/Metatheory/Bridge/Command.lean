import Crush.Metatheory.Bridge.Type
import Crush.SMT.Syntax

/-!
# Proof-carrying production declarations

These certificates retain the intrinsic type witness, its ordered SMT sort
images, and the exact command emitted by the live translator. They deliberately
do not assign semantics to arbitrary `SMT.SSort`; sort handlers remain governed
by `SortHookCertificate` or the explicit trusted boundary.
-/

namespace Crush.Metatheory.Bridge

/-- One intrinsic type paired with the concrete SMT sort selected by production. -/
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

/-- Certificate for a production n-ary `app` declaration. -/
structure AppDeclarationCertificate where
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

/-- Certificate for an exact-capture closure constructor declaration. -/
structure ClosureDeclarationCertificate where
  arrow : ArrowBridge
  name : String
  captures : List SortImage
  captureTypes : List TypeBridge
  captureBridges : captures.map (·.bridge) = captureTypes
  functionSort : SMT.SSort
  command : SMT.Command
  command_eq : command = .declFun name (captures.map (·.smt)).toArray functionSort

/-- Certificate for the defining assertion emitted for a closure. The optional
guard records subtype well-formedness separately from the raw semantic equation. -/
structure ClosureEquationCertificate where
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
  /-- Index into `TranslateState.verifiedClosures` when executable reification
  produced the dependent semantic closure certificate. -/
  verifiedClosureIndex : Option Nat
  command : SMT.Command
  command_eq : command = .assert
    (if binders.isEmpty then guardedEquation else .forallE binders guardedEquation)

/-- Certificates retained by the live translation state in emission order. -/
inductive CommandCertificate where
  | app : AppDeclarationCertificate → CommandCertificate
  | closure : ClosureDeclarationCertificate → CommandCertificate
  | closureEquation : ClosureEquationCertificate → CommandCertificate

namespace CommandCertificate

def command : CommandCertificate → SMT.Command
  | .app certificate => certificate.command
  | .closure certificate => certificate.command
  | .closureEquation certificate => certificate.command

private def sortHead? : SMT.SSort → Option String
  | .app (.symb name) _ => some name
  | _ => none

private def termHead? : SMT.Term → Option String
  | .const name => some name
  | .app (.symb name) _ => some name
  | _ => none

/-- Principal structural symbols determined by the certificate itself. Keeping
this projection here prevents a live call site from supplying unrelated names
while claiming command/allocation correspondence. -/
def structuralSymbols : CommandCertificate → Array String
  | .app certificate =>
      match sortHead? certificate.functionSort with
      | some functionSort => #[functionSort, certificate.name]
      | none => #[certificate.name]
  | .closure certificate =>
      match sortHead? certificate.functionSort with
      | some functionSort => #[functionSort, certificate.name]
      | none => #[certificate.name]
  | .closureEquation certificate =>
      match termHead? certificate.closure with
      | some closureName => #[closureName, certificate.appName]
      | none => #[certificate.appName]

end CommandCertificate

end Crush.Metatheory.Bridge
