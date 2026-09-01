import Crush.Metatheory.VCG.Trust
import Crush.SMT.Quote

/-!
# Syntax witnesses for emitted defunctionalization commands

These encodings retain a reified type witness, its ordered SMT sort images,
and the exact command emitted by the Crush translator. They establish
syntactic correspondence only.  In particular, they do not assign semantics to
arbitrary `SMT.SSort`, prove that an emitted term represents an intrinsically typed FO
term, or show that the whole command sequence preserves satisfiability.  Those
are later representation obligations; sort handlers remain governed by
`SortHookCertificate` or the explicit trusted boundary.
-/

namespace Crush.Metatheory.VCG

open Crush.Metatheory.Reification

/-- One reified source type paired with the concrete SMT sort selected by the Crush
translator. -/
structure SortImage where
  reified : ReifiedType
  smt : SMT.SSort

/-- Traverse reified types while retaining a proof that a monadic sort emitter did not
reorder, duplicate, or drop them. -/
def mapSortImagesM {m : Type → Type} [Monad m]
    (emit : ReifiedType → m SMT.SSort) :
    (reifiedTypes : List ReifiedType) →
      m { images : List SortImage // images.map (·.reified) = reifiedTypes }
  | [] => pure ⟨[], rfl⟩
  | reifiedType :: reifiedTypes => do
      let smt ← emit reifiedType
      let ⟨images, equality⟩ ← mapSortImagesM emit reifiedTypes
      return ⟨{ reified := reifiedType, smt } :: images, congrArg (reifiedType :: ·) equality⟩

/-- Syntactic encoding of a flattened n-ary `app` declaration. -/
structure AppDeclEncoding where
  arrow : ReifiedArrowType
  name : String
  functionSort : SMT.SSort
  arguments : List SortImage
  result : SortImage
  argumentTypes_eq : arguments.map (·.reified) = arrow.flatten.1
  resultType_eq : result.reified = arrow.flatten.2
  command : SMT.Command
  command_eq : command = .declFun name
    (#[functionSort] ++ (arguments.map (·.smt)).toArray) result.smt

/-- Syntactic encoding of an exact-capture closure constructor declaration. -/
structure ClosureDeclEncoding where
  arrow : ReifiedArrowType
  name : String
  captures : List SortImage
  captureTypes : List ReifiedType
  captureTypes_eq : captures.map (·.reified) = captureTypes
  functionSort : SMT.SSort
  command : SMT.Command
  command_eq : command = .declFun name (captures.map (·.smt)).toArray functionSort

/-- Syntactic encoding of the defining assertion emitted for a closure. The
optional guard records subtype well-formedness separately from the raw equation;
the record does not by itself prove that either SMT term has the intended
semantics. -/
structure ClosureEquationEncoding where
  arrow : ReifiedArrowType
  appName : String
  closure : SMT.Term
  parameters : Array SMT.Term
  body : SMT.Term
  rawEquation : SMT.Term
  rawEquation_eq : rawEquation =
    let applied := SMT.Term.app (.symb appName) (#[closure] ++ parameters)
    (smt| (= $applied $body))
  guard : Option SMT.Term
  guardedEquation : SMT.Term
  guardedEquation_eq : guardedEquation =
    match guard with
    | none => rawEquation
    | some condition => (smt| (=> $condition $rawEquation))
  binders : Array (String × SMT.SSort)
  /-- Typed proof for the modeled path, or an explicit trusted-boundary reason. -/
  evidence : ClosureEvidence
  command : SMT.Command
  command_eq : command = .assert
    (if binders.isEmpty then guardedEquation else .forallE binders guardedEquation)

/-- Exact emitted encoding of the mutually recursive well-formedness
predicates associated with one reified datatype block. Semantic field-guard
evidence is attached by the later representation layer. -/
structure DatatypeGuardDef where
  reifiedBlock : DatatypeBlock
  defs : Array SMT.FunDef
  command : SMT.Command
  command_eq : command = .defFunsRec defs

/-- Syntax descriptions retained by the Crush translator in emission order. -/
inductive CommandEncoding where
  | app : AppDeclEncoding → CommandEncoding
  | closure : ClosureDeclEncoding → CommandEncoding
  | closureEquation : ClosureEquationEncoding → CommandEncoding
  | datatypeGuard : DatatypeGuardDef → CommandEncoding

namespace CommandEncoding

def command : CommandEncoding → SMT.Command
  | .app encoding => encoding.command
  | .closure encoding => encoding.command
  | .closureEquation encoding => encoding.command
  | .datatypeGuard encoding => encoding.command

private def sortHead? : SMT.SSort → Option String
  | .app (.symb name) _ => some name
  | _ => none

private def termHead? : SMT.Term → Option String
  | .const name => some name
  | .app (.symb name) _ => some name
  | _ => none

/-- Principal allocated symbols determined by the encoding itself. Keeping this
projection here prevents a translator call site from supplying unrelated names
while claiming command/allocation correspondence. -/
def allocatedSymbols : CommandEncoding → Array String
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
  | .datatypeGuard encoding => encoding.defs.map (·.name)

end CommandEncoding

end Crush.Metatheory.VCG
