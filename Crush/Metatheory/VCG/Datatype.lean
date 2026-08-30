import Crush.Metatheory.Reification.Datatype
import Crush.Metatheory.Reification.Witness
import Crush.Metatheory.SMT.DatatypeCarry
import Crush.Metatheory.SMT.DatatypeRepresentation
import Crush.Metatheory.VCG.Command
import Crush.SMT.TermEq

/-!
# Datatype commands retained from production translation

This module records which native datatype and recursive well-formedness commands
occur in the final command array produced by the translator. Each retained
command is indexed by the intrinsic datatype block that it implements and by its
position in that final array. The module proves only this datatype-specific
connection; it does not claim that every other production command is correct.
-/

namespace Crush.Metatheory.VCG

open Reification Datatype Defunctionalization.Flattened

abbrev Command := Crush.SMT.Command

/-- A native command indexed by the exact intrinsic datatype block it declares.
This typed description is what the soundness proof retains after production
metadata has served its discovery purpose. -/
structure NativeCommandFor (owner : SomeBlock) where
  blockEncoding : SMT.Datatype.BlockEncoding owner.arity
  command : Command
  command_eq : command = SMT.Datatype.command owner.block blockEncoding
  wf : SMT.Datatype.CommandWF owner.block blockEncoding

/-- One exact native datatype command, including the allocator-selected names,
its typed reified block, and the well-formedness evidence consumed by canonical
model lifting. Constructors, selectors, and implicit testers are all determined
by the single native command. -/
structure NativeDatatypeCommand where
  owner : DatatypeBlock
  typed : NativeCommandFor ⟨owner.arity, owner.block⟩

instance : TypeName NativeDatatypeCommand := unsafe
  (TypeName.mk _ ``NativeDatatypeCommand)

namespace NativeDatatypeCommand

@[reducible] def block (native : NativeDatatypeCommand) : DatatypeBlock :=
  native.owner

@[reducible] def blockEncoding (native : NativeDatatypeCommand) :
    SMT.Datatype.BlockEncoding native.owner.arity :=
  native.typed.blockEncoding

@[reducible] def command (native : NativeDatatypeCommand) : Command :=
  native.typed.command

theorem command_eq (native : NativeDatatypeCommand) :
    native.command =
      SMT.Datatype.command native.block.block native.blockEncoding :=
  native.typed.command_eq

theorem wf (native : NativeDatatypeCommand) :
    SMT.Datatype.CommandWF native.block.block native.blockEncoding :=
  native.typed.wf

/-- Recover a command indexed by a requested reified block only after checking
exact intrinsic block equality. This replaces the former string-key equation;
metadata rendering is no longer part of the proof boundary. -/
def typedForOwner? (native : NativeDatatypeCommand) (target : SomeBlock) :
    Option (NativeCommandFor target) := by
  let source : SomeBlock := ⟨native.block.arity, native.block.block⟩
  if equal : source = target then
    have typed : NativeCommandFor source := by
      simpa [source] using native.typed
    exact some (equal ▸ typed)
  else
    exact none

def typedFor? (native : NativeDatatypeCommand) (target : DatatypeBlock) :
    Option (NativeCommandFor ⟨target.arity, target.block⟩) :=
  native.typedForOwner? ⟨target.arity, target.block⟩

/-- Concrete allocator-owned names used by the native block. SMT tester
identifiers reuse their constructor name inside `(_ is C)` and therefore do not
allocate another symbol. -/
def names (native : NativeDatatypeCommand) : Array String :=
  let entries := SMT.Datatype.entries native.block.block
    native.blockEncoding
  let sorts := entries.toList.map (·.1)
  let members := entries.toList.flatMap fun entry =>
    entry.2.2.ctors.toList.flatMap fun ctor =>
      ctor.name :: ctor.selDecls.toList.map (·.1)
  (sorts ++ members).toArray

end NativeDatatypeCommand

/-- Dependency-ordered native commands indexed by the exact intrinsic ownership
environment. Command count, block identity, and source-symbol ownership are
consequences of this type, not parallel arrays or rendered keys. -/
inductive NativeCommandLocations {signature : Signature} (allCommands : Array Command) :
    Datatype.Env signature → Type where
  | nil : NativeCommandLocations allCommands []
  | cons {entry : Datatype.Entry signature} {rest : Datatype.Env signature}
      (command : NativeCommandFor ⟨entry.arity, entry.block⟩) (commandIndex : Nat)
      (command_at : allCommands[commandIndex]? = some command.command)
      (tail : NativeCommandLocations allCommands rest) :
      NativeCommandLocations allCommands (entry :: rest)

namespace NativeCommandLocations

/-- Reconnect commands stored without a statically known block to the exact
intrinsic datatype environment. Each lookup checks block equality before
refining the command's type. -/
def ofEnv? {signature : Signature} (allCommands : Array Command)
    (stored : Array NativeDatatypeCommand) (indices : Array Nat) :
    (env : Datatype.Env signature) → Option (NativeCommandLocations allCommands env)
  | [] => some .nil
  | entry :: rest =>
      let owner : SomeBlock := ⟨entry.arity, entry.block⟩
      match stored.findFinIdx? (fun command =>
          (command.typedForOwner? owner).isSome) with
      | none => none
      | some position =>
        match NativeDatatypeCommand.typedForOwner? stored[position] owner,
            indices[position.val]?, ofEnv? allCommands stored indices rest with
        | some command, some commandIndex, some tail =>
            match emittedEq : allCommands[commandIndex]? with
            | some (.declDatatypes emittedEntries) =>
              match expectedEq : command.command with
              | .declDatatypes expectedEntries =>
                if entriesEq : emittedEntries = expectedEntries then
                  have commandAt :
                      allCommands[commandIndex]? = some command.command := by
                    rw [emittedEq, expectedEq, entriesEq]
                  some (.cons command commandIndex commandAt tail)
                else none
              | _ => none
            | _ => none
        | _, _, _ => none

/-- Exact native commands in dependency order. -/
def commands {signature : Signature} {allCommands : Array Command} :
    {env : Datatype.Env signature} →
    NativeCommandLocations allCommands env → Array Command
  | [], .nil => #[]
  | _ :: _, .cons command _ _ tail =>
      #[command.command] ++ commands tail

/-- Positions of the native datatype commands in the final command array. -/
def indices {signature : Signature} {allCommands : Array Command} :
    {env : Datatype.Env signature} →
    NativeCommandLocations allCommands env → Array Nat
  | [], .nil => #[]
  | _ :: _, .cons _ commandIndex _ tail =>
      #[commandIndex] ++ indices tail

@[simp] theorem commands_size {signature : Signature}
    {env : Datatype.Env signature} {allCommands : Array Command}
    (locations : NativeCommandLocations allCommands env) :
    locations.commands.size = env.length := by
  induction locations with
  | nil => rfl
  | cons _ _ _ tail ih => simp [commands, ih, Nat.add_comm]

@[simp] theorem indices_size {signature : Signature}
    {env : Datatype.Env signature} {allCommands : Array Command}
    (locations : NativeCommandLocations allCommands env) :
    locations.indices.size = env.length := by
  induction locations with
  | nil => rfl
  | cons _ _ _ tail ih => simp [indices, ih, Nat.add_comm]

/-- Every paired command and index refers to the exact command already present
in the retained production array. -/
theorem commands_at {signature : Signature} {env : Datatype.Env signature}
    {allCommands : Array Command}
    (locations : NativeCommandLocations allCommands env)
    (position : Nat) :
    locations.indices[position]?.bind (fun index => allCommands[index]?) =
      locations.commands[position]? := by
  induction locations generalizing position with
  | nil => simp [indices, commands]
  | cons command commandIndex commandAt tail ih =>
      cases position with
      | zero =>
          simpa [indices, commands, Array.getElem?_append] using commandAt
      | succ position =>
          simpa [indices, commands, Array.getElem?_append] using ih position

/-- Locate a represented native-command prefix inside a larger command array.
The bound matters because commands after the native prefix need not correspond
to datatype blocks. -/
private def fromAt {signature : Signature} {allCommands : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    (blocks : SMT.Datatype.Represented fo env) (start : Nat)
    (commandAt : ∀ position, position < blocks.commands.size →
      allCommands[start + position]? = blocks.commands[position]?) :
    NativeCommandLocations allCommands env := by
  cases blocks with
  | nil => exact .nil
  | @cons entry rest data head tail =>
      let command : NativeCommandFor ⟨entry.arity, entry.block⟩ := {
        blockEncoding := data
        command := SMT.Datatype.command entry.block data
        command_eq := rfl
        wf := head.wf }
      refine cons command start ?_ ?_
      · have linked := commandAt 0 (by
          simp only [SMT.Datatype.Represented.commands, Array.size_append,
            Array.size_singleton]
          omega)
        simpa [command, SMT.Datatype.Represented.commands,
          Array.getElem?_append] using linked
      · apply fromAt tail (start + 1)
        intro position inBounds
        have linked := commandAt (position + 1) (by
          simp only [SMT.Datatype.Represented.commands, Array.size_append,
            Array.size_singleton]
          omega)
        simpa [SMT.Datatype.Represented.commands, Array.getElem?_append,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using linked

/-- A represented native prefix determines the exact positions of those
commands in the surrounding array. -/
def fromPrefix {signature : Signature} {allCommands suffix : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    (blocks : SMT.Datatype.Represented fo env)
    (emitted_eq : allCommands = blocks.commands ++ suffix) :
    NativeCommandLocations allCommands env := by
  apply fromAt blocks 0
  intro position inBounds
  rw [emitted_eq]
  simp [Array.getElem?_append, inBounds]

/-- Evidence that the located native commands use one FO-to-SMT encoding and
occur in datatype-dependency order. -/
structure Representation {signature : Signature} {allCommands : Array Command}
    (fo : SMT.Encoding (Symbol signature)) {env : Datatype.Env signature}
    (locations : NativeCommandLocations allCommands env) where
  blocks : SMT.Datatype.Represented fo env
  commands_eq : blocks.commands = locations.commands
  ordered : SMT.Datatype.Native.Step.Ordered blocks

namespace Representation

def nil {signature : Signature} {allCommands : Array Command}
    (fo : SMT.Encoding (Symbol signature)) :
    Representation fo (.nil : NativeCommandLocations allCommands []) := {
  blocks := .nil
  commands_eq := rfl
  ordered := .nil }

/-- Extend the represented environment and its ordering proof together with the
exact command location. -/
def cons {signature : Signature} {allCommands : Array Command}
    {fo : SMT.Encoding (Symbol signature)}
    {entry : Datatype.Entry signature} {restEnv : Datatype.Env signature}
    {command : NativeCommandFor ⟨entry.arity, entry.block⟩} {commandIndex : Nat}
    {commandAt : allCommands[commandIndex]? = some command.command}
    {tail : NativeCommandLocations allCommands restEnv}
    (head : SMT.Datatype.Representation entry.block entry.symbols fo
      command.blockEncoding)
    (rest : Representation fo tail)
    (after : SMT.Datatype.Native.Step.After head rest.blocks) :
    Representation fo (.cons command commandIndex commandAt tail) := {
  blocks := .cons head rest.blocks
  commands_eq := by
    simp [SMT.Datatype.Represented.commands, NativeCommandLocations.commands,
      rest.commands_eq, NativeCommandFor.command_eq]
  ordered := .cons after rest.ordered }

/-- Dependency order follows from the represented command sequence. -/
theorem blocks_ordered {signature : Signature} {allCommands : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    {locations : NativeCommandLocations allCommands env}
    (represented : Representation fo locations) :
    SMT.Datatype.Native.Step.Ordered represented.blocks :=
  represented.ordered

@[simp] theorem blocks_commands {signature : Signature}
    {allCommands : Array Command} {fo : SMT.Encoding (Symbol signature)}
    {env : Datatype.Env signature}
    {locations : NativeCommandLocations allCommands env}
    (represented : Representation fo locations) :
    represented.blocks.commands = locations.commands :=
  represented.commands_eq

end Representation

end NativeCommandLocations

/-! ## Exact production datatype-guard commands -/

/-- A production datatype-guard command indexed by the exact intrinsic block
whose `wf_T` predicates it defines. -/
structure GuardCommandFor (owner : SomeBlock) where
  definitions : Array Crush.SMT.FunDef
  command : Command
  command_eq : command = .defFunsRec definitions

namespace DatatypeGuardCommand

/-- Give a stored production guard command the requested block index only after
checking that it belongs to that exact intrinsic block. -/
def typedForOwner? (encoding : DatatypeGuardCommand) (target : SomeBlock) :
    Option (GuardCommandFor target) := by
  let source : SomeBlock :=
    ⟨encoding.owner.arity, encoding.owner.block⟩
  if equal : source = target then
    let typed : GuardCommandFor source := {
      definitions := encoding.definitions
      command := encoding.command
      command_eq := encoding.command_eq }
    exact some (equal ▸ typed)
  else
    exact none

end DatatypeGuardCommand

/-- Dependency-ordered recursive guard commands, each linked to its exact
position in the final production command array. -/
inductive GuardCommandLocations {signature : Signature} (allCommands : Array Command) :
    Datatype.Env signature → Type where
  | nil : GuardCommandLocations allCommands []
  | cons {entry : Datatype.Entry signature} {rest : Datatype.Env signature}
      (command : GuardCommandFor ⟨entry.arity, entry.block⟩)
      (commandIndex : Nat)
      (command_at : allCommands[commandIndex]? = some command.command)
      (tail : GuardCommandLocations allCommands rest) :
      GuardCommandLocations allCommands (entry :: rest)

namespace GuardCommandLocations

/-- Reconnect retained production guard encodings to an exact intrinsic
datatype environment. -/
def ofEnv? {signature : Signature} (allCommands : Array Command)
    (stored : Array DatatypeGuardCommand) (indices : Array Nat) :
    (env : Datatype.Env signature) → Option (GuardCommandLocations allCommands env)
  | [] => some .nil
  | entry :: rest =>
      let owner : SomeBlock := ⟨entry.arity, entry.block⟩
      match stored.findFinIdx? (fun command =>
          (command.typedForOwner? owner).isSome) with
      | none => none
      | some position =>
        match stored[position].typedForOwner? owner,
            indices[position.val]?, ofEnv? allCommands stored indices rest with
        | some command, some commandIndex, some tail =>
            match emittedEq : allCommands[commandIndex]? with
            | some (.defFunsRec emittedDefs) =>
              match expectedEq : command.command with
              | .defFunsRec expectedDefs =>
                if defsEq : emittedDefs = expectedDefs then
                  have commandAt : allCommands[commandIndex]? =
                      some command.command := by
                    rw [emittedEq, expectedEq, defsEq]
                  some (.cons command commandIndex commandAt tail)
                else none
              | _ => none
            | _ => none
        | _, _, _ => none

/-- Exact production recursive guard commands in dependency order. -/
def commands {signature : Signature} {allCommands : Array Command} :
    {env : Datatype.Env signature} →
      GuardCommandLocations allCommands env → Array Command
  | [], .nil => #[]
  | _ :: _, .cons command _ _ tail =>
      #[command.command] ++ commands tail

/-- Positions of the recursive guard commands in the final command array. -/
def indices {signature : Signature} {allCommands : Array Command} :
    {env : Datatype.Env signature} →
      GuardCommandLocations allCommands env → Array Nat
  | [], .nil => #[]
  | _ :: _, .cons _ commandIndex _ tail =>
      #[commandIndex] ++ indices tail

@[simp] theorem commands_size {signature : Signature}
    {env : Datatype.Env signature} {allCommands : Array Command}
    (locations : GuardCommandLocations allCommands env) :
    locations.commands.size = env.length := by
  induction locations with
  | nil => rfl
  | cons _ _ _ tail ih => simp [commands, ih, Nat.add_comm]

@[simp] theorem indices_size {signature : Signature}
    {env : Datatype.Env signature} {allCommands : Array Command}
    (locations : GuardCommandLocations allCommands env) :
    locations.indices.size = env.length := by
  induction locations with
  | nil => rfl
  | cons _ _ _ tail ih => simp [indices, ih, Nat.add_comm]

/-- Every retained recursive guard command is the command at its recorded
position in the final command array. -/
theorem commands_at {signature : Signature} {env : Datatype.Env signature}
    {allCommands : Array Command}
    (locations : GuardCommandLocations allCommands env)
    (position : Nat) :
    locations.indices[position]?.bind (fun index => allCommands[index]?) =
      locations.commands[position]? := by
  induction locations generalizing position with
  | nil => simp [indices, commands]
  | cons command commandIndex commandAt tail ih =>
      cases position with
      | zero =>
          simpa [indices, commands, Array.getElem?_append] using commandAt
      | succ position =>
          simpa [indices, commands, Array.getElem?_append] using ih position

end GuardCommandLocations

/-- One source fact, the common intrinsic environment used to reify it, and the
final command array produced after all selected facts were translated. The two
location fields identify the native datatype commands and recursive datatype
guards in that array. -/
structure ProductionFact where
  expression : Lean.Expr
  datatypes : DatatypeEnv
  ordinarySignature : Signature
  constants : SignatureBridge ordinarySignature
  /-- Exact intrinsic sentence retained when the whole fact, rather than only
  its datatype component, belongs to the supported reification fragment. -/
  sentence : Option (ReifiedSentenceFor expression datatypes constants)
  allCommands : Array Command
  nativeLocations :
    NativeCommandLocations allCommands
      (DataBridge.of datatypes ordinarySignature).toModelEnv
  guardLocations :
    GuardCommandLocations allCommands
      (DataBridge.of datatypes ordinarySignature).toModelEnv

namespace ProductionFact

/-- Retain a production fact only when every datatype in its intrinsic
environment has matching native and recursive-guard commands in the supplied
command array. -/
def build? (expression : Lean.Expr) (datatypes : DatatypeEnv)
    {ordinarySignature : Signature}
    (constants : SignatureBridge ordinarySignature)
    (sentence : Option
      (ReifiedSentenceFor expression datatypes constants))
    (allCommands : Array Command)
    (stored : Array NativeDatatypeCommand) (indices : Array Nat)
    (storedGuards : Array DatatypeGuardCommand) (guardIndices : Array Nat) :
    Option ProductionFact := do
  let nativeLocations ← NativeCommandLocations.ofEnv? allCommands stored indices
    (DataBridge.of datatypes ordinarySignature).toModelEnv
  let guardLocations ← GuardCommandLocations.ofEnv? allCommands storedGuards guardIndices
    (DataBridge.of datatypes ordinarySignature).toModelEnv
  return {
    expression, datatypes, ordinarySignature, constants, sentence, allCommands,
    nativeLocations,
    guardLocations }

/-- Recompute command locations after the translator has finished emitting all
facts, without changing the retained intrinsic environment. -/
def withCommands? (production : ProductionFact) (allCommands : Array Command)
    (stored : Array NativeDatatypeCommand) (indices : Array Nat)
    (storedGuards : Array DatatypeGuardCommand) (guardIndices : Array Nat) :
    Option ProductionFact := do
  let nativeLocations ← NativeCommandLocations.ofEnv? allCommands stored indices
    (DataBridge.of production.datatypes production.ordinarySignature).toModelEnv
  let guardLocations ← GuardCommandLocations.ofEnv? allCommands storedGuards guardIndices
    (DataBridge.of production.datatypes production.ordinarySignature).toModelEnv
  return {
    expression := production.expression
    datatypes := production.datatypes
    ordinarySignature := production.ordinarySignature
    constants := production.constants
    sentence := production.sentence
    allCommands
    nativeLocations
    guardLocations }

/-- Complete intrinsic signature bridge used by this fact. -/
def fullSignatureBridge (production : ProductionFact) :
    SignatureBridge (production.datatypes.signature ++ production.ordinarySignature) :=
  production.constants.prepend production.datatypes.signature

/-- The same datatype ownership environment consumed by the unified soundness
theorem. -/
def datatypeBridge (production : ProductionFact) :
    DataBridge (production.datatypes.signature ++ production.ordinarySignature) :=
  DataBridge.of production.datatypes production.ordinarySignature

/-- Native commands in dependency order, independent of their positions among
the other production commands. -/
def nativeCommands (production : ProductionFact) : Array Crush.SMT.Command :=
  production.nativeLocations.commands

/-- Production command positions corresponding to `nativeCommands`. -/
def commandIndices (production : ProductionFact) : Array Nat :=
  production.nativeLocations.indices

/-- Recursive datatype-guard commands in dependency order. -/
def guardCommands (production : ProductionFact) : Array Crush.SMT.Command :=
  production.guardLocations.commands

/-- Production positions corresponding to `guardCommands`. -/
def guardCommandIndices (production : ProductionFact) : Array Nat :=
  production.guardLocations.indices

@[simp] theorem nativeCommands_size (production : ProductionFact) :
    production.nativeCommands.size = production.datatypes.blocks.size := by
  simp [nativeCommands]

@[simp] theorem commandIndices_size (production : ProductionFact) :
    production.commandIndices.size = production.datatypes.blocks.size := by
  simp [commandIndices]

@[simp] theorem guardCommands_size (production : ProductionFact) :
    production.guardCommands.size = production.datatypes.blocks.size := by
  simp [guardCommands]

@[simp] theorem guardCommandIndices_size (production : ProductionFact) :
    production.guardCommandIndices.size = production.datatypes.blocks.size := by
  simp [guardCommandIndices]

/-- Each native datatype command occurs at its recorded position in the final
production command array. -/
theorem nativeCommand_at (production : ProductionFact)
    (position : Nat) :
    production.commandIndices[position]?.bind
      (fun index => production.allCommands[index]?) =
      production.nativeCommands[position]? := by
  exact production.nativeLocations.commands_at position

/-- Each recursive guard command occurs at its recorded position in the final
production command array. -/
theorem guardCommand_at (production : ProductionFact)
    (position : Nat) :
    production.guardCommandIndices[position]?.bind
      (fun index => production.allCommands[index]?) =
      production.guardCommands[position]? := by
  exact production.guardLocations.commands_at position

/-- Evidence that all located native datatype commands are generated by one
FO-to-SMT encoding and form exactly that encoding's native-command prefix. -/
structure Representation (production : ProductionFact)
    (fo : SMT.Encoding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))) where
  native : production.nativeLocations.Representation fo
  native_eq : fo.nativeCommands = production.nativeCommands

/-- Evidence that the located recursive guard commands use fresh, injective SMT
identifiers and match the datatype blocks fixed by the native representation.
These fields describe command syntax only; they do not depend on a model. -/
structure GuardRepresentation (production : ProductionFact)
    (guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature)))
    (represented : production.Representation guarding.encoding) where
  definitions :
    SMT.Datatype.Native.Step.GuardCommands guarding represented.native.blocks
  commands_eq : definitions.commands = production.guardCommands
  ident : FO.FOSort → Option Crush.SMT.Ident
  ident_injective : ∀ {left right identifier},
    ident left = some identifier → ident right = some identifier → left = right
  notBuiltin : ∀ sort identifier, ident sort = some identifier →
    Crush.SMT.NotBuiltin identifier
  sourceFresh : ∀ sort identifier, ident sort = some identifier →
    ∀ {decl : FO.SymbolDecl}
      (symbol : Symbol (production.datatypes.signature ++ production.ordinarySignature) decl),
      identifier ≠ guarding.encoding.ident symbol
  linked : definitions.Matches ident

namespace GuardRepresentation

/-- Combine the fixed SMT identifiers for guard predicates with their meaning
in one particular target model. -/
def toUnaryGuards {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    (guarded : production.GuardRepresentation guarding represented)
    (target : FO.FamilyModel
      (Symbol (production.datatypes.signature ++ production.ordinarySignature)))
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop) :
    SMT.UnaryGuards guarding.encoding target guard where
  ident := guarded.ident
  ident_injective := guarded.ident_injective
  notBuiltin := guarded.notBuiltin
  sourceFresh := guarded.sourceFresh

end GuardRepresentation

/-- Convert the production-specific evidence into the datatype representation
used by the shared SMT soundness theorems. -/
def Representation.datatypeRepresentation {production : ProductionFact}
    {fo : SMT.Encoding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation fo) :
    SMT.Datatype.EnvRepresentation fo production.datatypeBridge.toModelEnv := {
  blocks := represented.native.blocks
  native_eq := by
    calc
      fo.nativeCommands = production.nativeCommands := represented.native_eq
      _ = production.nativeLocations.commands := rfl
      _ = represented.native.blocks.commands :=
        represented.native.blocks_commands.symm }

/-- One source model's complete guarded target construction. `prior` records
representations already chosen for ordinary base types (for example
`Nat → Int`); the remaining fields install recursive datatype guards using
the same SMT function graph. -/
structure GuardModel (production : ProductionFact)
    (guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature)))
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented)
    (source : Model (production.datatypes.signature ++ production.ordinarySignature))
    (lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv) where
  prior : Lifted (canonicalModel source)
  base : SMT.ExtraGraph guarding.encoding
    (represented.datatypeRepresentation.liftedFrom source lawful prior).target
  baseUnique : Crush.SMT.ApplyUnique
    (SMT.modelWith guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target base)
  fresh : (guarded.toUnaryGuards
    (represented.datatypeRepresentation.liftedFrom source lawful prior).target
    (fun sort => ((represented.datatypeRepresentation.liftedFrom source lawful prior).relation
      sort).guard)).Fresh base
  semantics : guarding.TermSemantics
    (represented.datatypeRepresentation.liftedFrom source lawful prior).target
    ((guarded.toUnaryGuards
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target
      (fun sort => ((represented.datatypeRepresentation.liftedFrom source lawful prior).relation
        sort).guard)).over base)
    (fun sort => ((represented.datatypeRepresentation.liftedFrom source lawful prior).relation
      sort).guard)

namespace GuardModel

/-- SMT function graph implementing the guard predicates for this model, using
the identifiers retained by `GuardRepresentation`. -/
@[reducible] noncomputable def guards {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    {guarded : production.GuardRepresentation guarding represented}
    {source : Model (production.datatypes.signature ++ production.ordinarySignature)}
    {lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv}
    (model : production.GuardModel guarding represented guarded source lawful) :
    SMT.UnaryGuards guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source lawful model.prior).target
      (fun sort => ((represented.datatypeRepresentation.liftedFrom source lawful model.prior).relation
        sort).guard) :=
  guarded.toUnaryGuards
    (represented.datatypeRepresentation.liftedFrom source lawful model.prior).target
    (fun sort => ((represented.datatypeRepresentation.liftedFrom source lawful model.prior).relation
      sort).guard)

/-- Construct the complete guarded model when one ordinary base type is
represented by integers and recursive datatype guards use fixed SMT identifiers.
The remaining premises are source-side carrier facts: integer
nonnegativity represents the distinguished relation guard, and every other sort
omitted by the unary allocation has a total relation guard. All raw graph,
functionality, freshness, and guard-term semantics fields are derived here. -/
noncomputable def ofIntView {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {represented : production.Representation guarding.encoding}
    {guarded : production.GuardRepresentation guarding represented}
    {source : Model (production.datatypes.signature ++ production.ordinarySignature)}
    {lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv}
    (prior : Lifted (canonicalModel source))
    (view : SMT.IntView guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target)
    (guard_eq : guarding.guard = (view.withGuards
      (guarded.toUnaryGuards
        (represented.datatypeRepresentation.liftedFrom source lawful prior).target
        (fun sort => ((represented.datatypeRepresentation.liftedFrom source lawful prior).relation
          sort).guard))).guard)
    (separate : ∀ sort identifier,
      guarded.ident sort = some identifier → identifier ≠ .symb ">=")
    (omitted : ∀ sort, sort ≠ view.sort → guarded.ident sort = none →
      ∀ value,
        ((represented.datatypeRepresentation.liftedFrom source lawful prior).relation sort).guard
          value)
    (integerGuard : ∀ value,
      0 ≤ view.toInt value ↔
        ((represented.datatypeRepresentation.liftedFrom source lawful prior).relation
          view.sort).guard value) :
    production.GuardModel guarding represented guarded source lawful := by
  let lifted := represented.datatypeRepresentation.liftedFrom source lawful prior
  let guards := guarded.toUnaryGuards lifted.target
    (fun sort => (lifted.relation sort).guard)
  have total : ∀ sort, sort ≠ view.sort → guards.ident sort = none →
      ∀ value, (lifted.relation sort).guard value := by
    intro sort unequal absent value
    exact omitted sort unequal absent value
  have guardEqual : ∀ sort value,
      view.guardWith guards sort value ↔ (lifted.relation sort).guard value := by
    intro sort value
    simp only [SMT.IntView.guardWith]
    split
    next equal =>
      subst sort
      exact integerGuard value
    next _ => rfl
  have termSemantics : guarding.TermSemantics lifted.target
      (guards.over view.extra)
      (fun sort => (lifted.relation sort).guard) := by
    have combined :=
      (view.termSemantics_withGuards guards total).congr guardEqual
    exact {
      omitted := by
        intro sort raw absent value
        apply combined.omitted sort raw _ value
        rw [← guard_eq]
        exact absent
      encoded := by
        intro sort raw value environment condition rawEval present
        apply combined.encoded sort raw value environment condition rawEval
        rw [← guard_eq]
        exact present }
  exact {
    prior
    base := view.extra
    baseUnique := view.applyUnique
    fresh := view.guardsFresh guards separate
    semantics := termSemantics }

end GuardModel

/-- One static production guard representation realized for every datatype-lawful
source model. Keeping this family outside the quantified source-model contract
prevents the reflection theorem from silently discarding a lawful source model
merely because target-model construction evidence was not bundled with it. -/
structure GuardInterpretation (production : ProductionFact)
    (guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature)))
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented) where
  realize : ∀ (source : Model
      (production.datatypes.signature ++ production.ordinarySignature))
      (lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv),
    production.GuardModel guarding represented guarded source lawful

namespace Representation

/-- The production representation validates its whole native datatype prefix
in the final dependency-folded target. -/
theorem lifted_valid {production : ProductionFact}
    {fo : SMT.Encoding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation fo)
    (source : Model (production.datatypes.signature ++ production.ordinarySignature))
    (lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv) :
    (SMT.model fo (represented.datatypeRepresentation.lifted source lawful).target).SatisfiesCommands
      fo.nativeCommands :=
  represented.datatypeRepresentation.lifted_valid represented.native.blocks_ordered source lawful

/-- Native validity over a caller-supplied interpreted or guarded base model. -/
theorem liftedFrom_valid {production : ProductionFact}
    {fo : SMT.Encoding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation fo)
    (source : Model (production.datatypes.signature ++ production.ordinarySignature))
    (lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv)
    (prior : Lifted (canonicalModel source)) :
    (SMT.model fo
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target).SatisfiesCommands
      fo.nativeCommands :=
  represented.datatypeRepresentation.liftedFrom_valid represented.native.blocks_ordered
    source lawful prior

/-- Native datatype commands remain valid in the exact combined model used by
fresh `wf_T` predicates and interpreted arithmetic. -/
theorem lifted_valid_with {production : ProductionFact}
    {fo : SMT.Encoding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation fo)
    (source : Model (production.datatypes.signature ++ production.ordinarySignature))
    (lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv)
    (extra : SMT.ExtraGraph fo (represented.datatypeRepresentation.lifted source lawful).target) :
    (SMT.modelWith fo (represented.datatypeRepresentation.lifted source lawful).target extra).SatisfiesCommands
      fo.nativeCommands :=
  represented.datatypeRepresentation.lifted_valid_with represented.native.blocks_ordered
    source lawful extra

/-- Native validity with derived graphs over a caller-supplied base lifting. -/
theorem liftedFrom_valid_with {production : ProductionFact}
    {fo : SMT.Encoding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation fo)
    (source : Model (production.datatypes.signature ++ production.ordinarySignature))
    (lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv)
    (prior : Lifted (canonicalModel source))
    (extra : SMT.ExtraGraph fo
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target) :
    (SMT.modelWith fo (represented.datatypeRepresentation.liftedFrom source lawful prior).target
      extra).SatisfiesCommands fo.nativeCommands :=
  represented.datatypeRepresentation.liftedFrom_valid_with represented.native.blocks_ordered
    source lawful prior extra

/-- The production recursive guard commands are simultaneously valid in the
target model obtained after all datatype blocks are installed, using the same
guard identifiers throughout. -/
theorem guards_valid {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented)
    (source : Model (production.datatypes.signature ++ production.ordinarySignature))
    (lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv)
    (prior : Lifted (canonicalModel source))
    (guards : SMT.UnaryGuards guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target
      (fun sort => ((represented.datatypeRepresentation.liftedFrom source lawful prior).relation
        sort).guard))
    (base : SMT.ExtraGraph guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target)
    (baseUnique : Crush.SMT.ApplyUnique
      (SMT.modelWith guarding.encoding
        (represented.datatypeRepresentation.liftedFrom source lawful prior).target base))
    (fresh : guards.Fresh base)
    (semantics : guarding.TermSemantics
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target (guards.over base)
      (fun sort => ((represented.datatypeRepresentation.liftedFrom source lawful prior).relation
        sort).guard))
    (linked : guarded.definitions.Matches guards.ident) :
    (SMT.modelWith guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source lawful prior).target
      (guards.over base)).SatisfiesCommands production.guardCommands := by
  rw [← guarded.commands_eq]
  simpa [SMT.Datatype.EnvRepresentation.liftedFrom,
    Representation.datatypeRepresentation,
    ProductionFact.datatypeBridge] using
    represented.native.blocks_ordered.guards_valid guarded.definitions source lawful
      prior guards base
      baseUnique fresh semantics linked

/-- One complete soundness theorem for a represented guarded datatype command
array. Native declarations, exact production-shaped `wf_T` definitions,
ordinary declarations, and guarded assertions are interpreted in the same untyped
model. A caller may set `commands := production.allCommands` when the surrounding
array has the stated guarded representation. -/
theorem sound {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented)
    (source : Model (production.datatypes.signature ++ production.ordinarySignature))
    (lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv)
    (guardModel : production.GuardModel guarding represented guarded
      source lawful)
    {theory : FO.FamilyTheory
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      production.guardCommands theory commands)
    (valid : (canonicalModel source).SatisfiesTheory theory) :
    ∃ model : Crush.SMT.Model, model.SatisfiesCommands commands := by
  apply SMT.guarded_lift guarding encoding (canonicalModel source)
    (represented.datatypeRepresentation.liftedFrom source lawful guardModel.prior).target
    (represented.datatypeRepresentation.liftedFrom source lawful guardModel.prior).relation
    (represented.datatypeRepresentation.liftedFrom source lawful guardModel.prior).models valid
    (guardModel.guards.over guardModel.base) guardModel.semantics.toSemantics
  · exact represented.liftedFrom_valid_with source lawful guardModel.prior
      (guardModel.guards.over guardModel.base)
  · exact represented.guards_valid guarded source lawful guardModel.prior
      guardModel.guards guardModel.base guardModel.baseUnique guardModel.fresh
      guardModel.semantics guarded.linked

/-- Semantic unsatisfiability when source models must also supply all base-type
representations in `GuardModel`. Unlike ordinary datatype unsatisfiability,
this condition can restrict opaque source base types, for example by requiring
a `Nat → Int` representation. -/
theorem unsat_under {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented)
    (formula : Sentence
      (production.datatypes.signature ++ production.ordinarySignature))
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      production.guardCommands (translatedTheory formula) commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    UnsatisfiableUnder
      (fun source =>
        Σ lawful : Datatype.Env.Lawful source production.datatypeBridge.toModelEnv,
          production.GuardModel guarding represented guarded source lawful)
      formula := by
  intro source model sourceValid
  rcases model with ⟨lawful, guardModel⟩
  obtain ⟨target, valid⟩ := represented.sound guarded source lawful
    guardModel encoding (model_extension source formula sourceValid)
  exact unsat target valid

/-- Reflection over every datatype-lawful source model once the production
guard interpretation is known uniformly. Unlike `unsat_under`, the quantified
model class contains only the intrinsic source lawfulness condition; untyped target
construction evidence is supplied once by `GuardInterpretation`. -/
theorem unsat {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented)
    (interpretation : production.GuardInterpretation guarding represented guarded)
    (formula : Sentence
      (production.datatypes.signature ++ production.ordinarySignature))
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      production.guardCommands (translatedTheory formula) commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    Datatype.Env.Unsatisfiable production.datatypeBridge.toModelEnv formula := by
  intro source lawful sourceValid
  exact represented.unsat_under guarded formula encoding unsat source
    ⟨lawful, interpretation.realize source lawful⟩ sourceValid

/-- Reflection for a complete finite source theory translated against the
production's one common signature and datatype environment. -/
theorem theory_unsat {production : ProductionFact}
    {guarding : SMT.Guarding
      (Symbol (production.datatypes.signature ++ production.ordinarySignature))}
    (represented : production.Representation guarding.encoding)
    (guarded : production.GuardRepresentation guarding represented)
    (interpretation : production.GuardInterpretation guarding represented guarded)
    (sourceTheory : Theory
      (production.datatypes.signature ++ production.ordinarySignature))
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      production.guardCommands (translatedTheories sourceTheory) commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    Datatype.Env.TheoryUnsatisfiable production.datatypeBridge.toModelEnv
      sourceTheory := by
  intro source lawful sourceValid
  obtain ⟨target, valid⟩ := represented.sound guarded source lawful
    (interpretation.realize source lawful) encoding
    (model_extension_theory source sourceTheory sourceValid)
  exact unsat target valid

end Representation

end ProductionFact

end Crush.Metatheory.VCG
