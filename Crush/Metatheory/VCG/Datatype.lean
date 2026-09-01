import Crush.Metatheory.Reification.Datatype
import Crush.Metatheory.Reification.Witness
import Crush.Metatheory.SMT.DatatypeTransport
import Crush.Metatheory.SMT.DatatypeRepresentation
import Crush.Metatheory.VCG.Command
import Crush.SMT.TermEq

/-!
# Datatype commands retained from translation

This module records which SMT datatype declarations and recursive well-formedness
definitions occur in the command sequence emitted by the translator. Each retained
command is indexed by the reified datatype block that it implements and by its
position in that emitted sequence. The module proves only this datatype-specific
connection; it does not claim that every other translation command is correct.
-/

namespace Crush.Metatheory.VCG

open Reification Datatype Defunctionalization.Flattened

abbrev Command := Crush.SMT.Command

/-- An SMT datatype declaration indexed by the exact reified datatype block it declares.
This typed description is what the soundness proof retains after translation
metadata has served its discovery purpose. -/
structure DatatypeDeclarationFor (reifiedBlock : SomeBlock) where
  blockEncoding : SMT.Datatype.BlockEncoding reifiedBlock.arity
  command : Command
  command_eq : command = SMT.Datatype.command reifiedBlock.block blockEncoding
  wf : SMT.Datatype.CommandWF reifiedBlock.block blockEncoding

/-- One exact SMT datatype declaration, including the allocator-selected names,
its typed reified block, and the well-formedness evidence consumed by canonical
model lifting. Constructors, selectors, and implicit testers are all determined
by the single declaration. -/
structure DatatypeDeclaration where
  reifiedBlock : DatatypeBlock
  typed : DatatypeDeclarationFor ⟨reifiedBlock.arity, reifiedBlock.block⟩

instance : TypeName DatatypeDeclaration := unsafe
  (TypeName.mk _ ``DatatypeDeclaration)

namespace DatatypeDeclaration

@[reducible] def block (declaration : DatatypeDeclaration) : DatatypeBlock :=
  declaration.reifiedBlock

@[reducible] def blockEncoding (declaration : DatatypeDeclaration) :
    SMT.Datatype.BlockEncoding declaration.reifiedBlock.arity :=
  declaration.typed.blockEncoding

@[reducible] def command (declaration : DatatypeDeclaration) : Command :=
  declaration.typed.command

theorem command_eq (declaration : DatatypeDeclaration) :
    declaration.command =
      SMT.Datatype.command declaration.block.block declaration.blockEncoding :=
  declaration.typed.command_eq

theorem wf (declaration : DatatypeDeclaration) :
    SMT.Datatype.CommandWF declaration.block.block declaration.blockEncoding :=
  declaration.typed.wf

/-- Recover a command indexed by a requested reified block only after checking
exact reified block equality. This replaces the former string-key equation;
metadata rendering is no longer part of the proof boundary. -/
def typedForBlock? (declaration : DatatypeDeclaration) (target : SomeBlock) :
    Option (DatatypeDeclarationFor target) := by
  let source : SomeBlock := ⟨declaration.block.arity, declaration.block.block⟩
  if equal : source = target then
    have typed : DatatypeDeclarationFor source := by
      simpa [source] using declaration.typed
    exact some (equal ▸ typed)
  else
    exact none

def typedFor? (declaration : DatatypeDeclaration) (target : DatatypeBlock) :
    Option (DatatypeDeclarationFor ⟨target.arity, target.block⟩) :=
  declaration.typedForBlock? ⟨target.arity, target.block⟩

/-- Concrete allocated names used by the SMT datatype block. SMT tester
identifiers reuse their constructor name inside `(_ is C)` and therefore do not
allocate another symbol. -/
def names (declaration : DatatypeDeclaration) : Array String :=
  let entries := SMT.Datatype.entries declaration.block.block
    declaration.blockEncoding
  let sorts := entries.toList.map (·.1)
  let members := entries.toList.flatMap fun entry =>
    entry.2.2.ctors.toList.flatMap fun ctor =>
      ctor.name :: ctor.selDecls.toList.map (·.1)
  (sorts ++ members).toArray

end DatatypeDeclaration

/-- Dependency-ordered SMT datatype commands indexed by the exact reified block
environment. Command count, block identity, and source-symbol positions are
consequences of this type, not parallel arrays or rendered keys. -/
inductive DatatypeDeclarationLocations {signature : Signature} (emittedCommands : Array Command) :
    Datatype.Env signature → Type where
  | nil : DatatypeDeclarationLocations emittedCommands []
  | cons {entry : Datatype.Entry signature} {rest : Datatype.Env signature}
      (command : DatatypeDeclarationFor ⟨entry.arity, entry.block⟩) (commandIndex : Nat)
      (command_at : emittedCommands[commandIndex]? = some command.command)
      (tail : DatatypeDeclarationLocations emittedCommands rest) :
      DatatypeDeclarationLocations emittedCommands (entry :: rest)

namespace DatatypeDeclarationLocations

/-- Reconnect commands stored without a statically known block to the exact
reified datatype environment. Each lookup checks block equality before
refining the command's type. -/
def ofEnv? {signature : Signature} (emittedCommands : Array Command)
    (stored : Array DatatypeDeclaration) (indices : Array Nat) :
    (env : Datatype.Env signature) → Option (DatatypeDeclarationLocations emittedCommands env)
  | [] => some .nil
  | entry :: rest =>
      let reifiedBlock : SomeBlock := ⟨entry.arity, entry.block⟩
      match stored.findFinIdx? (fun command =>
          (command.typedForBlock? reifiedBlock).isSome) with
      | none => none
      | some position =>
        match DatatypeDeclaration.typedForBlock? stored[position] reifiedBlock,
            indices[position.val]?, ofEnv? emittedCommands stored indices rest with
        | some command, some commandIndex, some tail =>
            match emittedEq : emittedCommands[commandIndex]? with
            | some (.declDatatypes emittedEntries) =>
              match expectedEq : command.command with
              | .declDatatypes expectedEntries =>
                if entriesEq : emittedEntries = expectedEntries then
                  have commandAt :
                      emittedCommands[commandIndex]? = some command.command := by
                    rw [emittedEq, expectedEq, entriesEq]
                  some (.cons command commandIndex commandAt tail)
                else none
              | _ => none
            | _ => none
        | _, _, _ => none

/-- Exact SMT datatype declarations in dependency order. -/
def commands {signature : Signature} {emittedCommands : Array Command} :
    {env : Datatype.Env signature} →
    DatatypeDeclarationLocations emittedCommands env → Array Command
  | [], .nil => #[]
  | _ :: _, .cons command _ _ tail =>
      #[command.command] ++ commands tail

/-- Positions of the SMT datatype declarations in the emitted command sequence. -/
def indices {signature : Signature} {emittedCommands : Array Command} :
    {env : Datatype.Env signature} →
    DatatypeDeclarationLocations emittedCommands env → Array Nat
  | [], .nil => #[]
  | _ :: _, .cons _ commandIndex _ tail =>
      #[commandIndex] ++ indices tail

@[simp] theorem commands_size {signature : Signature}
    {env : Datatype.Env signature} {emittedCommands : Array Command}
    (locations : DatatypeDeclarationLocations emittedCommands env) :
    locations.commands.size = env.length := by
  induction locations with
  | nil => rfl
  | cons _ _ _ tail ih => simp [commands, ih, Nat.add_comm]

@[simp] theorem indices_size {signature : Signature}
    {env : Datatype.Env signature} {emittedCommands : Array Command}
    (locations : DatatypeDeclarationLocations emittedCommands env) :
    locations.indices.size = env.length := by
  induction locations with
  | nil => rfl
  | cons _ _ _ tail ih => simp [indices, ih, Nat.add_comm]

/-- Every paired command and index refers to the exact command already present
in the retained translation array. -/
theorem commands_at {signature : Signature} {env : Datatype.Env signature}
    {emittedCommands : Array Command}
    (locations : DatatypeDeclarationLocations emittedCommands env)
    (position : Nat) :
    locations.indices[position]?.bind (fun index => emittedCommands[index]?) =
      locations.commands[position]? := by
  induction locations generalizing position with
  | nil => simp [indices, commands]
  | cons command commandIndex commandAt tail ih =>
      cases position with
      | zero =>
          simpa [indices, commands, Array.getElem?_append] using commandAt
      | succ position =>
          simpa [indices, commands, Array.getElem?_append] using ih position

/-- Locate a represented SMT datatype prefix inside a larger command sequence.
The bound matters because commands after the datatype prefix need not correspond
to datatype blocks. -/
private def fromAt {signature : Signature} {emittedCommands : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    (blocks : SMT.Datatype.Represented fo env) (start : Nat)
    (commandAt : ∀ position, position < blocks.commands.size →
      emittedCommands[start + position]? = blocks.commands[position]?) :
    DatatypeDeclarationLocations emittedCommands env := by
  cases blocks with
  | nil => exact .nil
  | @cons entry rest data head tail =>
      let command : DatatypeDeclarationFor ⟨entry.arity, entry.block⟩ := {
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

/-- A represented SMT datatype prefix determines the exact positions of those
commands in the surrounding array. -/
def fromPrefix {signature : Signature} {emittedCommands suffix : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    (blocks : SMT.Datatype.Represented fo env)
    (emitted_eq : emittedCommands = blocks.commands ++ suffix) :
    DatatypeDeclarationLocations emittedCommands env := by
  apply fromAt blocks 0
  intro position inBounds
  rw [emitted_eq]
  simp [Array.getElem?_append, inBounds]

/-- Evidence that the located SMT datatype declarations use one FO-to-SMT encoding and
occur in datatype-dependency order. -/
structure Representation {signature : Signature} {emittedCommands : Array Command}
    (fo : SMT.Encoding (Symbol signature)) {env : Datatype.Env signature}
    (locations : DatatypeDeclarationLocations emittedCommands env) where
  blocks : SMT.Datatype.Represented fo env
  commands_eq : blocks.commands = locations.commands
  ordered : SMT.Datatype.Native.ModelExtension.DependencyOrdered blocks

namespace Representation

def nil {signature : Signature} {emittedCommands : Array Command}
    (fo : SMT.Encoding (Symbol signature)) :
    Representation fo (.nil : DatatypeDeclarationLocations emittedCommands []) := {
  blocks := .nil
  commands_eq := rfl
  ordered := .nil }

/-- Extend the represented environment and its ordering proof together with the
exact command location. -/
def cons {signature : Signature} {emittedCommands : Array Command}
    {fo : SMT.Encoding (Symbol signature)}
    {entry : Datatype.Entry signature} {restEnv : Datatype.Env signature}
    {command : DatatypeDeclarationFor ⟨entry.arity, entry.block⟩} {commandIndex : Nat}
    {commandAt : emittedCommands[commandIndex]? = some command.command}
    {tail : DatatypeDeclarationLocations emittedCommands restEnv}
    (head : SMT.Datatype.Representation entry.block entry.symbols fo
      command.blockEncoding)
    (rest : Representation fo tail)
    (after : SMT.Datatype.Native.ModelExtension.DisjointFromSuffix head rest.blocks) :
    Representation fo (.cons command commandIndex commandAt tail) := {
  blocks := .cons head rest.blocks
  commands_eq := by
    simp [SMT.Datatype.Represented.commands, DatatypeDeclarationLocations.commands,
      rest.commands_eq, DatatypeDeclarationFor.command_eq]
  ordered := .cons after rest.ordered }

/-- Dependency order follows from the represented command sequence. -/
theorem blocks_ordered {signature : Signature} {emittedCommands : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    {locations : DatatypeDeclarationLocations emittedCommands env}
    (represented : Representation fo locations) :
    SMT.Datatype.Native.ModelExtension.DependencyOrdered represented.blocks :=
  represented.ordered

@[simp] theorem blocks_commands {signature : Signature}
    {emittedCommands : Array Command} {fo : SMT.Encoding (Symbol signature)}
    {env : Datatype.Env signature}
    {locations : DatatypeDeclarationLocations emittedCommands env}
    (represented : Representation fo locations) :
    represented.blocks.commands = locations.commands :=
  represented.commands_eq

end Representation

end DatatypeDeclarationLocations

/-! ## Exact translation datatype-guard commands -/

/-- A translation datatype-guard command indexed by the exact reified block
whose `wf_T` predicates it defines. -/
structure DatatypeGuardDefinitionFor (_reifiedBlock : SomeBlock) where
  definitions : Array Crush.SMT.FunDef
  command : Command
  command_eq : command = .defFunsRec definitions

namespace DatatypeGuardDefinition

/-- Give a stored translation guard command the requested block index only after
checking that it belongs to that exact reified block. -/
def typedForBlock? (encoding : DatatypeGuardDefinition) (target : SomeBlock) :
    Option (DatatypeGuardDefinitionFor target) := by
  let source : SomeBlock :=
    ⟨encoding.reifiedBlock.arity, encoding.reifiedBlock.block⟩
  if equal : source = target then
    let typed : DatatypeGuardDefinitionFor source := {
      definitions := encoding.definitions
      command := encoding.command
      command_eq := encoding.command_eq }
    exact some (equal ▸ typed)
  else
    exact none

end DatatypeGuardDefinition

/-- Dependency-ordered recursive guard commands, each linked to its exact
position in the final translation command array. -/
inductive DatatypeGuardDefinitionLocations {signature : Signature} (emittedCommands : Array Command) :
    Datatype.Env signature → Type where
  | nil : DatatypeGuardDefinitionLocations emittedCommands []
  | cons {entry : Datatype.Entry signature} {rest : Datatype.Env signature}
      (command : DatatypeGuardDefinitionFor ⟨entry.arity, entry.block⟩)
      (commandIndex : Nat)
      (command_at : emittedCommands[commandIndex]? = some command.command)
      (tail : DatatypeGuardDefinitionLocations emittedCommands rest) :
      DatatypeGuardDefinitionLocations emittedCommands (entry :: rest)

namespace DatatypeGuardDefinitionLocations

/-- Reconnect retained translation guard encodings to an exact reified
datatype environment. -/
def ofEnv? {signature : Signature} (emittedCommands : Array Command)
    (stored : Array DatatypeGuardDefinition) (indices : Array Nat) :
    (env : Datatype.Env signature) → Option (DatatypeGuardDefinitionLocations emittedCommands env)
  | [] => some .nil
  | entry :: rest =>
      let reifiedBlock : SomeBlock := ⟨entry.arity, entry.block⟩
      match stored.findFinIdx? (fun command =>
          (command.typedForBlock? reifiedBlock).isSome) with
      | none => none
      | some position =>
        match stored[position].typedForBlock? reifiedBlock,
            indices[position.val]?, ofEnv? emittedCommands stored indices rest with
        | some command, some commandIndex, some tail =>
            match emittedEq : emittedCommands[commandIndex]? with
            | some (.defFunsRec emittedDefs) =>
              match expectedEq : command.command with
              | .defFunsRec expectedDefs =>
                if defsEq : emittedDefs = expectedDefs then
                  have commandAt : emittedCommands[commandIndex]? =
                      some command.command := by
                    rw [emittedEq, expectedEq, defsEq]
                  some (.cons command commandIndex commandAt tail)
                else none
              | _ => none
            | _ => none
        | _, _, _ => none

/-- Exact translation recursive guard commands in dependency order. -/
def commands {signature : Signature} {emittedCommands : Array Command} :
    {env : Datatype.Env signature} →
      DatatypeGuardDefinitionLocations emittedCommands env → Array Command
  | [], .nil => #[]
  | _ :: _, .cons command _ _ tail =>
      #[command.command] ++ commands tail

/-- Positions of the recursive guard definitions in the emitted command sequence. -/
def indices {signature : Signature} {emittedCommands : Array Command} :
    {env : Datatype.Env signature} →
      DatatypeGuardDefinitionLocations emittedCommands env → Array Nat
  | [], .nil => #[]
  | _ :: _, .cons _ commandIndex _ tail =>
      #[commandIndex] ++ indices tail

@[simp] theorem commands_size {signature : Signature}
    {env : Datatype.Env signature} {emittedCommands : Array Command}
    (locations : DatatypeGuardDefinitionLocations emittedCommands env) :
    locations.commands.size = env.length := by
  induction locations with
  | nil => rfl
  | cons _ _ _ tail ih => simp [commands, ih, Nat.add_comm]

@[simp] theorem indices_size {signature : Signature}
    {env : Datatype.Env signature} {emittedCommands : Array Command}
    (locations : DatatypeGuardDefinitionLocations emittedCommands env) :
    locations.indices.size = env.length := by
  induction locations with
  | nil => rfl
  | cons _ _ _ tail ih => simp [indices, ih, Nat.add_comm]

/-- Every retained recursive guard command is the command at its recorded
position in the emitted command sequence. -/
theorem commands_at {signature : Signature} {env : Datatype.Env signature}
    {emittedCommands : Array Command}
    (locations : DatatypeGuardDefinitionLocations emittedCommands env)
    (position : Nat) :
    locations.indices[position]?.bind (fun index => emittedCommands[index]?) =
      locations.commands[position]? := by
  induction locations generalizing position with
  | nil => simp [indices, commands]
  | cons command commandIndex commandAt tail ih =>
      cases position with
      | zero =>
          simpa [indices, commands, Array.getElem?_append] using commandAt
      | succ position =>
          simpa [indices, commands, Array.getElem?_append] using ih position

end DatatypeGuardDefinitionLocations

/-- One source fact, the common reified environment used to reify it, and the
complete command sequence emitted after all selected facts were translated. The two
location fields identify the SMT datatype declarations and recursive datatype
guards in that array. -/
structure FactTranslationRecord where
  expression : Lean.Expr
  datatypes : DatatypeEnv
  ordinarySignature : Signature
  constants : ReifiedSignature ordinarySignature
  /-- Exact reified higher-order sentence retained when the whole fact, rather than only
  its datatype component, belongs to the supported reification fragment. -/
  reifiedSentence : Option (ReifiedSentenceFor expression datatypes constants)
  emittedCommands : Array Command
  datatypeDeclarationLocations :
    DatatypeDeclarationLocations emittedCommands
      (DatatypeSignaturePrefix.of datatypes ordinarySignature).toModelEnv
  guardDefinitionLocations :
    DatatypeGuardDefinitionLocations emittedCommands
      (DatatypeSignaturePrefix.of datatypes ordinarySignature).toModelEnv

namespace FactTranslationRecord

/-- Retain a translation fact only when every datatype in its reified
environment has matching SMT datatype declarations and recursive guard definitions in the supplied
command array. -/
def build? (expression : Lean.Expr) (datatypes : DatatypeEnv)
    {ordinarySignature : Signature}
    (constants : ReifiedSignature ordinarySignature)
    (reifiedSentence : Option
      (ReifiedSentenceFor expression datatypes constants))
    (emittedCommands : Array Command)
    (stored : Array DatatypeDeclaration) (indices : Array Nat)
    (storedGuards : Array DatatypeGuardDefinition) (guardIndices : Array Nat) :
    Option FactTranslationRecord := do
  let datatypeDeclarationLocations ← DatatypeDeclarationLocations.ofEnv? emittedCommands stored indices
    (DatatypeSignaturePrefix.of datatypes ordinarySignature).toModelEnv
  let guardDefinitionLocations ← DatatypeGuardDefinitionLocations.ofEnv? emittedCommands storedGuards guardIndices
    (DatatypeSignaturePrefix.of datatypes ordinarySignature).toModelEnv
  return {
    expression, datatypes, ordinarySignature, constants, reifiedSentence, emittedCommands,
    datatypeDeclarationLocations,
    guardDefinitionLocations }

/-- Recompute command locations after the translator has finished emitting all
facts, without changing the retained reified environment. -/
def withCommands? (translation : FactTranslationRecord) (emittedCommands : Array Command)
    (stored : Array DatatypeDeclaration) (indices : Array Nat)
    (storedGuards : Array DatatypeGuardDefinition) (guardIndices : Array Nat) :
    Option FactTranslationRecord := do
  let datatypeDeclarationLocations ← DatatypeDeclarationLocations.ofEnv? emittedCommands stored indices
    (DatatypeSignaturePrefix.of translation.datatypes translation.ordinarySignature).toModelEnv
  let guardDefinitionLocations ← DatatypeGuardDefinitionLocations.ofEnv? emittedCommands storedGuards guardIndices
    (DatatypeSignaturePrefix.of translation.datatypes translation.ordinarySignature).toModelEnv
  return {
    expression := translation.expression
    datatypes := translation.datatypes
    ordinarySignature := translation.ordinarySignature
    constants := translation.constants
    reifiedSentence := translation.reifiedSentence
    emittedCommands
    datatypeDeclarationLocations
    guardDefinitionLocations }

/-- Complete reified signature used by this fact. -/
def fullReifiedSignature (translation : FactTranslationRecord) :
    ReifiedSignature (translation.datatypes.signature ++ translation.ordinarySignature) :=
  translation.constants.prepend translation.datatypes.signature

/-- The same datatype block environment consumed by the unified soundness
theorem. -/
def datatypeSignaturePrefix (translation : FactTranslationRecord) :
    DatatypeSignaturePrefix (translation.datatypes.signature ++ translation.ordinarySignature) :=
  DatatypeSignaturePrefix.of translation.datatypes translation.ordinarySignature

/-- SMT datatype declarations in dependency order, independent of their positions among
the other translation commands. -/
def datatypeDeclarations (translation : FactTranslationRecord) : Array Crush.SMT.Command :=
  translation.datatypeDeclarationLocations.commands

/-- Emitted command positions corresponding to `datatypeDeclarations`. -/
def datatypeDeclarationIndices (translation : FactTranslationRecord) : Array Nat :=
  translation.datatypeDeclarationLocations.indices

/-- Recursive datatype-guard commands in dependency order. -/
def guardDefinitionCommands (translation : FactTranslationRecord) : Array Crush.SMT.Command :=
  translation.guardDefinitionLocations.commands

/-- Emitted positions corresponding to `guardDefinitionCommands`. -/
def guardDefinitionIndices (translation : FactTranslationRecord) : Array Nat :=
  translation.guardDefinitionLocations.indices

@[simp] theorem datatypeDeclarations_size (translation : FactTranslationRecord) :
    translation.datatypeDeclarations.size = translation.datatypes.blocks.size := by
  simp [datatypeDeclarations]

@[simp] theorem datatypeDeclarationIndices_size (translation : FactTranslationRecord) :
    translation.datatypeDeclarationIndices.size = translation.datatypes.blocks.size := by
  simp [datatypeDeclarationIndices]

@[simp] theorem guardDefinitionCommands_size (translation : FactTranslationRecord) :
    translation.guardDefinitionCommands.size = translation.datatypes.blocks.size := by
  simp [guardDefinitionCommands]

@[simp] theorem guardDefinitionIndices_size (translation : FactTranslationRecord) :
    translation.guardDefinitionIndices.size = translation.datatypes.blocks.size := by
  simp [guardDefinitionIndices]

/-- Each SMT datatype declaration occurs at its recorded position in the complete
emitted command sequence. -/
theorem datatypeDeclaration_at (translation : FactTranslationRecord)
    (position : Nat) :
    translation.datatypeDeclarationIndices[position]?.bind
      (fun index => translation.emittedCommands[index]?) =
      translation.datatypeDeclarations[position]? := by
  exact translation.datatypeDeclarationLocations.commands_at position

/-- Each recursive guard command occurs at its recorded position in the final
translation command array. -/
theorem guardDefinition_at (translation : FactTranslationRecord)
    (position : Nat) :
    translation.guardDefinitionIndices[position]?.bind
      (fun index => translation.emittedCommands[index]?) =
      translation.guardDefinitionCommands[position]? := by
  exact translation.guardDefinitionLocations.commands_at position

/-- Evidence that all located SMT datatype declarations are generated by one
FO-to-SMT encoding and form exactly that encoding's datatype-command prefix. -/
structure Representation (translation : FactTranslationRecord)
    (fo : SMT.Encoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))) where
  declarations : translation.datatypeDeclarationLocations.Representation fo
  datatypeDeclarations_eq : fo.nativeCommands = translation.datatypeDeclarations

/-- Evidence that the located recursive guard commands use fresh, injective SMT
identifiers and match the datatype blocks fixed by the SMT datatype representation.
These fields describe command syntax only; they do not depend on a model. -/
structure GuardDefinitionEncoding (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding) where
  definitions :
    SMT.Datatype.Native.ModelExtension.GuardCommands guarding represented.declarations.blocks
  commands_eq : definitions.commands = translation.guardDefinitionCommands
  ident : FO.FOSort → Option Crush.SMT.Ident
  ident_injective : ∀ {left right identifier},
    ident left = some identifier → ident right = some identifier → left = right
  notBuiltin : ∀ sort identifier, ident sort = some identifier →
    Crush.SMT.NotBuiltin identifier
  sourceFresh : ∀ sort identifier, ident sort = some identifier →
    ∀ {decl : FO.SymbolDecl}
      (symbol : Symbol (translation.datatypes.signature ++ translation.ordinarySignature) decl),
      identifier ≠ guarding.encoding.ident symbol
  linked : definitions.Matches ident

namespace GuardDefinitionEncoding

/-- Combine the fixed SMT identifiers for guard predicates with their meaning
in one particular target model. -/
def toUnaryGuards {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.Representation guarding.encoding}
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (target : FO.FamilyModel
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (guard : ∀ sort : FO.FOSort, sort.Denote target.carriers → Prop) :
    SMT.UnaryGuards guarding.encoding target guard where
  ident := guarded.ident
  ident_injective := guarded.ident_injective
  notBuiltin := guarded.notBuiltin
  sourceFresh := guarded.sourceFresh

end GuardDefinitionEncoding

/-- Convert the translation-specific evidence into the datatype representation
used by the shared SMT soundness theorems. -/
def Representation.datatypeRepresentation {translation : FactTranslationRecord}
    {fo : SMT.Encoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation fo) :
    SMT.Datatype.EnvRepresentation fo translation.datatypeSignaturePrefix.toModelEnv := {
  blocks := represented.declarations.blocks
  datatypeCommands_eq := by
    calc
      fo.nativeCommands = translation.datatypeDeclarations := represented.datatypeDeclarations_eq
      _ = translation.datatypeDeclarationLocations.commands := rfl
      _ = represented.declarations.blocks.commands :=
        represented.declarations.blocks_commands.symm }

/-- One source model's complete guarded target construction. `prior` records
representations already chosen for ordinary base types (for example
`Nat → Int`); the remaining fields install recursive datatype guards using
the same SMT function graph. -/
structure GuardedModelExtension (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (source : Model (translation.datatypes.signature ++ translation.ordinarySignature))
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv) where
  prior : Lifted (canonicalModel source)
  base : SMT.ExtraGraph guarding.encoding
    (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
  baseUnique : Crush.SMT.ApplyUnique
    (SMT.modelWith guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target base)
  fresh : (guarded.toUnaryGuards
    (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
    (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation
      sort).guard)).Fresh base
  semantics : guarding.TermSemantics
    (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
    ((guarded.toUnaryGuards
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
      (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation
        sort).guard)).over base)
    (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation
      sort).guard)
  /-- Standard Boolean and integer semantics for the completed raw model.
  `ofIntView` constructs this field from an explicit FO sort mapped to SMT
  `Int` whose target carrier is isomorphic to `Int`; `Encoding` alone does not
  provide that model-dependent fact. -/
  standard : Crush.SMT.Model.Standard
    (SMT.modelWith guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
      ((guarded.toUnaryGuards
        (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
        (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation
          sort).guard)).over base))

namespace GuardedModelExtension

/-- SMT function graph implementing the guard predicates for this model, using
the identifiers retained by `GuardDefinitionEncoding`. -/
@[reducible] noncomputable def guards {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.Representation guarding.encoding}
    {guarded : translation.GuardDefinitionEncoding guarding represented}
    {source : Model (translation.datatypes.signature ++ translation.ordinarySignature)}
    {freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv}
    (model : translation.GuardedModelExtension guarding represented guarded source freeDataModel) :
    SMT.UnaryGuards guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source freeDataModel model.prior).target
      (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel model.prior).relation
        sort).guard) :=
  guarded.toUnaryGuards
    (represented.datatypeRepresentation.liftedFrom source freeDataModel model.prior).target
    (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel model.prior).relation
      sort).guard)

/-- Construct the complete guarded model when one ordinary base type is
represented by integers and recursive datatype guards use fixed SMT identifiers.
The remaining premises are source-side carrier facts: integer
nonnegativity represents the distinguished relation guard, and every other sort
omitted by the unary allocation has a total relation guard. All raw graph,
functionality, freshness, and guard-term semantics fields are derived here. -/
noncomputable def ofIntView {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {represented : translation.Representation guarding.encoding}
    {guarded : translation.GuardDefinitionEncoding guarding represented}
    {source : Model (translation.datatypes.signature ++ translation.ordinarySignature)}
    {freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv}
    (prior : Lifted (canonicalModel source))
    (view : SMT.IntView guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target)
    (guard_eq : guarding.guard = (view.withGuards
      (guarded.toUnaryGuards
        (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
        (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation
          sort).guard))).guard)
    (separate : ∀ sort identifier,
      guarded.ident sort = some identifier → identifier ≠ .symb ">=")
    (omitted : ∀ sort, sort ≠ view.sort → guarded.ident sort = none →
      ∀ value,
        ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation sort).guard
          value)
    (integerGuard : ∀ value,
      0 ≤ view.toInt value ↔
        ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation
          view.sort).guard value) :
    translation.GuardedModelExtension guarding represented guarded source freeDataModel := by
  let lifted := represented.datatypeRepresentation.liftedFrom source freeDataModel prior
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
    semantics := termSemantics
    standard := view.standard_withGuards guards separate }

end GuardedModelExtension

/-- One static guard representation realized for every source model satisfying the
free-datatype condition. Keeping this family outside the quantified source-model
contract prevents the reflection theorem from silently discarding a source model
merely because target-model construction evidence was not bundled with it. -/
structure GuardDefinitionSemantics (translation : FactTranslationRecord)
    (guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature)))
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented) where
  realize : ∀ (source : Model
      (translation.datatypes.signature ++ translation.ordinarySignature))
      (freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv),
    translation.GuardedModelExtension guarding represented guarded source freeDataModel

namespace Representation

/-- The translation representation validates its whole SMT datatype prefix
in the final dependency-folded target. -/
theorem lifted_valid {translation : FactTranslationRecord}
    {fo : SMT.Encoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation fo)
    (source : Model (translation.datatypes.signature ++ translation.ordinarySignature))
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv) :
    (SMT.model fo (represented.datatypeRepresentation.lifted source freeDataModel).target).SatisfiesCommands
      fo.nativeCommands :=
  represented.datatypeRepresentation.lifted_valid represented.declarations.blocks_ordered source freeDataModel

/-- SMT datatype validity over a caller-supplied interpreted or guarded base model. -/
theorem liftedFrom_valid {translation : FactTranslationRecord}
    {fo : SMT.Encoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation fo)
    (source : Model (translation.datatypes.signature ++ translation.ordinarySignature))
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv)
    (prior : Lifted (canonicalModel source)) :
    (SMT.model fo
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target).SatisfiesCommands
      fo.nativeCommands :=
  represented.datatypeRepresentation.liftedFrom_valid represented.declarations.blocks_ordered
    source freeDataModel prior

/-- SMT datatype declarations remain valid in the exact combined model used by
fresh `wf_T` predicates and interpreted arithmetic. -/
theorem lifted_valid_with {translation : FactTranslationRecord}
    {fo : SMT.Encoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation fo)
    (source : Model (translation.datatypes.signature ++ translation.ordinarySignature))
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv)
    (extra : SMT.ExtraGraph fo (represented.datatypeRepresentation.lifted source freeDataModel).target) :
    (SMT.modelWith fo (represented.datatypeRepresentation.lifted source freeDataModel).target extra).SatisfiesCommands
      fo.nativeCommands :=
  represented.datatypeRepresentation.lifted_valid_with represented.declarations.blocks_ordered
    source freeDataModel extra

/-- SMT datatype validity with derived graphs over a caller-supplied base lifting. -/
theorem liftedFrom_valid_with {translation : FactTranslationRecord}
    {fo : SMT.Encoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation fo)
    (source : Model (translation.datatypes.signature ++ translation.ordinarySignature))
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv)
    (prior : Lifted (canonicalModel source))
    (extra : SMT.ExtraGraph fo
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target) :
    (SMT.modelWith fo (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
      extra).SatisfiesCommands fo.nativeCommands :=
  represented.datatypeRepresentation.liftedFrom_valid_with represented.declarations.blocks_ordered
    source freeDataModel prior extra

/-- The translation recursive guard commands are simultaneously valid in the
target model obtained after all datatype blocks are installed, using the same
guard identifiers throughout. -/
theorem guards_valid {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (source : Model (translation.datatypes.signature ++ translation.ordinarySignature))
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv)
    (prior : Lifted (canonicalModel source))
    (guards : SMT.UnaryGuards guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
      (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation
        sort).guard))
    (base : SMT.ExtraGraph guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target)
    (baseUnique : Crush.SMT.ApplyUnique
      (SMT.modelWith guarding.encoding
        (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target base))
    (fresh : guards.Fresh base)
    (semantics : guarding.TermSemantics
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target (guards.over base)
      (fun sort => ((represented.datatypeRepresentation.liftedFrom source freeDataModel prior).relation
        sort).guard))
    (linked : guarded.definitions.Matches guards.ident) :
    (SMT.modelWith guarding.encoding
      (represented.datatypeRepresentation.liftedFrom source freeDataModel prior).target
      (guards.over base)).SatisfiesCommands translation.guardDefinitionCommands := by
  rw [← guarded.commands_eq]
  simpa [SMT.Datatype.EnvRepresentation.liftedFrom,
    Representation.datatypeRepresentation,
    FactTranslationRecord.datatypeSignaturePrefix] using
    represented.declarations.blocks_ordered.guards_valid guarded.definitions source freeDataModel
      prior guards base
      baseUnique fresh semantics linked

/-- One complete soundness theorem for a represented guarded datatype command
sequence. SMT datatype declarations, exact translation-shaped `wf_T` definitions,
ordinary declarations, and guarded assertions are interpreted in the same untyped
model. A caller may set `commands := translation.emittedCommands` when the surrounding
array has the stated guarded representation. -/
theorem sound {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (source : Model (translation.datatypes.signature ++ translation.ordinarySignature))
    (freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv)
    (guardModel : translation.GuardedModelExtension guarding represented guarded
      source freeDataModel)
    {theory : FO.FamilyTheory
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      translation.guardDefinitionCommands theory commands)
    (valid : (canonicalModel source).SatisfiesTheory theory) :
    ∃ model : Crush.SMT.Model,
      model.Standard ∧ model.SatisfiesCommands commands := by
  let target :=
    (represented.datatypeRepresentation.liftedFrom source freeDataModel
      guardModel.prior).target
  let extra := guardModel.guards.over guardModel.base
  refine ⟨SMT.modelWith guarding.encoding target extra, guardModel.standard, ?_⟩
  apply SMT.guarded_valid guarding encoding (canonicalModel source) target
    (represented.datatypeRepresentation.liftedFrom source freeDataModel guardModel.prior).relation
    (represented.datatypeRepresentation.liftedFrom source freeDataModel guardModel.prior).models valid
    extra guardModel.semantics.toSemantics
  · exact represented.liftedFrom_valid_with source freeDataModel guardModel.prior extra
  · exact represented.guards_valid guarded source freeDataModel guardModel.prior
      guardModel.guards guardModel.base guardModel.baseUnique guardModel.fresh
      guardModel.semantics guarded.linked

/-- Semantic unsatisfiability when source models must also supply all base-type
representations in `GuardedModelExtension`. Unlike ordinary datatype unsatisfiability,
this condition can restrict opaque source base types, for example by requiring
a `Nat → Int` representation. -/
theorem unsat_under {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (formula : Sentence
      (translation.datatypes.signature ++ translation.ordinarySignature))
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      translation.guardDefinitionCommands (translatedTheory formula) commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    UnsatisfiableUnder
      (fun source =>
        Σ freeDataModel : Datatype.Env.IsFreeDatatypeModel source translation.datatypeSignaturePrefix.toModelEnv,
          translation.GuardedModelExtension guarding represented guarded source freeDataModel)
      formula := by
  intro source model sourceValid
  rcases model with ⟨freeDataModel, guardModel⟩
  obtain ⟨target, standard, valid⟩ := represented.sound guarded source freeDataModel
    guardModel encoding (model_extension source formula sourceValid)
  exact unsat.noModel target standard valid

/-- Reflection over every source model satisfying the free-datatype condition once the
guard interpretation is known uniformly. Unlike `unsat_under`, the quantified
model class contains only the free-datatype source-model condition; untyped target
construction evidence is supplied once by `GuardDefinitionSemantics`. -/
theorem unsat {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (interpretation : translation.GuardDefinitionSemantics guarding represented guarded)
    (formula : Sentence
      (translation.datatypes.signature ++ translation.ordinarySignature))
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      translation.guardDefinitionCommands (translatedTheory formula) commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    Datatype.Env.Unsatisfiable translation.datatypeSignaturePrefix.toModelEnv formula := by
  intro source freeDataModel sourceValid
  exact represented.unsat_under guarded formula encoding unsat source
    ⟨freeDataModel, interpretation.realize source freeDataModel⟩ sourceValid

/-- Reflection for a complete finite source theory translated against the
translation's one common signature and datatype environment. -/
theorem theory_unsat {translation : FactTranslationRecord}
    {guarding : SMT.GuardedEncoding
      (Symbol (translation.datatypes.signature ++ translation.ordinarySignature))}
    (represented : translation.Representation guarding.encoding)
    (guarded : translation.GuardDefinitionEncoding guarding represented)
    (interpretation : translation.GuardDefinitionSemantics guarding represented guarded)
    (sourceTheory : Theory
      (translation.datatypes.signature ++ translation.ordinarySignature))
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      translation.guardDefinitionCommands (translatedTheories sourceTheory) commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    Datatype.Env.TheoryUnsatisfiable translation.datatypeSignaturePrefix.toModelEnv
      sourceTheory := by
  intro source freeDataModel sourceValid
  obtain ⟨target, standard, valid⟩ := represented.sound guarded source freeDataModel
    (interpretation.realize source freeDataModel) encoding
    (model_extension_theory source sourceTheory sourceValid)
  exact unsat.noModel target standard valid

end Representation

end FactTranslationRecord

end Crush.Metatheory.VCG
