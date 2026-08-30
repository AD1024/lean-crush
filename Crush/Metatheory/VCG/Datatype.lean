import Crush.Metatheory.Reification.Datatype
import Crush.Metatheory.SMT.DatatypeCarry
import Crush.Metatheory.SMT.DatatypeRepresentation
import Crush.Metatheory.VCG.Command
import Crush.SMT.TermEq

/-!
# Certified production datatype commands

This module is the narrow proof-carrying boundary for the opt-in datatype path.
It relates one reified Lean mutual block to the exact native SMT datatype command
emitted for it. It does not classify the surrounding legacy VCG as certified.
-/

namespace Crush.Metatheory.VCG

open Reification Datatype Defunctionalization.Flattened

abbrev Command := Crush.SMT.Command

/-- A native command indexed by the exact intrinsic datatype block it declares.
This is the proof-relevant core retained after production metadata has served
its discovery purpose. -/
structure DataCommand (owner : SomeBlock) where
  encoding : SMT.Datatype.Encoding owner.arity
  command : Command
  command_eq : command = SMT.Datatype.command owner.block encoding
  wf : SMT.Datatype.CommandWF owner.block encoding

/-- One exact native datatype command, including the allocator-selected names,
its typed reified block, and the well-formedness evidence consumed by canonical
model lifting. Constructors, selectors, and implicit testers are all determined
by the single native command. -/
structure CertifiedDataCommand where
  owner : DatatypeBlock
  typed : DataCommand ⟨owner.arity, owner.block⟩

instance : TypeName CertifiedDataCommand := unsafe
  (TypeName.mk _ ``CertifiedDataCommand)

namespace CertifiedDataCommand

@[reducible] def block (certificate : CertifiedDataCommand) : DatatypeBlock :=
  certificate.owner

@[reducible] def encoding (certificate : CertifiedDataCommand) :
    SMT.Datatype.Encoding certificate.owner.arity :=
  certificate.typed.encoding

@[reducible] def command (certificate : CertifiedDataCommand) : Command :=
  certificate.typed.command

theorem command_eq (certificate : CertifiedDataCommand) :
    certificate.command =
      SMT.Datatype.command certificate.block.block certificate.encoding :=
  certificate.typed.command_eq

theorem wf (certificate : CertifiedDataCommand) :
    SMT.Datatype.CommandWF certificate.block.block certificate.encoding :=
  certificate.typed.wf

/-- Recover a command indexed by a requested reified block only after checking
exact intrinsic block equality. This replaces the former string-key equation;
metadata rendering is no longer part of the proof boundary. -/
def typedForOwner? (certificate : CertifiedDataCommand) (target : SomeBlock) :
    Option (DataCommand target) := by
  let source : SomeBlock := ⟨certificate.block.arity, certificate.block.block⟩
  if equal : source = target then
    have typed : DataCommand source := by
      simpa [source] using certificate.typed
    exact some (equal ▸ typed)
  else
    exact none

def typedFor? (certificate : CertifiedDataCommand) (target : DatatypeBlock) :
    Option (DataCommand ⟨target.arity, target.block⟩) :=
  certificate.typedForOwner? ⟨target.arity, target.block⟩

/-- Concrete allocator-owned names used by the native block. SMT tester
identifiers reuse their constructor name inside `(_ is C)` and therefore do not
allocate another symbol. -/
def names (certificate : CertifiedDataCommand) : Array String :=
  let entries := SMT.Datatype.entries certificate.block.block certificate.encoding
  let sorts := entries.toList.map (·.1)
  let members := entries.toList.flatMap fun entry =>
    entry.2.2.ctors.toList.flatMap fun ctor =>
      ctor.name :: ctor.selDecls.toList.map (·.1)
  (sorts ++ members).toArray

end CertifiedDataCommand

/-- Dependency-ordered native commands indexed by the exact intrinsic ownership
environment. Command count, block identity, and source-symbol ownership are
consequences of this type, not parallel arrays or rendered keys. -/
inductive CertifiedDataTrace {signature : Signature} (emitted : Array Command) :
    Datatype.Env signature → Type where
  | nil : CertifiedDataTrace emitted []
  | cons {entry : Datatype.Entry signature} {rest : Datatype.Env signature}
      (command : DataCommand ⟨entry.arity, entry.block⟩) (commandIndex : Nat)
      (command_at : emitted[commandIndex]? = some command.command)
      (tail : CertifiedDataTrace emitted rest) :
      CertifiedDataTrace emitted (entry :: rest)

namespace CertifiedDataTrace

/-- Reconnect existential production commands to the exact intrinsic ownership
environment. Each lookup checks block equality before refining the command. -/
def ofEnv? {signature : Signature} (emitted : Array Command)
    (stored : Array CertifiedDataCommand) (indices : Array Nat) :
    (env : Datatype.Env signature) → Option (CertifiedDataTrace emitted env)
  | [] => some .nil
  | entry :: rest =>
      let owner : SomeBlock := ⟨entry.arity, entry.block⟩
      match stored.findFinIdx? (fun command =>
          (command.typedForOwner? owner).isSome) with
      | none => none
      | some position =>
        match CertifiedDataCommand.typedForOwner? stored[position] owner,
            indices[position.val]?, ofEnv? emitted stored indices rest with
        | some command, some commandIndex, some tail =>
            match emittedEq : emitted[commandIndex]? with
            | some (.declDatatypes emittedEntries) =>
              match expectedEq : command.command with
              | .declDatatypes expectedEntries =>
                if entriesEq : emittedEntries = expectedEntries then
                  have commandAt :
                      emitted[commandIndex]? = some command.command := by
                    rw [emittedEq, expectedEq, entriesEq]
                  some (.cons command commandIndex commandAt tail)
                else none
              | _ => none
            | _ => none
        | _, _, _ => none

/-- Exact native commands in dependency order. -/
def commands {signature : Signature} {emitted : Array Command} :
    {env : Datatype.Env signature} →
    CertifiedDataTrace emitted env → Array Command
  | [], .nil => #[]
  | _ :: _, .cons command _ _ tail =>
      #[command.command] ++ commands tail

/-- Exact production-state positions in dependency order. -/
def indices {signature : Signature} {emitted : Array Command} :
    {env : Datatype.Env signature} →
    CertifiedDataTrace emitted env → Array Nat
  | [], .nil => #[]
  | _ :: _, .cons _ commandIndex _ tail =>
      #[commandIndex] ++ indices tail

@[simp] theorem commands_size {signature : Signature}
    {env : Datatype.Env signature} {emitted : Array Command}
    (trace : CertifiedDataTrace emitted env) :
    trace.commands.size = env.length := by
  induction trace with
  | nil => rfl
  | cons _ _ _ tail ih => simp [commands, ih, Nat.add_comm]

@[simp] theorem indices_size {signature : Signature}
    {env : Datatype.Env signature} {emitted : Array Command}
    (trace : CertifiedDataTrace emitted env) :
    trace.indices.size = env.length := by
  induction trace with
  | nil => rfl
  | cons _ _ _ tail ih => simp [indices, ih, Nat.add_comm]

/-- Every paired command and index refers to the exact command already present
in the retained production array. -/
theorem commands_at {signature : Signature} {env : Datatype.Env signature}
    {emitted : Array Command} (trace : CertifiedDataTrace emitted env)
    (position : Nat) :
    trace.indices[position]?.bind (fun index => emitted[index]?) =
      trace.commands[position]? := by
  induction trace generalizing position with
  | nil => simp [indices, commands]
  | cons command commandIndex commandAt tail ih =>
      cases position with
      | zero =>
          simpa [indices, commands, Array.getElem?_append] using commandAt
      | succ position =>
          simpa [indices, commands, Array.getElem?_append] using ih position

/-- Build an indexed datatype trace from a represented command segment beginning
at `start` in a larger emitted array.  The bound is essential: commands following
the native prefix need not agree with the exhausted datatype trace. -/
private def fromAt {signature : Signature} {emitted : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    (blocks : SMT.Datatype.Represented fo env) (start : Nat)
    (commandAt : ∀ position, position < blocks.commands.size →
      emitted[start + position]? = blocks.commands[position]?) :
    CertifiedDataTrace emitted env := by
  cases blocks with
  | nil => exact .nil
  | @cons entry rest data head tail =>
      let command : DataCommand ⟨entry.arity, entry.block⟩ := {
        encoding := data
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

/-- A represented native prefix determines a proof-relevant trace at the exact
indices of the surrounding command array. -/
def fromPrefix {signature : Signature} {emitted suffix : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    (blocks : SMT.Datatype.Represented fo env)
    (emitted_eq : emitted = blocks.commands ++ suffix) :
    CertifiedDataTrace emitted env := by
  apply fromAt blocks 0
  intro position inBounds
  rw [emitted_eq]
  simp [Array.getElem?_append, inBounds]

/-- Shared-encoding representation of an exact production trace. The ordinary
represented environment is the single structural witness; command agreement and
dependency order are properties of it, not a second recursive mirror. -/
structure Represents {signature : Signature} {emitted : Array Command}
    (fo : SMT.Encoding (Symbol signature)) {env : Datatype.Env signature}
    (trace : CertifiedDataTrace emitted env) where
  blocks : SMT.Datatype.Represented fo env
  commands_eq : blocks.commands = trace.commands
  ordered : SMT.Datatype.Native.Step.Ordered blocks

namespace Represents

def nil {signature : Signature} {emitted : Array Command}
    (fo : SMT.Encoding (Symbol signature)) :
    Represents fo (.nil : CertifiedDataTrace emitted []) := {
  blocks := .nil
  commands_eq := rfl
  ordered := .nil }

/-- Extend the single represented environment and its ordering proof in lockstep
with the exact production trace. -/
def cons {signature : Signature} {emitted : Array Command}
    {fo : SMT.Encoding (Symbol signature)}
    {entry : Datatype.Entry signature} {restEnv : Datatype.Env signature}
    {command : DataCommand ⟨entry.arity, entry.block⟩} {commandIndex : Nat}
    {commandAt : emitted[commandIndex]? = some command.command}
    {tail : CertifiedDataTrace emitted restEnv}
    (head : SMT.Datatype.Representation entry.block entry.symbols fo
      command.encoding)
    (rest : Represents fo tail)
    (after : SMT.Datatype.Native.Step.After head rest.blocks) :
    Represents fo (.cons command commandIndex commandAt tail) := {
  blocks := .cons head rest.blocks
  commands_eq := by
    simp [SMT.Datatype.Represented.commands, CertifiedDataTrace.commands,
      rest.commands_eq, DataCommand.command_eq]
  ordered := .cons after rest.ordered }

/-- Dependency order is intrinsic to the represented trace rather than stored
again by the enclosing production certificate. -/
theorem blocks_ordered {signature : Signature} {emitted : Array Command}
    {fo : SMT.Encoding (Symbol signature)} {env : Datatype.Env signature}
    {trace : CertifiedDataTrace emitted env}
    (represented : Represents fo trace) :
    SMT.Datatype.Native.Step.Ordered represented.blocks :=
  represented.ordered

@[simp] theorem blocks_commands {signature : Signature}
    {emitted : Array Command} {fo : SMT.Encoding (Symbol signature)}
    {env : Datatype.Env signature} {trace : CertifiedDataTrace emitted env}
    (represented : Represents fo trace) :
    represented.blocks.commands = trace.commands :=
  represented.commands_eq

end Represents

end CertifiedDataTrace

/-! ## Exact production datatype-guard commands -/

/-- A production datatype-guard command indexed by the exact intrinsic block
whose `wf_T` predicates it defines. -/
structure DataGuardCommand (owner : SomeBlock) where
  definitions : Array Crush.SMT.FunDef
  command : Command
  command_eq : command = .defFunsRec definitions

namespace DataGuardEncoding

/-- Refine an existential production guard encoding only after checking its
exact intrinsic block identity. -/
def typedForOwner? (encoding : DataGuardEncoding) (target : SomeBlock) :
    Option (DataGuardCommand target) := by
  let source : SomeBlock :=
    ⟨encoding.owner.arity, encoding.owner.block⟩
  if equal : source = target then
    let typed : DataGuardCommand source := {
      definitions := encoding.definitions
      command := encoding.command
      command_eq := encoding.command_eq }
    exact some (equal ▸ typed)
  else
    exact none

end DataGuardEncoding

/-- Dependency-ordered recursive guard commands, each linked to its exact
position in the completed production command array. -/
inductive CertifiedGuardTrace {signature : Signature} (emitted : Array Command) :
    Datatype.Env signature → Type where
  | nil : CertifiedGuardTrace emitted []
  | cons {entry : Datatype.Entry signature} {rest : Datatype.Env signature}
      (command : DataGuardCommand ⟨entry.arity, entry.block⟩)
      (commandIndex : Nat)
      (command_at : emitted[commandIndex]? = some command.command)
      (tail : CertifiedGuardTrace emitted rest) :
      CertifiedGuardTrace emitted (entry :: rest)

namespace CertifiedGuardTrace

/-- Reconnect retained production guard encodings to an exact intrinsic
datatype environment. -/
def ofEnv? {signature : Signature} (emitted : Array Command)
    (stored : Array DataGuardEncoding) (indices : Array Nat) :
    (env : Datatype.Env signature) → Option (CertifiedGuardTrace emitted env)
  | [] => some .nil
  | entry :: rest =>
      let owner : SomeBlock := ⟨entry.arity, entry.block⟩
      match stored.findFinIdx? (fun command =>
          (command.typedForOwner? owner).isSome) with
      | none => none
      | some position =>
        match stored[position].typedForOwner? owner,
            indices[position.val]?, ofEnv? emitted stored indices rest with
        | some command, some commandIndex, some tail =>
            match emittedEq : emitted[commandIndex]? with
            | some (.defFunsRec emittedDefs) =>
              match expectedEq : command.command with
              | .defFunsRec expectedDefs =>
                if defsEq : emittedDefs = expectedDefs then
                  have commandAt : emitted[commandIndex]? =
                      some command.command := by
                    rw [emittedEq, expectedEq, defsEq]
                  some (.cons command commandIndex commandAt tail)
                else none
              | _ => none
            | _ => none
        | _, _, _ => none

/-- Exact production recursive guard commands in dependency order. -/
def commands {signature : Signature} {emitted : Array Command} :
    {env : Datatype.Env signature} →
      CertifiedGuardTrace emitted env → Array Command
  | [], .nil => #[]
  | _ :: _, .cons command _ _ tail =>
      #[command.command] ++ commands tail

/-- Production-state positions of the recursive guard commands. -/
def indices {signature : Signature} {emitted : Array Command} :
    {env : Datatype.Env signature} →
      CertifiedGuardTrace emitted env → Array Nat
  | [], .nil => #[]
  | _ :: _, .cons _ commandIndex _ tail =>
      #[commandIndex] ++ indices tail

@[simp] theorem commands_size {signature : Signature}
    {env : Datatype.Env signature} {emitted : Array Command}
    (trace : CertifiedGuardTrace emitted env) :
    trace.commands.size = env.length := by
  induction trace with
  | nil => rfl
  | cons _ _ _ tail ih => simp [commands, ih, Nat.add_comm]

@[simp] theorem indices_size {signature : Signature}
    {env : Datatype.Env signature} {emitted : Array Command}
    (trace : CertifiedGuardTrace emitted env) :
    trace.indices.size = env.length := by
  induction trace with
  | nil => rfl
  | cons _ _ _ tail ih => simp [indices, ih, Nat.add_comm]

/-- Every retained recursive guard command is the command at its recorded
production-state position. -/
theorem commands_at {signature : Signature} {env : Datatype.Env signature}
    {emitted : Array Command} (trace : CertifiedGuardTrace emitted env)
    (position : Nat) :
    trace.indices[position]?.bind (fun index => emitted[index]?) =
      trace.commands[position]? := by
  induction trace generalizing position with
  | nil => simp [indices, commands]
  | cons command commandIndex commandAt tail ih =>
      cases position with
      | zero =>
          simpa [indices, commands, Array.getElem?_append] using commandAt
      | succ position =>
          simpa [indices, commands, Array.getElem?_append] using ih position

end CertifiedGuardTrace

/-- One fact-local datatype environment linked, in dependency order, to the
canonical native commands retained in the production state. This certifies the
datatype component only; surrounding legacy commands are intentionally absent. -/
structure CertifiedDataEnv where
  source : Lean.Expr
  env : DatatypeEnv
  tail : Signature
  bridge : SignatureBridge tail
  emitted : Array Command
  trace : CertifiedDataTrace emitted (DataBridge.of env tail).core
  guardTrace : CertifiedGuardTrace emitted (DataBridge.of env tail).core

namespace CertifiedDataEnv

/-- Construct a fact-local certificate only when every entry in its exact typed
environment is linked to a matching command in the supplied production state. -/
def build? (source : Lean.Expr) (env : DatatypeEnv) {tail : Signature}
    (bridge : SignatureBridge tail) (emitted : Array Command)
    (stored : Array CertifiedDataCommand) (indices : Array Nat)
    (storedGuards : Array DataGuardEncoding) (guardIndices : Array Nat) :
    Option CertifiedDataEnv := do
  let trace ← CertifiedDataTrace.ofEnv? emitted stored indices
    (DataBridge.of env tail).core
  let guardTrace ← CertifiedGuardTrace.ofEnv? emitted storedGuards guardIndices
    (DataBridge.of env tail).core
  return { source, env, tail, bridge, emitted, trace, guardTrace }

/-- Reconnect an existing fact-local certificate to a later production command
snapshot without changing its intrinsic environment. -/
def withCommands? (certificate : CertifiedDataEnv) (emitted : Array Command)
    (stored : Array CertifiedDataCommand) (indices : Array Nat)
    (storedGuards : Array DataGuardEncoding) (guardIndices : Array Nat) :
    Option CertifiedDataEnv := do
  let trace ← CertifiedDataTrace.ofEnv? emitted stored indices
    (DataBridge.of certificate.env certificate.tail).core
  let guardTrace ← CertifiedGuardTrace.ofEnv? emitted storedGuards guardIndices
    (DataBridge.of certificate.env certificate.tail).core
  return {
    source := certificate.source
    env := certificate.env
    tail := certificate.tail
    bridge := certificate.bridge
    emitted
    trace
    guardTrace }

/-- Complete intrinsic signature bridge used by this fact. -/
def signature (certificate : CertifiedDataEnv) :
    SignatureBridge (certificate.env.signature ++ certificate.tail) :=
  certificate.bridge.prepend certificate.env.signature

/-- The same datatype ownership environment consumed by the unified soundness
theorem. -/
def data (certificate : CertifiedDataEnv) :
    DataBridge (certificate.env.signature ++ certificate.tail) :=
  DataBridge.of certificate.env certificate.tail

/-- Native commands in dependency order, independent of their positions among
the other production commands. -/
def nativeCommands (certificate : CertifiedDataEnv) : Array Crush.SMT.Command :=
  certificate.trace.commands

/-- Production command positions corresponding to `nativeCommands`. -/
def commandIndices (certificate : CertifiedDataEnv) : Array Nat :=
  certificate.trace.indices

/-- Recursive datatype-guard commands in dependency order. -/
def guardCommands (certificate : CertifiedDataEnv) : Array Crush.SMT.Command :=
  certificate.guardTrace.commands

/-- Production positions corresponding to `guardCommands`. -/
def guardCommandIndices (certificate : CertifiedDataEnv) : Array Nat :=
  certificate.guardTrace.indices

@[simp] theorem nativeCommands_size (certificate : CertifiedDataEnv) :
    certificate.nativeCommands.size = certificate.env.blocks.size := by
  simp [nativeCommands]

@[simp] theorem commandIndices_size (certificate : CertifiedDataEnv) :
    certificate.commandIndices.size = certificate.env.blocks.size := by
  simp [commandIndices]

@[simp] theorem guardCommands_size (certificate : CertifiedDataEnv) :
    certificate.guardCommands.size = certificate.env.blocks.size := by
  simp [guardCommands]

@[simp] theorem guardCommandIndices_size (certificate : CertifiedDataEnv) :
    certificate.guardCommandIndices.size = certificate.env.blocks.size := by
  simp [guardCommandIndices]

/-- The native command list is an exact indexed subsequence of the retained
production command snapshot. -/
theorem nativeCommand_at (certificate : CertifiedDataEnv)
    (position : Nat) :
    certificate.commandIndices[position]?.bind
      (fun index => certificate.emitted[index]?) =
      certificate.nativeCommands[position]? := by
  exact certificate.trace.commands_at position

/-- The recursive guard command list is an exact indexed subsequence of the
retained production command snapshot. -/
theorem guardCommand_at (certificate : CertifiedDataEnv)
    (position : Nat) :
    certificate.guardCommandIndices[position]?.bind
      (fun index => certificate.emitted[index]?) =
      certificate.guardCommands[position]? := by
  exact certificate.guardTrace.commands_at position

/-- The single remaining semantic obligation for a certified production
datatype environment: every typed trace entry is represented by one shared FO
encoding, whose native command prefix is precisely the production-certified
list. This is a bridge into the generic SMT soundness theorem, not a second
datatype theorem. -/
structure Represents (certificate : CertifiedDataEnv)
    (fo : SMT.Encoding
      (Symbol (certificate.env.signature ++ certificate.tail))) where
  trace : certificate.trace.Represents fo
  native_eq : fo.nativeCommands = certificate.nativeCommands

/-- Exact semantic representation of the production recursive guard trace.
The native representation fixes every block and its datatype encoding; this
witness adds only the production guard syntax and command equality. -/
structure GuardRepresentation (certificate : CertifiedDataEnv)
    (guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail)))
    (represented : certificate.Represents guarding.encoding) where
  trace : SMT.Datatype.Native.Step.GuardTrace guarding represented.trace.blocks
  commands_eq : trace.commands = certificate.guardCommands

/-- Forget production provenance after entering the shared semantic theorem. -/
def Represents.env {certificate : CertifiedDataEnv}
    {fo : SMT.Encoding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents fo) :
    SMT.Datatype.EnvRepresentation fo certificate.data.core := {
  blocks := represented.trace.blocks
  native_eq := by
    calc
      fo.nativeCommands = certificate.nativeCommands := represented.native_eq
      _ = certificate.trace.commands := rfl
      _ = represented.trace.blocks.commands :=
        represented.trace.blocks_commands.symm }

/-- One source model's complete guarded target construction. The prior lifting
records interpreted base carriers (for example `Nat → Int`); the remaining
fields install the exact recursive datatype guards over the shared derived
graph. -/
structure GuardModel (certificate : CertifiedDataEnv)
    (guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail)))
    (represented : certificate.Represents guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented)
    (source : Model (certificate.env.signature ++ certificate.tail))
    (lawful : Datatype.Env.Lawful source certificate.data.core) where
  prior : Lifted (canonicalModel source)
  guards : SMT.UnaryGuards guarding.encoding
    (represented.env.liftedFrom source lawful prior).target
    (fun sort => ((represented.env.liftedFrom source lawful prior).relation
      sort).guard)
  base : SMT.ExtraGraph guarding.encoding
    (represented.env.liftedFrom source lawful prior).target
  baseUnique : Crush.SMT.ApplyUnique
    (SMT.modelWith guarding.encoding
      (represented.env.liftedFrom source lawful prior).target base)
  fresh : guards.Fresh base
  semantics : guarding.TermSemantics
    (represented.env.liftedFrom source lawful prior).target (guards.over base)
    (fun sort => ((represented.env.liftedFrom source lawful prior).relation
      sort).guard)
  linked : guarded.trace.Matches guards

namespace Represents

/-- The production representation validates its whole native datatype prefix
in the final dependency-folded target. -/
theorem lifted_valid {certificate : CertifiedDataEnv}
    {fo : SMT.Encoding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents fo)
    (source : Model (certificate.env.signature ++ certificate.tail))
    (lawful : Datatype.Env.Lawful source certificate.data.core) :
    (SMT.model fo (represented.env.lifted source lawful).target).SatisfiesCommands
      fo.nativeCommands :=
  represented.env.lifted_valid represented.trace.blocks_ordered source lawful

/-- Native validity over a caller-supplied interpreted or guarded base model. -/
theorem liftedFrom_valid {certificate : CertifiedDataEnv}
    {fo : SMT.Encoding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents fo)
    (source : Model (certificate.env.signature ++ certificate.tail))
    (lawful : Datatype.Env.Lawful source certificate.data.core)
    (prior : Lifted (canonicalModel source)) :
    (SMT.model fo
      (represented.env.liftedFrom source lawful prior).target).SatisfiesCommands
      fo.nativeCommands :=
  represented.env.liftedFrom_valid represented.trace.blocks_ordered
    source lawful prior

/-- Native datatype commands remain valid in the exact combined model used by
fresh `wf_T` predicates and interpreted arithmetic. -/
theorem lifted_valid_with {certificate : CertifiedDataEnv}
    {fo : SMT.Encoding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents fo)
    (source : Model (certificate.env.signature ++ certificate.tail))
    (lawful : Datatype.Env.Lawful source certificate.data.core)
    (extra : SMT.ExtraGraph fo (represented.env.lifted source lawful).target) :
    (SMT.modelWith fo (represented.env.lifted source lawful).target extra).SatisfiesCommands
      fo.nativeCommands :=
  represented.env.lifted_valid_with represented.trace.blocks_ordered
    source lawful extra

/-- Native validity with derived graphs over a caller-supplied base lifting. -/
theorem liftedFrom_valid_with {certificate : CertifiedDataEnv}
    {fo : SMT.Encoding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents fo)
    (source : Model (certificate.env.signature ++ certificate.tail))
    (lawful : Datatype.Env.Lawful source certificate.data.core)
    (prior : Lifted (canonicalModel source))
    (extra : SMT.ExtraGraph fo
      (represented.env.liftedFrom source lawful prior).target) :
    (SMT.modelWith fo (represented.env.liftedFrom source lawful prior).target
      extra).SatisfiesCommands fo.nativeCommands :=
  represented.env.liftedFrom_valid_with represented.trace.blocks_ordered
    source lawful prior extra

/-- The exact production recursive guard commands are simultaneously valid in
the final dependency-folded target and shared derived-symbol graph. -/
theorem guards_valid {certificate : CertifiedDataEnv}
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented)
    (source : Model (certificate.env.signature ++ certificate.tail))
    (lawful : Datatype.Env.Lawful source certificate.data.core)
    (prior : Lifted (canonicalModel source))
    (guards : SMT.UnaryGuards guarding.encoding
      (represented.env.liftedFrom source lawful prior).target
      (fun sort => ((represented.env.liftedFrom source lawful prior).relation
        sort).guard))
    (base : SMT.ExtraGraph guarding.encoding
      (represented.env.liftedFrom source lawful prior).target)
    (baseUnique : Crush.SMT.ApplyUnique
      (SMT.modelWith guarding.encoding
        (represented.env.liftedFrom source lawful prior).target base))
    (fresh : guards.Fresh base)
    (semantics : guarding.TermSemantics
      (represented.env.liftedFrom source lawful prior).target (guards.over base)
      (fun sort => ((represented.env.liftedFrom source lawful prior).relation
        sort).guard))
    (linked : guarded.trace.Matches guards) :
    (SMT.modelWith guarding.encoding
      (represented.env.liftedFrom source lawful prior).target
      (guards.over base)).SatisfiesCommands certificate.guardCommands := by
  rw [← guarded.commands_eq]
  simpa [SMT.Datatype.EnvRepresentation.liftedFrom, env,
    CertifiedDataEnv.data] using
    represented.trace.blocks_ordered.guards_valid guarded.trace source lawful
      prior guards base
      baseUnique fresh semantics linked

/-- One complete soundness theorem for a certified guarded datatype command
array. Native declarations, exact production-shaped `wf_T` definitions,
ordinary declarations, and guarded assertions are interpreted in the same raw
model. A caller may set `commands := certificate.emitted` when the surrounding
array has the stated guarded representation. -/
theorem sound {certificate : CertifiedDataEnv}
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented)
    (source : Model (certificate.env.signature ++ certificate.tail))
    (lawful : Datatype.Env.Lawful source certificate.data.core)
    (guardModel : certificate.GuardModel guarding represented guarded
      source lawful)
    {theory : FO.FamilyTheory
      (Symbol (certificate.env.signature ++ certificate.tail))}
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      certificate.guardCommands theory commands)
    (valid : (canonicalModel source).SatisfiesTheory theory) :
    ∃ model : Crush.SMT.Model, model.SatisfiesCommands commands := by
  apply SMT.guarded_lift guarding encoding (canonicalModel source)
    (represented.env.liftedFrom source lawful guardModel.prior).target
    (represented.env.liftedFrom source lawful guardModel.prior).relation
    (represented.env.liftedFrom source lawful guardModel.prior).models valid
    (guardModel.guards.over guardModel.base) guardModel.semantics.toSemantics
  · exact represented.liftedFrom_valid_with source lawful guardModel.prior
      (guardModel.guards.over guardModel.base)
  · exact represented.guards_valid guarded source lawful guardModel.prior
      guardModel.guards guardModel.base guardModel.baseUnique guardModel.fresh
      guardModel.semantics guardModel.linked

/-- Semantic unsatisfiability under the exact combined model contract. Unlike
ordinary datatype unsatisfiability, this contract can restrict opaque source
base carriers through an interpreted prior such as `Nat → Int`. -/
theorem unsat_under {certificate : CertifiedDataEnv}
    {guarding : SMT.Guarding
      (Symbol (certificate.env.signature ++ certificate.tail))}
    (represented : certificate.Represents guarding.encoding)
    (guarded : certificate.GuardRepresentation guarding represented)
    (formula : Sentence
      (certificate.env.signature ++ certificate.tail))
    {commands : Array Crush.SMT.Command}
    (encoding : SMT.GuardedTheoryRepresentation guarding
      certificate.guardCommands (translatedTheory formula) commands)
    (unsat : Crush.SMT.CommandsUnsatisfiable commands) :
    UnsatisfiableUnder
      (fun source =>
        Σ lawful : Datatype.Env.Lawful source certificate.data.core,
          certificate.GuardModel guarding represented guarded source lawful)
      formula := by
  intro source model sourceValid
  rcases model with ⟨lawful, guardModel⟩
  obtain ⟨target, valid⟩ := represented.sound guarded source lawful
    guardModel encoding (model_extension source formula sourceValid)
  exact unsat target valid

end Represents

end CertifiedDataEnv

end Crush.Metatheory.VCG
