import Crush.Metatheory.VCG.Generate
import Crush.Metatheory.VCG.Datatype
import Crush.Translation.Monad

/-!
# Total stateful VCG

`run` is the proved production route after successful Lean-to-HO reification.
It installs the pure encoder's exact command sequence in a fresh translation
state.  The legacy `emitTerm` route remains explicitly trusted because it
translates `Lean.Expr` directly and permits unrestricted extension handlers.
-/

namespace Crush.Metatheory.VCG

open Defunctionalization.Flattened

/-- An emitted state contains exactly the command sequence representing one
intrinsic translated theory. -/
structure StateRepresents {signature : Signature}
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) (state : TranslateState) : Prop where
  commands_eq : state.commands = commands encoding source
  representation :
    SMT.TheoryRepresentation encoding (translatedTheory source) state.commands

/-- Total stateful VCG after successful structural reification.  All mutable
translation bookkeeping starts fresh, so the resulting state cannot inherit a
trusted fallback or commands from an earlier direct run. -/
def run {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) : TranslateState :=
  { cfg, commands := commands encoding source }

@[simp] theorem run_commands {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) :
    (run cfg encoding source).commands = commands encoding source := rfl

@[simp] theorem run_proved {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) :
    (run cfg encoding source).status = .proved := by
  simp [run, TranslateState.status]

/-- The actual state returned by total VCG represents the complete intrinsic
theory, in its exact emitted order. -/
theorem run_represents {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) :
    StateRepresents encoding source (run cfg encoding source) := by
  exact ⟨rfl, commands_represents encoding source⟩

/-- Native commands form the first segment of the exact pure VCG array. All
remaining sort declarations, ordinary declarations, and assertions share the
same encoding and follow that segment. -/
theorem commands_native_prefix {signature : Signature}
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) :
    ∃ suffix, commands encoding source = encoding.nativeCommands ++ suffix := by
  exact ⟨commandBody encoding source, commands_split encoding source⟩

/-- The exact state returned by `run` carries a dependency-aligned typed trace
of every native datatype command. No second name allocator is involved: the
single encoding's global injectivity and freshness fields cover native and
ordinary symbols together. -/
def run_dataTrace {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) {env : Datatype.Env signature}
    (represented : SMT.Datatype.EnvRepresentation encoding env) :
    CertifiedDataTrace (run cfg encoding source).commands env := by
  apply CertifiedDataTrace.fromPrefix represented.blocks
    (suffix := commandBody encoding source)
  rw [run_commands, commands_split, represented.native_eq]

/-! ## Guarded stateful VCG -/

/-- Total stateful route for an intrinsic guarded theory and its exact certified
derived-command segment. -/
def runGuarded {signature : Signature} (cfg : Config)
    (guarding : SMT.Guarding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Sentence signature) :
    TranslateState :=
  { cfg, commands := guardedCommands guarding derived source }

@[simp] theorem runGuarded_commands {signature : Signature} (cfg : Config)
    (guarding : SMT.Guarding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Sentence signature) :
    (runGuarded cfg guarding derived source).commands =
      guardedCommands guarding derived source := rfl

@[simp] theorem runGuarded_proved {signature : Signature} (cfg : Config)
    (guarding : SMT.Guarding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Sentence signature) :
    (runGuarded cfg guarding derived source).status = .proved := by
  simp [runGuarded, TranslateState.status]

/-- The exact guarded state array represents the translated intrinsic theory. -/
theorem runGuarded_represents {signature : Signature} (cfg : Config)
    (guarding : SMT.Guarding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Sentence signature) :
    SMT.GuardedTheoryRepresentation guarding derived (translatedTheory source)
      (runGuarded cfg guarding derived source).commands := by
  simpa using guardedCommands_represents guarding derived source

/-- Native datatype identity and dependency order are retained inside the exact
guarded state array. -/
def runGuarded_dataTrace {signature : Signature} (cfg : Config)
    (guarding : SMT.Guarding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Sentence signature)
    {env : Datatype.Env signature}
    (represented : SMT.Datatype.EnvRepresentation guarding.encoding env) :
    CertifiedDataTrace (runGuarded cfg guarding derived source).commands env := by
  apply CertifiedDataTrace.fromPrefix represented.blocks
    (suffix := derived ++ guarding.theoryBody
      (𝓕⟦source⟧.declarations.map SMT.ofDeclared)
      (translatedTheory source))
  simp [runGuarded, guardedCommands, SMT.Guarding.theory,
    represented.native_eq]

/-! ## Finite source theories -/

/-- An emitted state contains exactly the commands representing one finite
intrinsic source theory. -/
structure TheoryStateRepresents {signature : Signature}
    (encoding : SMT.Encoding (Symbol signature))
    (source : Theory signature) (state : TranslateState) : Prop where
  commands_eq : state.commands = theoryCommands encoding source
  representation : SMT.TheoryRepresentation encoding
    (translatedTheories source) state.commands

/-- Total stateful VCG for a finite theory sharing one intrinsic signature. -/
def runTheory {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Theory signature) : TranslateState :=
  { cfg, commands := theoryCommands encoding source }

@[simp] theorem runTheory_commands {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Theory signature) :
    (runTheory cfg encoding source).commands = theoryCommands encoding source := rfl

theorem runTheory_represents {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Theory signature) :
    TheoryStateRepresents encoding source (runTheory cfg encoding source) :=
  ⟨rfl, theoryCommands_represents encoding source⟩

/-- Total guarded stateful VCG for a finite theory. -/
def runGuardedTheory {signature : Signature} (cfg : Config)
    (guarding : SMT.Guarding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Theory signature) :
    TranslateState :=
  { cfg, commands := guardedTheoryCommands guarding derived source }

@[simp] theorem runGuardedTheory_commands {signature : Signature} (cfg : Config)
    (guarding : SMT.Guarding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Theory signature) :
    (runGuardedTheory cfg guarding derived source).commands =
      guardedTheoryCommands guarding derived source := rfl

theorem runGuardedTheory_represents {signature : Signature} (cfg : Config)
    (guarding : SMT.Guarding (Symbol signature))
    (derived : Array Crush.SMT.Command) (source : Theory signature) :
    SMT.GuardedTheoryRepresentation guarding derived (translatedTheories source)
      (runGuardedTheory cfg guarding derived source).commands :=
  guardedTheoryCommands_represents guarding derived source

end Crush.Metatheory.VCG
