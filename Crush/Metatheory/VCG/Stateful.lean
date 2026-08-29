import Crush.Metatheory.VCG.Generate
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
    (source : Sentence signature) : TranslationStatus encoding × TranslateState :=
  (generate encoding source, { cfg, commands := commands encoding source })

@[simp] theorem run_status {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) :
    (run cfg encoding source).1 = generate encoding source := rfl

@[simp] theorem run_commands {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) :
    (run cfg encoding source).2.commands = commands encoding source := rfl

@[simp] theorem run_proved {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) :
    (run cfg encoding source).2.status = .proved := by
  simp [run, TranslateState.status]

/-- The actual state returned by total VCG represents the complete intrinsic
theory, in its exact emitted order. -/
theorem run_represents {signature : Signature} (cfg : Config)
    (encoding : SMT.Encoding (Symbol signature))
    (source : Sentence signature) :
    StateRepresents encoding source (run cfg encoding source).2 := by
  exact ⟨rfl, commands_represents encoding source⟩

end Crush.Metatheory.VCG
