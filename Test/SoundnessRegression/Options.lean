import Crush

/-!
Invalid option strings or raw values must fail before proof search, even on trivial
goals. Misspelling reconstruct must never select the default trust policy. The pure
parser retains errors through record updates, and direct callers validate their
supplied configuration independently of ambient options.
-/

/-- error: crush: invalid value 'Reconstruct' for option 'crush.trust'; expected trust, reconstruct, or reconstructOrTrust -/
#guard_msgs in
set_option crush.trust "Reconstruct" in
example : True := by crush

/-- error: crush: invalid value 'reconstrut' for option 'crush.trust'; expected trust, reconstruct, or reconstructOrTrust -/
#guard_msgs in
set_option crush.trust "reconstrut" in
example : True := by crush

/-- error: crush: invalid value 'CVC5' for option 'crush.backend'; expected z3, cvc5, bitwuzla, or none -/
#guard_msgs in
set_option crush.backend "CVC5" in
example : True := by crush

/-- error: crush: invalid value 'alethee' for option 'crush.reconstruct'; expected auto, alethe, or core -/
#guard_msgs in
set_option crush.reconstruct "alethee" in
example : True := by crush

/-- error: crush: invalid value 'Native' for option 'crush.ho.mode'; expected defunctionalize or native -/
#guard_msgs in
set_option crush.ho.mode "Native" in
example : True := by crush

-- Metaprograms can insert values of the wrong raw type, bypassing `set_option`.
/-- error: crush: invalid value 'true' for option 'crush.trust'; expected trust, reconstruct, or reconstructOrTrust -/
#guard_msgs in
#eval show Lean.MetaM Unit from do
  let _ ← Crush.Config.ofOptionsChecked (({} : Lean.Options).setBool `crush.trust true)
  pure ()

-- Positive controls cover defaults and every accepted enum value.
#eval show Lean.MetaM Unit from do
  let defaults := Crush.Config.ofOptions {}
  defaults.validate
  unless defaults.backend == .z3 && defaults.trust == .trust &&
      defaults.hoMode == .defunctionalize && defaults.reconstruct == .auto do
    throwError "default crush configuration changed"
  for value in Crush.Backend.all do
    let cfg := Crush.Config.ofOptions (({} : Lean.Options).set `crush.backend (toString value))
    cfg.validate
    unless cfg.backend == value do throwError "backend option parsed incorrectly"
  for value in #[Crush.TrustMode.trust, .reconstruct, .reconstructOrTrust] do
    let cfg := Crush.Config.ofOptions (({} : Lean.Options).set `crush.trust (toString value))
    cfg.validate
    unless cfg.trust == value do throwError "trust option parsed incorrectly"
  for value in #[Crush.HOMode.defunctionalize, .native] do
    let cfg := Crush.Config.ofOptions (({} : Lean.Options).set `crush.ho.mode (toString value))
    cfg.validate
    unless cfg.hoMode == value do throwError "higher-order option parsed incorrectly"
  for value in #[Crush.ReconstructMode.auto, .alethe, .core] do
    let cfg := Crush.Config.ofOptions (({} : Lean.Options).set `crush.reconstruct (toString value))
    cfg.validate
    unless cfg.reconstruct == value do throwError "reconstruction option parsed incorrectly"

namespace SoundnessOptions

open Lean Elab Tactic

-- Pin the pure parser type used by downstream metaprograms.
def parseOptions : Options → Crush.Config := Crush.Config.ofOptions

elab "crushBadParsedConfig" : tactic => do
  let cfg := parseOptions (({} : Options).set `crush.trust "Reconstruct")
  -- Record updates used by direct callers must preserve the parse failure.
  let cfg := { cfg with timeout := 1 }
  Crush.runCrush (← getMainGoal) cfg

-- Valid ambient options must not hide an error in the supplied configuration.
/-- error: crush: invalid value 'Reconstruct' for option 'crush.trust'; expected trust, reconstruct, or reconstructOrTrust -/
#guard_msgs in
example : True := by crushBadParsedConfig

elab "crushBadRawConfig" : tactic => do
  let cfg := parseOptions (({} : Options).setBool `crush.backend true)
  Crush.runCrush (← getMainGoal) cfg

/-- error: crush: invalid value 'true' for option 'crush.backend'; expected z3, cvc5, bitwuzla, or none -/
#guard_msgs in
example : True := by crushBadRawConfig

elab "crushValidConfig" : tactic => do
  let cfg := parseOptions (({} : Options).set `crush.trust "reconstruct")
  Crush.runCrush (← getMainGoal) cfg

-- Invalid ambient options must not override a valid explicit configuration.
set_option crush.trust "Reconstruct" in
example : True := by crushValidConfig

end SoundnessOptions
