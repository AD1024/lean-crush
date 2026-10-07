import Crush

/-!
An invalid string option must fail before any proof search, including on a goal
that preprocessing can close without a solver. In particular, misspelling
`reconstruct` must never fall back to the default `trust` policy.
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
  let _ ← Crush.Config.ofOptions (({} : Lean.Options).setBool `crush.trust true)
  pure ()

-- Every accepted value, and the absence of explicit options, retain their meaning.
#eval show Lean.MetaM Unit from do
  let defaults ← Crush.Config.ofOptions {}
  unless defaults.backend == .z3 && defaults.trust == .trust &&
      defaults.hoMode == .defunctionalize && defaults.reconstruct == .auto do
    throwError "default crush configuration changed"
  for value in Crush.Backend.all do
    let cfg ← Crush.Config.ofOptions (({} : Lean.Options).set `crush.backend (toString value))
    unless cfg.backend == value do throwError "backend option parsed incorrectly"
  for value in #[Crush.TrustMode.trust, .reconstruct, .reconstructOrTrust] do
    let cfg ← Crush.Config.ofOptions (({} : Lean.Options).set `crush.trust (toString value))
    unless cfg.trust == value do throwError "trust option parsed incorrectly"
  for value in #[Crush.HOMode.defunctionalize, .native] do
    let cfg ← Crush.Config.ofOptions (({} : Lean.Options).set `crush.ho.mode (toString value))
    unless cfg.hoMode == value do throwError "higher-order option parsed incorrectly"
  for value in #[Crush.ReconstructMode.auto, .alethe, .core] do
    let cfg ← Crush.Config.ofOptions (({} : Lean.Options).set `crush.reconstruct (toString value))
    unless cfg.reconstruct == value do throwError "reconstruction option parsed incorrectly"
