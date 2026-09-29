import Lean
import Crush.Solver.Replay.Format
open Lean

/-!
# Configuration options for lean-crush

Every knob is a real `register_option` so it participates in `set_option`,
tab-completion, and `#help option`. Options are grouped by subsystem with the
`crush.*` prefix. The tactic reads these into a `Crush.Config` record once at
entry (see `Crush/Frontend/Tactic.lean`) so downstream code passes a value
rather than repeatedly touching the option environment.
-/

namespace Crush

/-- Which backend family to target. Selects the concrete solver process and the
translation profile (logic string, theory availability). -/
inductive Backend where
  | z3
  | cvc5
  | bitwuzla
  /-- Emit an SMT-LIB script only; do not spawn a solver. -/
  | none
  deriving BEq, Hashable, Inhabited, Repr

instance : ToString Backend where
  toString
    | .z3 => "z3" | .cvc5 => "cvc5" | .bitwuzla => "bitwuzla" | .none => "none"

/-- Every backend value. Kept beside the constructors so a new one is added here too. -/
def Backend.all : Array Backend := #[.z3, .cvc5, .bitwuzla, .none]

instance : KVMap.Value Backend where
  toDataValue b := toString b
  ofDataValue?
    | "z3" => some .z3 | "cvc5" => some .cvc5
    | "bitwuzla" => some .bitwuzla | "none" => some .none
    | _ => none

/-- How to treat a solver `unsat` result. -/
inductive TrustMode where
  /-- Close the goal with the `crushSorry` axiom (fast, unsound-by-trust). The default. -/
  | trust
  /-- Attempt to reconstruct a checkable Lean proof; error if reconstruction fails,
  so the `crushSorry` axiom is never used. -/
  | reconstruct
  /-- Reconstruct if possible, else fall back to trust with a warning. -/
  | reconstructOrTrust
  deriving BEq, Hashable, Inhabited, Repr

instance : ToString TrustMode where
  toString
    | .trust => "trust" | .reconstruct => "reconstruct"
    | .reconstructOrTrust => "reconstructOrTrust"

instance : KVMap.Value TrustMode where
  toDataValue m := toString m
  ofDataValue?
    | "trust" => some .trust | "reconstruct" => some .reconstruct
    | "reconstructOrTrust" => some .reconstructOrTrust
    | _ => none

/-- Certificate selection and core-guided reconstruction. -/
inductive ReconstructMode where
  /-- Alethe replay on cvc5, followed by core-guided reconstruction. -/
  | auto
  /-- Alethe replay, with core fallback unless explicitly disabled. -/
  | alethe
  /-- CPC replay, with core fallback unless explicitly disabled. -/
  | cpc
  /-- Core-guided reconstruction without certificate replay. -/
  | core
  deriving BEq, Hashable, Inhabited, Repr

instance : ToString ReconstructMode where
  toString
    | .auto => "auto" | .alethe => "alethe" | .cpc => "cpc" | .core => "core"

instance : KVMap.Value ReconstructMode where
  toDataValue m := toString m
  ofDataValue?
    | "auto" => some .auto | "alethe" | "Alethe" => some .alethe
    | "cpc" | "CPC" => some .cpc | "core" => some .core
    | _ => none

/-- The requested certificate format; automatic mode preserves Alethe selection. -/
def ReconstructMode.format : ReconstructMode → ReplayFormat
  | .cpc => .cpc
  | _ => .alethe

/-- Strategy for eliminating higher-order features before hitting first-order SMT. -/
inductive HOMode where
  /-- Monomorphize + lambda-lift + defunctionalize applied HO args (default). -/
  | defunctionalize
  /-- Pass HO constructs straight to a HO-capable solver (cvc5 `--ho`). -/
  | native
  deriving BEq, Hashable, Inhabited, Repr

instance : ToString HOMode where
  toString
    | .defunctionalize => "defunctionalize"
    | .native => "native"

instance : KVMap.Value HOMode where
  toDataValue m := toString m
  ofDataValue?
    | "defunctionalize" => some .defunctionalize
    | "native" => some .native
    | _ => none

end Crush

open Crush

register_option crush.backend : Backend := {
  defValue := Backend.z3
  descr := "SMT backend to invoke: z3, cvc5, bitwuzla, or none (emit script only)."
}

register_option crush.timeout : Nat := {
  defValue := 10
  descr := "Per-query solver wall-clock timeout in seconds. Enforced by lean-crush \
            in addition to the solver's own limit, so a hung solver is always killed."
}

register_option crush.trust : TrustMode := {
  defValue := TrustMode.trust
  descr := "How to discharge the goal on `unsat`: trust (default), reconstruct, or \
            reconstructOrTrust. On solver `unsat`, trust closes with `Crush.crushSorry`, \
            trusting the solver and translation. Reconstruct requires a checked proof and \
            fails if none is found; reconstructOrTrust allows a warned trusted fallback. \
            A trusted discharge records `Crush.crushSorry` in `#print axioms`. Checked \
            proofs found before SMT do not use this fallback, even under trust."
}

register_option crush.ho.mode : HOMode := {
  defValue := HOMode.defunctionalize
  descr := "Higher-order elimination strategy: defunctionalize or native."
}

register_option crush.mono.fuel : Nat := {
  defValue := 512
  descr := "Maximum number of monomorphization instances generated before giving up."
}

register_option crush.mono.rounds : Nat := {
  defValue := 8
  descr := "Maximum saturation rounds for the monomorphization E-matching loop."
}

register_option crush.mono.certify : Bool := {
  defValue := false
  descr := "Type-check each generated monomorphization instance (its proof term must \
            have its proposition) and drop any that fail. Off by default: under the \
            `reconstruct` policy the kernel re-checks the proof during replay anyway, \
            so this only adds value under `trust`/`reconstructOrTrust`, where it turns \
            the pass's soundness from argued into checked at each call."
}

register_option crush.inst.fuel : Nat := {
  defValue := 128
  descr := "Maximum number of proof-producing ground term instances generated from \
            explicit hints and selected premises before translation."
}

register_option crush.inst.rounds : Nat := {
  defValue := 3
  descr := "Maximum saturation rounds for ground term instantiation. Set either \
            this option or `crush.inst.fuel` to 0 to disable the pass."
}

register_option crush.save : String := {
  defValue := ""
  descr := "If nonempty, write the generated SMT-LIB script to this path before solving."
}

register_option crush.additionalArgs : String := {
  defValue := ""
  descr := "Extra space-separated command-line flags passed verbatim to the solver."
}

register_option crush.logic : String := {
  defValue := ""
  descr := "Override the auto-detected SMT-LIB logic string (e.g. \"UFNIA\"). Empty = auto."
}

register_option crush.trace.script : Bool := {
  defValue := false
  descr := "Log the full generated SMT-LIB script as an info message."
}

register_option crush.autoUnfold : Bool := {
  defValue := true
  descr := "Automatically fold the equation lemmas of `@[crush_unfold]`/`@[crush_defeq]` \
            definitions reachable from the goal into each query (like always-on u[…]/d[…])."
}

register_option crush.preReconstruct.ruleSearch : Bool := {
  defValue := false
  descr := "In the pre-SMT pass, search the selected facts for a backward rule that \
            closes the goal, discharging the premises it generates with bounded Lean \
            automation. Disabled by default: the pass then applies only a selected \
            universal rule that closes the goal outright, generating no premises. The \
            rest of the pass — empty-inductive elimination, existential witnesses, the \
            datatype split — runs either way. Both settings apply under every trust \
            policy, so the stages up to the solver call do not depend on whether a \
            kernel-checked proof is required. Enabling it closes goals the solver would \
            otherwise have to reach, and spends time on searches that fail."
}

register_option crush.reconstruct : ReconstructMode := {
  defValue := ReconstructMode.auto
  descr := "Reconstruction path: auto (Alethe on cvc5, then core reconstruction), \
            alethe, cpc, or core. Explicit Alethe and CPC modes require cvc5 and \
            default to checked core-guided fallback when replay fails."
}

register_option crush.reconstruct.fallback : Bool := {
  defValue := true
  descr := "After certificate replay fails, try checked core-guided reconstruction. \
            Set false with alethe or cpc to require replay and bypass pre-SMT proof \
            shortcuts. This does not enable trusting an unreplayed certificate."
}

register_option crush.reconstruct.trustBvDecide : Bool := {
  defValue := false
  descr := "Allow reconstruction tactics to use `bv_decide`. This trusts the native \
            code generator used to check `bv_decide`'s LRAT certificate and records an \
            auditable `_native.bv_decide.ax_*` dependency. Disabled by default, so \
            reconstruction otherwise accepts only kernel-checkable generated declarations."
}

register_option crush.reconstruct.trustNativeDecide : Bool := {
  defValue := false
  descr := "Allow core reconstruction to use `native_decide`. This trusts Lean's native \
            compiler, runtime, and the executable definitions reached by the decision \
            procedure, and records an auditable `_native.native_decide.ax_*` dependency. \
            Disabled by default."
}

register_option crush.profile : Bool := {
  defValue := false
  descr := "Log a per-phase wall-clock breakdown of the tactic (collect, normalize, \
            monomorphize, instantiate, translate, solve, reconstruct) as an info \
            message, to find where time goes."
}

register_option crush.profile.machine : Bool := {
  defValue := false
  descr := "When `crush.profile` is enabled, also print one machine-readable TSV record \
            containing the declaration, goal hash, outcome, reconstruction status, and \
            nanoseconds spent in each phase. Intended for benchmark tooling."
}

register_option crush.premises : Bool := {
  defValue := false
  descr := "Use Lean's registered LibrarySuggestions engine to add relevant library \
            theorems to bare `crush` calls. Explicit `[...]` lists remain strict \
            restrictions and disable automatic premise selection."
}

register_option crush.premises.max : Nat := {
  defValue := 32
  descr := "Maximum number of LibrarySuggestions premises added when \
            `crush.premises` is enabled."
}

namespace Crush

/-- Resolved configuration, read once from the option environment at tactic entry. -/
structure Config where
  backend        : Backend   := .z3
  timeout        : Nat       := 10
  trust          : TrustMode := .trust
  hoMode         : HOMode    := .defunctionalize
  monoFuel       : Nat       := 512
  monoRounds     : Nat       := 8
  monoCertify    : Bool      := false
  instFuel       : Nat       := 128
  instRounds     : Nat       := 3
  savePath       : String    := ""
  additionalArgs : Array String := #[]
  logic          : Option String := none
  traceScript    : Bool      := false
  autoUnfold     : Bool      := true
  preRuleSearch  : Bool      := false
  reconstruct    : ReconstructMode := .auto
  reconstructFallback : Bool := true
  trustBvDecide  : Bool      := false
  trustNativeDecide : Bool   := false
  profile        : Bool      := false
  profileMachine : Bool      := false
  premises       : Bool      := false
  premiseMax     : Nat       := 32
  deriving Inhabited

/-- Read the current option environment into a `Config`. -/
def Config.ofOptions (opts : Options) : Config :=
  let split (s : String) : Array String :=
    (s.splitOn " ").toArray.filterMap (fun w =>
      let w := w.trimAscii.toString
      if w.isEmpty then none else some w)
  let logicStr := crush.logic.get opts
  { backend        := crush.backend.get opts
    timeout        := crush.timeout.get opts
    trust          := crush.trust.get opts
    hoMode         := crush.ho.mode.get opts
    monoFuel       := crush.mono.fuel.get opts
    monoRounds     := crush.mono.rounds.get opts
    monoCertify    := crush.mono.certify.get opts
    instFuel       := crush.inst.fuel.get opts
    instRounds     := crush.inst.rounds.get opts
    savePath       := crush.save.get opts
    additionalArgs := split (crush.additionalArgs.get opts)
    logic          := if logicStr.isEmpty then none else some logicStr
    traceScript    := crush.trace.script.get opts
    autoUnfold     := crush.autoUnfold.get opts
    preRuleSearch  := crush.preReconstruct.ruleSearch.get opts
    reconstruct    := crush.reconstruct.get opts
    reconstructFallback := crush.reconstruct.fallback.get opts
    trustBvDecide  := crush.reconstruct.trustBvDecide.get opts
    trustNativeDecide := crush.reconstruct.trustNativeDecide.get opts
    profile        := crush.profile.get opts
    profileMachine := crush.profile.machine.get opts
    premises       := crush.premises.get opts
    premiseMax     := crush.premises.max.get opts }

end Crush
