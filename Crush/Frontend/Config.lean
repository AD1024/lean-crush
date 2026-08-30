import Lean
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

/-- Which reconstruction path(s) to use under a reconstructing `TrustMode`.

There are two independent ways to turn an `unsat` into a Lean proof, with different
reach, so this selects between them:

* replaying the solver's proof certificate step by step (`Crush/Solver/AletheReplay.lean`),
  which needs cvc5 and handles long inference chains;
* the core-directed finisher ladder (`Crush/Solver/Reconstruct.lean`), which requires a
  backend-provided unsat core and one Lean tactic to re-find the whole argument. -/
inductive ReconstructMode where
  /-- Try Alethe certificate replay first, then the finisher ladder. The default: replay
  reaches goals the ladder cannot, and declining is cheap, so trying both closes the most. -/
  | auto
  /-- Alethe certificate replay only; do not fall back to the ladder. For working on replay
  itself, where a silent fallback would mask whether replay actually succeeded. -/
  | alethe
  /-- Core-directed finisher ladder only; ignore any certificate. Also what a backend
  that emits no Alethe proof (z3) effectively gets. -/
  | core
  deriving BEq, Hashable, Inhabited, Repr

instance : ToString ReconstructMode where
  toString
    | .auto => "auto" | .alethe => "alethe" | .core => "core"

instance : KVMap.Value ReconstructMode where
  toDataValue m := toString m
  ofDataValue?
    | "auto" => some .auto | "alethe" => some .alethe | "core" => some .core
    | _ => none

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
            reconstructOrTrust. The default closes the goal with the `crushSorry` axiom, \
            trusting the solver and the translation. Set `reconstruct` to demand a kernel-checked \
            proof and error if none is found (so no axiom is ever used), or \
            `reconstructOrTrust` to try that first and fall back with a warning. Any \
            theorem closed under `trust` names `crushSorry` in `#print axioms`."
}

register_option crush.ho.mode : HOMode := {
  defValue := HOMode.defunctionalize
  descr := "Higher-order elimination strategy: defunctionalize or native."
}

register_option crush.datatype.certify : Bool := {
  defValue := false
  descr := "Certify datatype discovery, typed ownership, and native declarations. Disabled \
            by default so existing production datatype behavior and benchmarks remain \
            unchanged while certified fragment coverage is expanded."
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

register_option crush.reconstruct : ReconstructMode := {
  defValue := ReconstructMode.auto
  descr := "Which reconstruction path to use when `crush.trust` asks for one: auto \
            (default — try the Alethe certificate, then the finisher ladder), alethe \
            (cvc5 Alethe certificate only, no ladder fallback), or core (finisher ladder \
            only, ignoring any certificate). Both paths end in a kernel-checked term and \
            neither can close a goal on the solver's word; they differ in reach. Alethe \
            replay handles long chains of trivial inferences (Boolean pigeonhole, deep EUF \
            conflicts) but needs cvc5 ≥ 1.3; the ladder needs one Lean tactic to re-find \
            the whole argument and an unsat core (available from Z3 and cvc5, but not \
            currently Bitwuzla). Under `alethe`, a goal whose \
            certificate cannot be replayed fails rather than falling back — useful when \
            working on replay itself, where a silent fallback hides whether it worked."
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
  certifyDatatype : Bool     := false
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
  reconstruct    : ReconstructMode := .auto
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
    certifyDatatype := crush.datatype.certify.get opts
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
    reconstruct    := crush.reconstruct.get opts
    trustBvDecide  := crush.reconstruct.trustBvDecide.get opts
    trustNativeDecide := crush.reconstruct.trustNativeDecide.get opts
    profile        := crush.profile.get opts
    profileMachine := crush.profile.machine.get opts
    premises       := crush.premises.get opts
    premiseMax     := crush.premises.max.get opts }

end Crush
