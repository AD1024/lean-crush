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

instance : KVMap.Value Backend where
  toDataValue b := toString b
  ofDataValue?
    | "z3" => some .z3 | "cvc5" => some .cvc5
    | "bitwuzla" => some .bitwuzla | "none" => some .none
    | _ => none

/-- How to treat a solver `unsat` result. -/
inductive TrustMode where
  /-- Close the goal with the `crushSorry` axiom (fast, unsound-by-trust). -/
  | trust
  /-- Attempt to reconstruct a checkable Lean proof; error if reconstruction fails,
  so the `crushSorry` axiom is never used. The default. -/
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

/-- Strategy for eliminating higher-order features before hitting first-order SMT. -/
inductive HOMode where
  /-- Monomorphize + lambda-lift + defunctionalize applied HO args (default). -/
  | defunctionalize
  /-- Use S/K/B/C/W combinators for lambdas, with their defining equations. -/
  | combinators
  /-- Pass HO constructs straight to a HO-capable solver (cvc5 `--ho`). -/
  | native
  deriving BEq, Hashable, Inhabited, Repr

instance : ToString HOMode where
  toString
    | .defunctionalize => "defunctionalize"
    | .combinators => "combinators" | .native => "native"

instance : KVMap.Value HOMode where
  toDataValue m := toString m
  ofDataValue?
    | "defunctionalize" => some .defunctionalize
    | "combinators" => some .combinators | "native" => some .native
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
  defValue := TrustMode.reconstruct
  descr := "How to discharge the goal on `unsat`: trust, reconstruct (default), or \
            reconstructOrTrust. The default never uses the `crushSorry` axiom — a goal \
            the finishers cannot replay is an error, so a translation bug that yields a \
            false `unsat` cannot silently close a false goal. Opt into the axiom fallback \
            with `reconstructOrTrust`, or skip reconstruction entirely with `trust`."
}

register_option crush.ho.mode : HOMode := {
  defValue := HOMode.defunctionalize
  descr := "Higher-order elimination strategy: defunctionalize, combinators, or native."
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

namespace Crush

/-- Resolved configuration, read once from the option environment at tactic entry. -/
structure Config where
  backend        : Backend   := .z3
  timeout        : Nat       := 10
  trust          : TrustMode := .reconstruct
  hoMode         : HOMode    := .defunctionalize
  monoFuel       : Nat       := 512
  monoRounds     : Nat       := 8
  monoCertify    : Bool      := false
  savePath       : String    := ""
  additionalArgs : Array String := #[]
  logic          : Option String := none
  traceScript    : Bool      := false
  autoUnfold     : Bool      := true
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
    savePath       := crush.save.get opts
    additionalArgs := split (crush.additionalArgs.get opts)
    logic          := if logicStr.isEmpty then none else some logicStr
    traceScript    := crush.trace.script.get opts
    autoUnfold     := crush.autoUnfold.get opts }

end Crush
