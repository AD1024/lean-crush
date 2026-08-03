import Crush

/-!
Smoke tests for the lean-crush skeleton. These do not exercise the (not-yet-built)
reification pipeline; they check that the foundational layers compile and behave:
the SMT IR printer, the `@[crush_translate]` extension mechanism, the `crush_map`
sugar, config parsing, and a live solver round-trip.
-/

open Crush Crush.SMT

/-- IR printing round-trip. -/
def demoScript : Array Command := #[
  .setLogic "QF_UF",
  .declSort "U" 0,
  .declFun "f" #[.app (.symb "U") #[]] (.app (.symb "U") #[]),
  .declFun "a" #[] (.app (.symb "U") #[]),
  .assert (.app (.symb "=") #[.symbApp "f" #[.const "a"], .const "a"]),
  .assert (.forallE #[("x", .app (.symb "U") #[])]
            (.annot (.app (.symb "=") #[.symbApp "f" #[.bvar 0], .bvar 0]) #[.named "ax"])),
  .checkSat
]

/-- info: (set-logic QF_UF) -/
#guard_msgs in
#eval IO.println (commandToString demoScript[0]!)

#eval do
  IO.println "--- generated script ---"
  IO.println (scriptToString demoScript)

-- Extension mechanism: register a handler two ways and confirm both are found.

/-- A hand-written handler that maps `Nat.succ n` to `(+ n 1)`. -/
@[crush_translate high]
def succHandler : TranslationHandler := fun ctx => do
  let .const ``Nat.succ _ := ctx.fn | return none
  match ctx.args with
  | #[n] => return some (.app (.symb "+") #[← ctx.emitTerm n, .lit (.num 1)])
  | _ => return none

-- Sugar handlers.
crush_map Nat.add => "+"
crush_map_sort Nat => "Int"

-- Both the attribute-registered and sugar-registered handlers are present.
-- (Run in `MetaM`, since `getTranslationHandlers` lives in `TranslateM`.)
#eval show Lean.MetaM Unit from do
  let (hs, _) ← TranslateM.run {} getTranslationHandlers
  IO.println s!"registered handlers: {hs.size}"
  if hs.size < 3 then throwError "expected >= 3 handlers, got {hs.size}"

-- Config parsing from options.
#eval show Lean.MetaM Unit from do
  let cfg := Config.ofOptions (← Lean.getOptions)
  IO.println s!"default backend = {cfg.backend}, timeout = {cfg.timeout}s, ho = {cfg.hoMode}"

-- Live solver round-trip (skips gracefully if z3 is absent).
#eval show Lean.MetaM Unit from do
  let cfg : Config := { backend := .z3, timeout := 5 }
  match ← (Solver.backendSpec cfg.backend).elim (pure none) (fun _ => do
      let r ← Solver.runQuery cfg #[
        .declSort "U" 0,
        .declFun "a" #[] (.app (.symb "U") #[]),
        .assert (.app (.symb "not")
          #[.app (.symb "=") #[.const "a", .const "a"]])]
      pure (some r)) with
  | none => IO.println "z3: no backend spec"
  | some (.unsat ..) => IO.println "z3 round-trip: unsat ✓"
  | some (.sat ..) => IO.println "z3 round-trip: sat (unexpected)"
  | some (.unknown r) => IO.println s!"z3 round-trip: unknown ({r})"
