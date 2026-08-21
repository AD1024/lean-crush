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
  .assert (smt| (= (f a) a)),
  .assert (.forallE #[("x", .app (.symb "U") #[])]
            (.annot (smt| (= (f $(.bvar 0)) $(.bvar 0))) #[.named "ax"])),
  .checkSat
]

/-- info: (set-logic QF_UF) -/
#guard_msgs in
#eval IO.println (commandToString demoScript[0]!)

#eval do
  IO.println "--- generated script ---"
  IO.println (scriptToString demoScript)

#eval show IO Unit from do
  unless escapeSmtString "\\u{61}" == "\\u{5c}u{61}" do
    throw <| IO.userError "backslash was not escaped before SMT-LIB printing"
  unless quoteSymbol "let" == "|let|" do
    throw <| IO.userError "SMT-LIB reserved word was emitted as a simple symbol"
  let encodedPipe := quoteSymbol "a|b"
  let encodedSlash := quoteSymbol "a\\b"
  unless encodedPipe != encodedSlash && !encodedPipe.contains "|" && !encodedSlash.contains "\\" do
    throw <| IO.userError "unsafe quoted symbols were not encoded injectively"
  unless quoteSymbol encodedPipe != encodedPipe do
    throw <| IO.userError "encoded SMT symbol collided with a literal source name"
  match parseSexp "(|a b| |x(y)|)" with
  | some (.list xs, _) =>
    unless xs == #[.atom "a b", .atom "x(y)"] do
      throw <| IO.userError "quoted SMT symbols parsed incorrectly"
  | _ => throw <| IO.userError "quoted SMT symbol expression did not parse"
  match parseSexp "\t\r\n(λ |β γ| \"δ\"\"ε\") trailing" with
  | some (.list xs, " trailing") =>
    unless xs == #[.atom "λ", .atom "β γ", .str "δ\"ε"] do
      throw <| IO.userError "UTF-8 atoms or escaped SMT strings parsed incorrectly"
  | _ => throw <| IO.userError "UTF-8 S-expression or remainder did not parse"
  unless parseSexps "; first\n(a)\r\n; second\r\n(b)" ==
      #[.list #[.atom "a"], .list #[.atom "b"]] do
    throw <| IO.userError "SMT-LIB whitespace or comments parsed incorrectly"
  unless (parseSexps "(|invalid\\symbol|)").isEmpty do
    throw <| IO.userError "backslash in a quoted SMT symbol was accepted"
  unless (parseSexps "(ok) (").isEmpty do
    throw <| IO.userError "truncated S-expression input was accepted partially"
  -- A leading status atom is skipped, the first list is the core, the rest is the proof.
  let (core, proof) :=
    Solver.splitCoreAndProof true true (parseSexps "warning (|a ) b| x) (proof)")
  unless core == some (.list #[.atom "a ) b", .atom "x"]) &&
      proof == #[Sexp.list #[.atom "proof"]] do
    throw <| IO.userError "solver response split drifted from the S-expression parser"
  -- A truncated tail keeps the complete S-expressions before it.
  unless parseSexpPrefix "(core) (step" == #[Sexp.list #[.atom "core"]] do
    throw <| IO.userError "truncated solver output discarded its usable prefix"

-- Extension mechanism: register term and sort handlers and confirm both are found.

/-- A hand-written handler that maps `Nat.succ n` to `(+ n 1)`. -/
@[crush_translate high]
def succHandler : TranslationHandler := fun ctx => do
  let .const ``Nat.succ _ := ctx.fn | return none
  match ctx.args with
  | #[n] => return some (smt| (+ $(← ctx.emitTerm n) 1))
  | _ => return none

-- Sugar handlers.
crush_map Nat.add => "+"
crush_map_sort Nat => "Int"

-- The attribute-registered and sugar-registered term handlers are present, and
-- `crush_map_sort` uses the independent sort-handler registry.
-- (Run in `MetaM`, since `getTranslationHandlers` lives in `TranslateM`.)
#eval show Lean.MetaM Unit from do
  let (hs, _) ← TranslateM.run {} getTranslationHandlers
  IO.println s!"registered handlers: {hs.size}"
  if hs.size < 2 then throwError "expected >= 2 term handlers, got {hs.size}"
  let (sortHs, _) ← TranslateM.run {} getSortHandlers
  IO.println s!"registered sort handlers: {sortHs.size}"
  if sortHs.isEmpty then throwError "expected at least one sort handler"

-- A derived fresh name must itself be reserved. Previously, allocating `x_0`
-- before the second `x` made the collision branch return `x_0` again.
#eval show Lean.MetaM Unit from do
  let ((first, base, second), _) ← TranslateM.run {} do
    let first ← TranslateM.freshSymbol "x_0"
    let base ← TranslateM.freshSymbol "x"
    let second ← TranslateM.freshSymbol "x"
    return (first, base, second)
  unless first != base && first != second && base != second do
    throwError "fresh SMT symbol allocation returned a reserved name"

-- Derived names remain stable while avoiding names allocated earlier.
#eval show Lean.MetaM Unit from do
  let ((occupied, named, namedAgain, derived, repeated, distinct), _) ←
      TranslateM.run {} do
    let occupied ← TranslateM.freshSymbol "Array_mk"
    let named ← TranslateM.reserveDerived "Array_mk"
    let namedAgain ← TranslateM.reserveDerived "Array_mk"
    let ctorKey : DerivedSymbolKey := {
      tag := "test-constructor"
      parent := "Array"
    }
    let derived ← TranslateM.reserveDerivedFor ctorKey "Array_mk"
    let repeated ← TranslateM.reserveDerivedFor ctorKey "Array_mk"
    let distinct ← TranslateM.reserveDerivedFor {
      tag := "test-selector"
      parent := "Array"
    } "Array_mk"
    return (occupied, named, namedAgain, derived, repeated, distinct)
  unless occupied != named && named == namedAgain && named != derived &&
      derived == repeated && derived != distinct do
    throwError "derived SMT symbol allocation was colliding or unstable"

opaque modelLabelProbe : Prop → Nat

/-- error: crush: could not prove the goal — the solver found a model:
    modelLabelProbe [modelLabelProbe_ -/
#guard_msgs(error, substring := true) in
example (p q : Prop) : modelLabelProbe p = modelLabelProbe q := by
  crush

-- Structural symbol keys distinguish universe levels even when pretty-printing
-- would render both constants identically with `pp.universes` disabled.
#eval show Lean.MetaM Unit from do
  let list0 := Lean.mkConst ``List [.zero]
  let list1 := Lean.mkConst ``List [.succ .zero]
  let ((name0, name1), _) ← TranslateM.run {} do
    let name0 ← TranslateM.symbolForStructural
      { tag := "test-sort", exprs := #[list0] } "List"
    let name1 ← TranslateM.symbolForStructural
      { tag := "test-sort", exprs := #[list1] } "List"
    return (name0, name1)
  if name0 == name1 then
    throwError "universe-distinct expressions shared one SMT symbol"

-- Definitional equality of universe maxima should not split an SMT symbol.
#eval show Lean.MetaM Unit from do
  let u := Lean.Level.param `u
  let v := Lean.Level.param `v
  let lhs := Lean.mkSort (.max u v)
  let rhs := Lean.mkSort (.max v u)
  let ((lhsName, rhsName), _) ← TranslateM.run {} do
    let lhsName ← TranslateM.symbolForStructural
      { tag := "test-sort", exprs := #[lhs] } "lhs"
    let rhsName ← TranslateM.symbolForStructural
      { tag := "test-sort", exprs := #[rhs] } "rhs"
    return (lhsName, rhsName)
  unless lhsName == rhsName do
    throwError "equivalent universe maxima received different SMT symbols"

-- Config parsing from options.
#eval show Lean.MetaM Unit from do
  let cfg := Config.ofOptions (← Lean.getOptions)
  IO.println s!"default backend = {cfg.backend}, timeout = {cfg.timeout}s, ho = {cfg.hoMode}"

-- Backend executable resolution: a missing solver must be caught before a query runs.
#eval show IO Unit from do
  unless (← Solver.resolveExe "crush-no-such-solver-executable").isNone do
    throw <| IO.userError "a nonexistent solver name resolved to an executable"
  unless (← Solver.resolveExe (← IO.appPath).toString).isSome do
    throw <| IO.userError "an existing executable path failed to resolve"
  unless Solver.backendExe .z3 == some "z3" && Solver.backendExe .none == none do
    throw <| IO.userError "backend executables were reported incorrectly"

-- A refused command must travel with the verdict: the solver keeps reading, so `sat`
-- covers only the fragment it accepted.
#eval show Lean.MetaM Unit from do
  let cfg : Config := { backend := .z3, timeout := 5 }
  if !(← Solver.backendAvailable cfg.backend) then
    IO.println "z3: not installed; skipping refusal round-trip"
  else
    match ← Solver.runQuery cfg #[.assert (smt| (= (crush_not_an_smt_operator 1) 1))] with
    | .sat _ diagnostics =>
      unless diagnostics.contains "error" do
        throwError "a refused command was not reported alongside the model"
      IO.println "z3 refusal round-trip: reported with the model ✓"
    | .unknown reason =>
      unless reason.contains "error" do
        throwError "a refused command was not reported alongside `unknown`"
      IO.println "z3 refusal round-trip: reported with `unknown` ✓"
    | .unsat .. => throwError "a refused command produced an `unsat` verdict"

-- Live solver round-trip (skips gracefully if z3 is absent).
#eval show Lean.MetaM Unit from do
  let cfg : Config := { backend := .z3, timeout := 5 }
  if !(← Solver.backendAvailable cfg.backend) then
    IO.println "z3: not installed; skipping round-trip"
  else
    match ← Solver.runQuery cfg #[
        .declSort "U" 0,
        .declFun "a" #[] (.app (.symb "U") #[]),
        .assert (smt| (not (= a a)))] with
    | .unsat .. => IO.println "z3 round-trip: unsat ✓"
    | .sat .. => IO.println "z3 round-trip: sat (unexpected)"
    | .unknown r => IO.println s!"z3 round-trip: unknown ({r})"
