import Crush

/-!
Smoke tests for the lean-crush skeleton. These do not exercise the (not-yet-built)
reification pipeline; they check that the foundational layers compile and behave:
the SMT IR printer, the `@[crush_translate]` extension mechanism, the `crush_map`
sugar, config parsing, and a live solver round-trip.
-/

open Crush Crush.SMT

/-- Certified datatype acceptance is opt-in, preserving the production default. -/
example : ({} : Config).certifyDatatype = false := rfl

/-- The live guard constructors are the exact syntax covered by the guarded
metatheory. -/
example (term : Term) : productionNatGuard term = (smt| (>= $term 0)) := rfl

example (condition body : Term) :
    productionGuardBody true condition body = (smt| (=> $condition $body)) := rfl

example (condition body : Term) :
    productionGuardBody false condition body = (smt| (and $condition $body)) := rfl

/-- Unrestricted extension registrations are explicitly marked as crossing the
trusted boundary; they are not accidentally reported as certified. -/
example : ({ declName := `demo, priority := 1000 : HandlerEntry }).trust =
    HandlerTrust.trustedBoundary := rfl

/-- One trusted step classifies the whole completed run as trusted and retains
its reason. -/
example : True := by
  run_tac
    let source := Lean.mkConst ``True
    let (_, state) ← TranslateM.run {} do
      TranslateM.markTrusted
        (Crush.Metatheory.VCG.TrustReason.unsupported source)
    match state.status with
    | .proved => throwError "a trusted step was classified as proved"
    | .trusted reasons =>
        unless reasons.size == 1 do
          throwError "the trusted run did not retain its reason"
  trivial

/-- Boolean negation is routed through the proof-carrying primitive registry,
not merely translated to equivalent syntax by the structural fallback. -/
example : True := by
  run_tac
    let notExpression := Lean.mkApp (Lean.mkConst ``Not) (Lean.mkConst ``True)
    let (translated, state) ← TranslateM.run {} (emitTerm notExpression)
    match translated with
    | .app (.symb "not") arguments =>
        match arguments.toList with
        | [.lit (.bool true)] => pure ()
        | _ => throwError "certified negation hook emitted the wrong argument"
    | _ => throwError "certified negation hook emitted the wrong SMT term"
    unless state.certifiedHookUses.size == 1 do
      throwError "live translation did not audit its certified-hook dispatch"
    let use := state.certifiedHookUses[0]!
    unless use.declaration == ``Not && use.targetSymbol == "not" do
      throwError "certified-hook audit recorded the wrong indexed names"
    let (mappings, _) ← TranslateM.run {} (getCertifiedLoweringsFor ``Not)
    match mappings[0]? with
    | some .not =>
        unless mappings.size == 1 do
          throwError "certified negation registration is ambiguous"
    | none => throwError "certified negation registration is missing"
  trivial

/-- Production arrow discovery now runs through the verified `TypeBridge.flatten`
implementation. -/
example : True := by
  run_tac
    let intTy := Lean.mkConst ``Int
    let natTy := Lean.mkConst ``Nat
    let propTy := Lean.mkSort .zero
    let natToProp ← Lean.mkArrow natTy propTy
    let arrow ← Lean.mkArrow intTy natToProp
    let some shape ← arrowShape? arrow
      | throwError "verified arrow bridge rejected a nondependent arrow"
    unless shape.args.size == 2 && shape.args[0]! == intTy &&
        shape.args[1]! == natTy && shape.res == propTy do
      throwError "verified arrow bridge returned the wrong flattened telescope"
  trivial

opaque bridgeCarrier : Type
axiom bridgeFunction : bridgeCarrier → bridgeCarrier
axiom bridgeArgument : bridgeCarrier
axiom bridgeArgument2 : bridgeCarrier

/-- The executable bridge reifies live constants/application and lambda binding
into intrinsically typed source terms. -/
example : True := by
  run_tac
    let fn := Lean.mkConst ``bridgeFunction
    let argument := Lean.mkConst ``bridgeArgument
    let fnType ← Crush.Metatheory.Reification.reifyType (← Lean.Meta.inferType fn)
    let argumentType ← Crush.Metatheory.Reification.reifyType (← Lean.Meta.inferType argument)
    let signature := Crush.Metatheory.Reification.SignatureBridge.cons fn fnType
      (Crush.Metatheory.Reification.SignatureBridge.cons argument argumentType
        Crush.Metatheory.Reification.SignatureBridge.nil)
    unless (Crush.Metatheory.Reification.certifyConstantIn? signature fn).isSome do
      throwError "live constant certification lost the reified signature position"
    let (_, constantState) ← TranslateM.run {} (emitTerm argument)
    unless constantState.verifiedConstants.size == 1 do
      throwError "live default declaration did not retain its constant certificate"
    match constantState.verifiedConstants[0]? with
    | some proof =>
        match Dynamic.get? Crush.Metatheory.Reification.LiveCertifiedConstantEmission proof with
        | some emission =>
            unless constantState.structuralAllocations.entries.any
                (fun entry => entry.2 == emission.symbol) do
              throwError "certified source symbol is absent from the allocation trace"
        | none => throwError "retained constant certificate has the wrong dynamic type"
    | none => throwError "retained constant certificate is missing"
    let argument2 := Lean.mkConst ``bridgeArgument2
    let sameTypedSignature := Crush.Metatheory.Reification.SignatureBridge.cons argument argumentType
      (Crush.Metatheory.Reification.SignatureBridge.cons argument2 argumentType
        Crush.Metatheory.Reification.SignatureBridge.nil)
    unless (Crush.Metatheory.Reification.certifyConstantIn?
        sameTypedSignature argument2).isSome do
      throwError "identity-bearing certification confused same-typed constants"
    let application := Lean.mkApp fn argument
    let some reifiedApplication ← Crush.Metatheory.Reification.reify? signature
        Crush.Metatheory.Reification.ContextBridge.nil application
      | throwError "typed reification rejected a modeled constant application"
    let _ : Crush.Metatheory.Reification.Reifies signature
        Crush.Metatheory.Reification.ContextBridge.nil application
        reifiedApplication.term := ⟨reifiedApplication.witness⟩
    let carrier := Lean.mkConst ``bridgeCarrier
    let identity := Lean.Expr.lam `x carrier (Lean.mkBVar 0) .default
    unless (← Crush.Metatheory.Reification.reifyTerm?
        Crush.Metatheory.Reification.SignatureBridge.nil
        Crush.Metatheory.Reification.ContextBridge.nil identity).isSome do
      throwError "typed bridge rejected a modeled lambda"
    unless (← Crush.Metatheory.Reification.certifyClosure?
        Crush.Metatheory.Reification.SignatureBridge.nil
        Crush.Metatheory.Reification.ContextBridge.nil (fun _ => false) identity).isSome do
      throwError "typed bridge failed to certify a closed lambda's capture list"
    let (_, translatedState) ← TranslateM.run {} (emitTerm identity)
    unless translatedState.commandEncodings.size == 3 do
      throwError "stateful defunctionalization did not retain all command encodings"
    unless translatedState.commandAllocationLinks.map (·.encodingIndex) == #[0, 1, 2] do
      throwError "defunctionalization allocation links drifted from encoding order"
    let allocatedNames := translatedState.nameAllocations.names
    unless translatedState.commandAllocationLinks.all fun link =>
        link.symbols.all fun symbol => allocatedNames.contains symbol do
      throwError "an encoded command retained an unallocated symbol"
    unless translatedState.commandAllocationLinks.map (·.symbols.size) == #[2, 2, 2] do
      throwError "app/closure/equation structural dependencies were not fully linked"
    match translatedState.status with
    | .trusted reasons =>
        unless reasons.size == 1 && translatedState.directSource == some identity do
          throwError "the direct translator did not retain its single root trust boundary"
        match reasons[0]? with
        | some (Crush.Metatheory.VCG.TrustReason.direct source) =>
            unless source == identity do
              throwError "the direct translator retained the wrong trusted root"
        | _ => throwError "the direct translator retained the wrong trust reason"
    | .proved =>
        throwError "the legacy direct translator was incorrectly classified as proved"
    match translatedState.commandEncodings[0]?, translatedState.commandEncodings[1]?,
        translatedState.commandEncodings[2]? with
    | some (Crush.Metatheory.VCG.CommandEncoding.app _),
        some (Crush.Metatheory.VCG.CommandEncoding.closure _),
        some (Crush.Metatheory.VCG.CommandEncoding.closureEquation equation) =>
        match equation.evidence with
        | .proved _ => pure ()
        | .trusted _ =>
            throwError "closure equation did not retain its typed semantic proof"
    | _, _, _ => throwError "stateful defunctionalization encodings have the wrong order"
    Lean.Meta.withLocalDeclD `captured carrier fun captured => do
      let liveContext := Crush.Metatheory.Reification.ContextBridge.cons
        captured.fvarId! argumentType Crush.Metatheory.Reification.ContextBridge.nil
      let capturingLambda := Lean.Expr.lam `ignored carrier captured .default
      let eligible := fun id => id == captured.fvarId!
      unless (← Crush.Metatheory.Reification.certifyClosure?
          Crush.Metatheory.Reification.SignatureBridge.nil liveContext eligible
          capturingLambda).isSome do
        throwError "typed bridge failed exact ordered capture certification"
      unless (← Crush.Metatheory.Reification.certifyLocalClosure?
          capturingLambda #[captured.fvarId!]).isSome do
        throwError "live closure entry point failed to construct its certificate"
      let appliedBody := Lean.mkApp fn captured
      let constantLambda := Lean.Expr.lam `ignored carrier appliedBody .default
      unless (← Crush.Metatheory.Reification.certifyLocalClosure?
          constantLambda #[captured.fvarId!]).isSome do
        throwError "live closure entry point failed to reify its finite signature"
    let equalityHead ← Lean.Meta.mkConstWithFreshMVarLevels ``Eq
    let reflexiveBody := Lean.mkApp3 equalityHead carrier (Lean.mkBVar 0) (Lean.mkBVar 0)
    let universal := Lean.Expr.forallE `x carrier reflexiveBody .default
    unless (← Crush.Metatheory.Reification.reifySentence? universal).isSome do
      throwError "typed reification rejected modeled equality/quantification"
    let predicate := Lean.Expr.lam `x carrier reflexiveBody .default
    let existsHead ← Lean.Meta.mkConstWithFreshMVarLevels ``Exists
    let existential := Lean.mkApp2 existsHead carrier predicate
    unless (← Crush.Metatheory.Reification.reifySentence? existential).isSome do
      throwError "typed reification rejected modeled existential quantification"
  trivial

/-- The total collector called by `emitClosure` preserves first occurrence,
removes duplicates, and then applies the SMT-local eligibility predicate. -/
example : True := by
  run_tac
    let x : Lean.FVarId := ⟨`capture_x⟩
    let y : Lean.FVarId := ⟨`capture_y⟩
    let expression := Lean.mkApp (Lean.mkFVar x)
      (Lean.mkApp (Lean.mkFVar y) (Lean.mkFVar x))
    unless collectFVarsOrdered expression == #[x, y] do
      throwError "production capture collection lost first-occurrence order"
    let selected := selectClosureCaptures expression fun id => id == y
    unless selected == #[y] do
      throwError "production capture eligibility filtering disagrees with collection"
  trivial

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
  let ((name0, name0Again, name1), state) ← TranslateM.run {} do
    let name0 ← TranslateM.symbolForStructural
      { tag := "test-sort", exprs := #[list0] } "List"
    let name0Again ← TranslateM.symbolForStructural
      { tag := "test-sort", exprs := #[list0] } "ignored-reuse-hint"
    let name1 ← TranslateM.symbolForStructural
      { tag := "test-sort", exprs := #[list1] } "List"
    return (name0, name0Again, name1)
  unless name0 == name0Again do
    throwError "one structural identity did not reuse its allocated SMT symbol"
  if name0 == name1 then
    throwError "universe-distinct expressions shared one SMT symbol"
  unless state.structuralAllocations.entries.length == 2 do
    throwError "structural allocation trace recorded reuse as a fresh allocation"
  have _ := state.structuralAllocations.namesNodup

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
