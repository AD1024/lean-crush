import Lean
import Crush.SMT.Sexp
import Crush.Solver.KernelCheck

open Lean Elab Meta Tactic

/-!
# Extensible certificate replay

Custom SMT lowerings can introduce theory operators that the built-in Alethe term
decoder does not know. `@[crush_replay "operator"]` registers the inverse mapping
needed by checked certificate replay. Rule handlers registered with
`@[crush_replay_rule "rule"]` prove individual Alethe inferences from their
already-replayed premises.
-/

namespace Crush

open SMT

universe u

/-- A decoded SMT application offered to a replay term handler. -/
structure ReplayTermContext where
  /-- The ordinary or indexed SMT operator name. -/
  head : String
  /-- Indexed-identifier payload, excluding `_` and the operator name. -/
  indices : Array Sexp
  /-- Recursively decoded Lean arguments. -/
  args : Array Expr

/-- Reconstruct the Lean expression denoted by an SMT operator application.

Returning `none` defers to the next handler. Built-in theory decoding runs before
registered handlers. -/
abbrev ReplayTermHandler := ReplayTermContext → MetaM (Option Expr)

instance : TypeName ReplayTermHandler := unsafe (TypeName.mk _ ``ReplayTermHandler)

/-- Serializable metadata for one operator-indexed term handler. -/
private structure ReplayTermEntry where
  head : String
  declName : Name
  priority : Nat
  deriving Inhabited

private structure ReplayTermDecl where
  declName : Name
  priority : Nat
  deriving Inhabited

private abbrev ReplayTermState :=
  Std.HashMap String (Array ReplayTermDecl)

private def addReplayTermEntry
    (state : ReplayTermState) (entry : ReplayTermEntry) : ReplayTermState :=
  state.alter entry.head fun entries =>
    (entries.getD #[]).push { declName := entry.declName, priority := entry.priority }

initialize crushReplayTermExt :
    SimplePersistentEnvExtension ReplayTermEntry ReplayTermState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addReplayTermEntry
    addImportedFn := fun imports =>
      imports.foldl (init := {}) fun state entries =>
        entries.foldl (init := state) addReplayTermEntry
  }

/-- Register an inverse replay handler for one SMT operator.

Higher priorities run first. A handler is consulted only when built-in decoding
does not recognize the application. -/
syntax (name := crushReplayAttr) "crush_replay " str (ppSpace prio)? : attr

private def registerReplayTermHandler
    (attributeName : String) (declName : Name) (stx : Syntax) : AttrM Unit := do
  let some head := stx[1].isStrLit?
    | throwError "@[{attributeName}] expects an SMT operator string"
  let priority ← getAttrParamOptPrio stx[2]
  let env ← getEnv
  let some info := env.find? declName
    | throwError "unknown declaration {declName}"
  let expectedType := mkConst ``Crush.ReplayTermHandler
  unless (← MetaM.run' (withoutModifyingState <|
      Meta.isDefEqGuarded info.type expectedType)) do
    throwError "@[{attributeName}] expects a declaration of type `ReplayTermHandler`, \
                but {declName} has type{indentExpr info.type}"
  modifyEnv fun env =>
    crushReplayTermExt.addEntry env { head, declName, priority }

initialize registerBuiltinAttribute {
  name := `crushReplayAttr
  descr := "Register an operator-indexed lean-crush replay term handler."
  applicationTime := .afterCompilation
  add := fun declName stx _ =>
    registerReplayTermHandler "crush_replay" declName stx
}

/-! ## Inference-rule replay -/

/-- A replayed clause and its checked Lean proof. -/
structure ReplayClause where
  proof : Expr
  clause : Expr
  literals : Array Expr
  deriving Inhabited

/-- A named value exposed as a local `let` while running a replay tactic. -/
structure ReplayBinding where
  name : Name
  value : Expr

/-- One concrete Alethe inference offered to a replay rule handler. -/
structure ReplayRuleContext where
  stepId : String
  rule : String
  target : Expr
  targetLiterals : Array Expr
  premises : Array ReplayClause
  args : Array Sexp
  scopedProofs : Array Expr := #[]
  decodeTerm : Sexp → MetaM (Option Expr)
  decodeSort : Sexp → MetaM (Option Expr)
  toProp : Expr → MetaM Expr
  bindings : Array ReplayBinding := #[]

/-- Retrieve a value captured by a replay pattern. -/
def ReplayRuleContext.binding? (ctx : ReplayRuleContext) (name : Name) : Option Expr :=
  let name := name.eraseMacroScopes
  ctx.bindings.findSome? fun binding =>
    if binding.name == name then some binding.value else none

/-- Patterns over raw Alethe S-expressions. -/
inductive ReplaySexpPattern where
  | ignore
  | rest
  | exactString (value : String)
  | exactNat (value : Nat)
  | exactAtom (value : String)
  | sexp (name : Name)
  | term (name : Name) (typeGuard : Option (TSyntax `term) := none)
  | nat (name : Name)
  | int (name : Name)
  | string (name : Name)
  | atom (name : Name)
  | sort (name : Name)
  | prop (name : Name)
  | list (patterns : Array ReplaySexpPattern)
  deriving Inhabited

/-- Patterns over arguments that certificate-term decoding has already reconstructed. -/
inductive ReplayExprPattern where
  | ignore
  | rest
  | term (name : Name) (typeGuard : Option (TSyntax `term) := none)
  deriving Inhabited

private partial def sexpToExpr : Sexp → MetaM Expr
  | .atom value =>
    return mkApp (mkConst ``Sexp.atom) (Lean.toExpr value)
  | .str value =>
    return mkApp (mkConst ``Sexp.str) (Lean.toExpr value)
  | .list values => do
    let values ← values.toList.mapM sexpToExpr
    let values ← mkArrayLit (mkConst ``Sexp) values
    return mkApp (mkConst ``Sexp.list) values

private partial def withReplayBindingsMeta {α : Type}
    (bindings : Array ReplayBinding) (index : Nat) (locals : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  if h : index < bindings.size then
    let binding := bindings[index]
    let type ← inferType binding.value
    withLetDecl binding.name type binding.value fun fvar =>
      withReplayBindingsMeta bindings (index + 1) (locals.push fvar) k
  else
    k locals

private partial def normalizeReplayBindingSyntax
  (bindings : Array ReplayBinding) : Syntax → Syntax
  | .ident info rawVal value preResolved =>
    let normalized := value.eraseMacroScopes
    if bindings.any (·.name.eraseMacroScopes == normalized) then
      .ident info rawVal normalized []
    else
      .ident info rawVal value preResolved
  | .node info kind args =>
    .node info kind (args.map (normalizeReplayBindingSyntax bindings))
  | stx =>
    stx

private def replayTypeMatches (bindings : Array ReplayBinding)
    (value : Expr) (guard : TSyntax `term) : MetaM Bool := do
  withReplayBindingsMeta bindings 0 #[] fun _ => do
    let guard : TSyntax `term :=
      ⟨normalizeReplayBindingSyntax bindings guard.raw⟩
    let expected ← Term.TermElabM.run' do
      let expected ← Term.elabType guard
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars expected
    let actual ← instantiateMVars (← inferType value)
    withoutModifyingState <| isDefEqGuarded actual expected

private def bindReplayValue (bindings : Array ReplayBinding)
    (name : Name) (value : Expr) : Option (Array ReplayBinding) :=
  let name := name.eraseMacroScopes
  if bindings.any (·.name == name) then
    none
  else
    some (bindings.push { name, value })

private partial def matchSexpPatterns
    (ctx : ReplayRuleContext) (patterns : Array ReplaySexpPattern)
    (values : Array Sexp) (bindings : Array ReplayBinding := #[]) :
    MetaM (Option (Array ReplayBinding)) := do
  go 0 0 bindings
where
  go (patternIndex valueIndex : Nat) (bindings : Array ReplayBinding) :
      MetaM (Option (Array ReplayBinding)) := do
    if patternIndex == patterns.size then
      return if valueIndex == values.size then some bindings else none
    let pattern := patterns[patternIndex]!
    if pattern matches .rest then
      return if patternIndex + 1 == patterns.size then some bindings else none
    let some value := values[valueIndex]? | return none
    let some bindings ← matchOne pattern value bindings | return none
    go (patternIndex + 1) (valueIndex + 1) bindings

  matchOne (pattern : ReplaySexpPattern) (value : Sexp)
      (bindings : Array ReplayBinding) :
      MetaM (Option (Array ReplayBinding)) := do
    match pattern with
    | .ignore => return some bindings
    | .rest => return none
    | .exactString expected =>
      return if value == .str expected then some bindings else none
    | .exactNat expected =>
      return if value.atom?.bind String.toNat? == some expected then
        some bindings
      else
        none
    | .exactAtom expected =>
      return if value == .atom expected then some bindings else none
    | .sexp name =>
      return bindReplayValue bindings name (← sexpToExpr value)
    | .nat name =>
      let some parsed := value.atom?.bind String.toNat? | return none
      return bindReplayValue bindings name (Lean.toExpr parsed)
    | .int name =>
      let some parsed := value.atom?.bind String.toInt? | return none
      return bindReplayValue bindings name (Lean.toExpr parsed)
    | .string name =>
      let .str parsed := value | return none
      return bindReplayValue bindings name (Lean.toExpr parsed)
    | .atom name =>
      let .atom parsed := value | return none
      return bindReplayValue bindings name (Lean.toExpr parsed)
    | .term name guard =>
      let some decoded ← ctx.decodeTerm value | return none
      if let some guard := guard then
        unless ← replayTypeMatches bindings decoded guard do return none
      return bindReplayValue bindings name decoded
    | .sort name =>
      let some decoded ← ctx.decodeSort value | return none
      return bindReplayValue bindings name decoded
    | .prop name =>
      let some decoded ← ctx.decodeTerm value | return none
      let proposition ← ctx.toProp decoded
      unless (← whnf (← inferType proposition)).isProp do return none
      return bindReplayValue bindings name proposition
    | .list nested =>
      let .list values := value | return none
      matchSexpPatterns ctx nested values bindings

private partial def matchExprPatterns
    (patterns : Array ReplayExprPattern) (values : Array Expr)
    (bindings : Array ReplayBinding := #[]) :
    MetaM (Option (Array ReplayBinding)) := do
  go 0 0 bindings
where
  go (patternIndex valueIndex : Nat) (bindings : Array ReplayBinding) :
      MetaM (Option (Array ReplayBinding)) := do
    if patternIndex == patterns.size then
      return if valueIndex == values.size then some bindings else none
    let pattern := patterns[patternIndex]!
    if pattern matches .rest then
      return if patternIndex + 1 == patterns.size then some bindings else none
    let some value := values[valueIndex]? | return none
    match pattern with
    | .ignore =>
      go (patternIndex + 1) (valueIndex + 1) bindings
    | .rest =>
      return none
    | .term name guard =>
      if let some guard := guard then
        unless ← replayTypeMatches bindings value guard do return none
      let some bindings := bindReplayValue bindings name value | return none
      go (patternIndex + 1) (valueIndex + 1) bindings

/-- Match a rule's raw `:args` and attach the resulting named bindings. -/
def ReplayRuleContext.matchArgs (ctx : ReplayRuleContext)
    (patterns : Array ReplaySexpPattern) : TacticM (Option ReplayRuleContext) := do
  let some bindings ← matchSexpPatterns ctx patterns ctx.args ctx.bindings
    | return none
  return some { ctx with bindings }

/-- Match an inverse term handler's indexed payload and decoded argument spine. -/
def ReplayTermContext.match (ctx : ReplayTermContext)
    (indices : Array ReplaySexpPattern) (args : Array ReplayExprPattern) :
    MetaM (Option (Array ReplayBinding)) := do
  let dummy : ReplayRuleContext := {
    stepId := ""
    rule := ctx.head
    target := mkConst ``True
    targetLiterals := #[]
    premises := #[]
    args := ctx.indices
    decodeTerm := fun _ => return none
    decodeSort := fun _ => return none
    toProp := pure
  }
  let some bindings ←
      matchSexpPatterns dummy indices ctx.indices
    | return none
  matchExprPatterns args ctx.args bindings

/-- Elaborate a Lean term under named replay bindings and close the aliases as lets. -/
def elabReplayTerm (bindings : Array ReplayBinding)
    (body : TSyntax `term) : MetaM Expr := do
  withReplayBindingsMeta bindings 0 #[] fun locals => do
    let body : TSyntax `term :=
      ⟨normalizeReplayBindingSyntax bindings body.raw⟩
    let value ← Term.TermElabM.run' do
      let value ← Term.elabTerm body none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars value
    mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false)
      locals value

/-- One left-hand-side alternative in a term replay registration. -/
structure ReplayTermAlternative where
  head : String
  indices : Array ReplaySexpPattern
  args : Array ReplayExprPattern
  deriving Inhabited

/-- A shallow term replay registration retained as syntax and matched natively. -/
structure ReplayTermPatternHandler where
  alternatives : Array ReplayTermAlternative
  body : TSyntax `term
  priority : Nat
  deriving Inhabited

private abbrev ReplayTermPatternState :=
  Std.HashMap String (Array ReplayTermPatternHandler)

private def addReplayTermPattern
    (state : ReplayTermPatternState)
    (entry : ReplayTermPatternHandler) : ReplayTermPatternState := Id.run do
  let mut state := state
  let mut heads : Array String := #[]
  for alternative in entry.alternatives do
    unless heads.contains alternative.head do
      heads := heads.push alternative.head
      state := state.alter alternative.head fun entries =>
        (entries.getD #[]).push entry
  return state

initialize crushReplayTermPatternExt :
    SimplePersistentEnvExtension
      ReplayTermPatternHandler ReplayTermPatternState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addReplayTermPattern
    addImportedFn := fun imports =>
      imports.foldl (init := {}) fun state entries =>
        entries.foldl (init := state) addReplayTermPattern
  }

/-- A resolved term replay implementation. -/
inductive ResolvedReplayTermHandler where
  | declaration (declName : Name) (handler : ReplayTermHandler)
  | pattern (handler : ReplayTermPatternHandler)

/-- A term replay implementation paired with its dispatch priority. -/
structure PrioritizedReplayTermHandler where
  priority : Nat
  implementation : ResolvedReplayTermHandler

/-- Resolved replay term handlers, grouped by SMT operator and ordered by priority. -/
abbrev ReplayTermRegistry :=
  Std.HashMap String (Array PrioritizedReplayTermHandler)

unsafe def getReplayTermHandlersUnsafe : MetaM ReplayTermRegistry := do
  let env ← getEnv
  let options ← getOptions
  let mut result : ReplayTermRegistry := {}
  for (head, entries) in (crushReplayTermExt.getState env).toList do
    let handlers ← entries.filterMapM fun entry => do
      match env.evalConst ReplayTermHandler options entry.declName with
      | .ok handler =>
        return some {
          priority := entry.priority
          implementation := .declaration entry.declName handler
        }
      | .error error =>
        throwError "failed to evaluate replay term handler \
          `{entry.declName}`: {error}"
    result := result.insert head handlers
  for (head, entries) in (crushReplayTermPatternExt.getState env).toList do
    result := result.alter head fun current =>
      let current := current.getD #[]
      some <| entries.foldl (init := current) fun result entry =>
        result.push {
          priority := entry.priority
          implementation := .pattern entry
        }
  for (head, handlers) in result.toList do
    result := result.insert head
      (handlers.qsort fun left right => left.priority > right.priority)
  return result

@[implemented_by getReplayTermHandlersUnsafe]
opaque getReplayTermHandlers : MetaM ReplayTermRegistry

/-- Whether an operator has any registered inverse replay handlers. -/
def hasReplayTermHandlersFor (head : String) : CoreM Bool := do
  let env ← getEnv
  return (crushReplayTermExt.getState env).contains head ||
    (crushReplayTermPatternExt.getState env).contains head

/-- Run registered handlers for an application after built-in decoding declines. -/
def runReplayTermHandlers (registry : ReplayTermRegistry)
    (head : String) (indices : Array Sexp) (args : Array Expr) :
    MetaM (Option Expr) := do
  let context : ReplayTermContext := { head, indices, args }
  for candidate in registry.getD head #[] do
    let result ←
      match candidate.implementation with
      | .declaration _ handler =>
        handler context
      | .pattern handler => do
        let mut result := none
        for alternative in handler.alternatives do
          if alternative.head == head then
            if let some bindings ←
                context.match alternative.indices alternative.args then
              result := some (← elabReplayTerm bindings handler.body)
              break
        pure result
    if let some result := result then
      let result ← instantiateMVars result
      let _ ← inferType result
      return some result
  return none

/-- Prove one concrete certificate inference, or return `none` to defer. -/
abbrev ReplayRuleHandler := ReplayRuleContext → TacticM (Option Expr)

instance : TypeName ReplayRuleHandler := unsafe (TypeName.mk _ ``ReplayRuleHandler)

/-- Uniform callback used internally for conditional replay dispatch. -/
abbrev ReplayConditionHandler := ReplayRuleContext → MetaM Bool

instance : TypeName ReplayConditionHandler :=
  unsafe (TypeName.mk _ ``ReplayConditionHandler)

/-- Interface for values that decide whether a matched replay rule applies. -/
class ReplayCondition (α : Type u) where
  check : α → ReplayRuleContext → MetaM Bool

instance : ReplayCondition ReplayConditionHandler where
  check condition ctx := condition ctx

private partial def withReplayBindings {α : Type}
    (bindings : Array ReplayBinding) (index : Nat) (locals : Array Expr)
    (k : Array Expr → TacticM α) : TacticM α := do
  if h : index < bindings.size then
    let binding := bindings[index]
    let type ← inferType binding.value
    withLetDecl binding.name type binding.value fun fvar =>
      withReplayBindings bindings (index + 1) (locals.push fvar) k
  else
    k locals

private partial def introReplayBinders (goal : MVarId) : MetaM MVarId := do
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    match target.consumeMData with
    | .forallE .. =>
      let (_, next) ← goal.intro1P
      introReplayBinders next
    | .letE name type value body nondep =>
      let tag ← goal.getTag
      withLetDecl name type value (nondep := nondep) fun fvar => do
        let inner ← mkFreshExprSyntheticOpaqueMVar
          (body.instantiate1 fvar) tag
        goal.assign (← mkLetFVars
          (usedLetOnly := false) (generalizeNondepLet := false)
          #[fvar] inner)
        introReplayBinders inner.mvarId!
    | _ =>
      return goal

/-- Run a tactic against exactly the replayed premises and explicit pattern bindings.

The implication is closed before tactic execution. `runReplayRuleHandlers`
kernel-checks the returned proof and generated declarations. -/
def ReplayRuleContext.runTactic (ctx : ReplayRuleContext)
    (tactic : TSyntax `tactic) (includeScope : Bool := false) :
    TacticM (Option Expr) := do
  let tactic : TSyntax `tactic :=
    ⟨normalizeReplayBindingSyntax ctx.bindings tactic.raw⟩
  let premiseProofs := ctx.premises.map (·.proof)
  let proofs :=
    if includeScope then premiseProofs ++ ctx.scopedProofs else premiseProofs
  let hypTypes ← proofs.mapM fun proof => do
    instantiateMVars (← inferType proof)
  let implication :=
    hypTypes.foldr (fun type body => mkForall `h .default type body) ctx.target
  let implication ←
    withReplayBindings ctx.bindings 0 #[] fun locals =>
      mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false)
        locals implication
  let stepParams ← collectProofParams #[implication]
  let closedImplication ← instantiateMVars (← mkForallFVars stepParams implication)
  let saved ← saveState
  try
    let goal ← withLCtx {} {} do mkFreshExprMVar closedImplication
    let tacticGoal ← introReplayBinders goal.mvarId!
    let goals ←
      withOptions (fun options =>
          options.setBool `linter.unusedSimpArgs false) <|
        Tactic.run tacticGoal <|
          Tactic.withSuppressedMessages <|
            Tactic.withoutRecover (evalTactic tactic)
    if goals.isEmpty then
      let assigned ← instantiateMVars goal
      let proof := mkAppN (mkAppN assigned stepParams) proofs
      return some proof
    restoreState saved
    return none
  catch _ =>
    restoreState saved
    return none

/-- Retry a replay tactic with enclosing subproof assumptions when necessary. -/
def ReplayRuleContext.runTacticWithScopeFallback (ctx : ReplayRuleContext)
    (tactic : TSyntax `tactic) : TacticM (Option Expr) := do
  if let some proof ← ctx.runTactic tactic then
    return some proof
  if ctx.scopedProofs.isEmpty then
    return none
  ctx.runTactic tactic (includeScope := true)

private structure ReplayRuleEntry where
  rule : Option String
  declName : Name
  priority : Nat
  deriving Inhabited

private structure ReplayRuleDecl where
  declName : Name
  priority : Nat
  deriving Inhabited

private abbrev ReplayRuleState :=
  Std.HashMap String (Array ReplayRuleDecl)

private def replayRuleKey (rule : Option String) : String :=
  rule.getD ""

private def addReplayRuleEntry
    (state : ReplayRuleState) (entry : ReplayRuleEntry) : ReplayRuleState :=
  state.alter (replayRuleKey entry.rule) fun entries =>
    (entries.getD #[]).push {
      declName := entry.declName
      priority := entry.priority
    }

initialize crushReplayRuleExt :
    SimplePersistentEnvExtension ReplayRuleEntry ReplayRuleState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addReplayRuleEntry
    addImportedFn := fun imports =>
      imports.foldl (init := {}) fun state entries =>
        entries.foldl (init := state) addReplayRuleEntry
  }

/-- Register a checked replay handler for one Alethe rule.

Omitting the rule string registers a wildcard handler. Higher priorities run first,
and returning `none` delegates to the next matching handler. -/
syntax (name := crushReplayRuleAttr)
  "crush_replay_rule" (ppSpace str)? (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `crushReplayRuleAttr
  descr := "Register a lean-crush Alethe inference replay handler."
  applicationTime := .afterCompilation
  add := fun declName stx _ => do
    let rule := stx[1].getOptional?.bind (·.isStrLit?)
    let priority ← getAttrParamOptPrio stx[2]
    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration {declName}"
    let expectedType := mkConst ``Crush.ReplayRuleHandler
    unless (← MetaM.run' (withoutModifyingState <|
        Meta.isDefEqGuarded info.type expectedType)) do
      throwError "@[crush_replay_rule] expects a declaration of type \
                  `ReplayRuleHandler`, but {declName} has type{indentExpr info.type}"
    modifyEnv fun env =>
      crushReplayRuleExt.addEntry env { rule, declName, priority }
}

/-- One left-hand-side alternative in an inference replay registration. -/
structure ReplayRuleAlternative where
  rule : String
  args : Array ReplaySexpPattern
  deriving Inhabited

private structure ReplayConditionRef where
  declName : Name
  label : String
  deriving Inhabited

/-- A shallow inference replay registration retained as syntax and run natively. -/
structure ReplayRulePatternHandler where
  alternatives : Array ReplayRuleAlternative
  condition : Option ReplayConditionRef
  tactic : TSyntax `tactic
  priority : Nat
  deriving Inhabited

private abbrev ReplayRulePatternState :=
  Std.HashMap String (Array ReplayRulePatternHandler)

private def addReplayRulePattern
    (state : ReplayRulePatternState)
    (entry : ReplayRulePatternHandler) : ReplayRulePatternState := Id.run do
  let mut state := state
  let mut rules : Array String := #[]
  for alternative in entry.alternatives do
    unless rules.contains alternative.rule do
      rules := rules.push alternative.rule
      state := state.alter alternative.rule fun entries =>
        (entries.getD #[]).push entry
  return state

initialize crushReplayRulePatternExt :
    SimplePersistentEnvExtension
      ReplayRulePatternHandler ReplayRulePatternState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addReplayRulePattern
    addImportedFn := fun imports =>
      imports.foldl (init := {}) fun state entries =>
        entries.foldl (init := state) addReplayRulePattern
  }

/-- A resolved inference replay implementation. -/
inductive ReplayRuleImplementation where
  | declaration (declName : Name) (handler : ReplayRuleHandler)
  | pattern (handler : ReplayRulePatternHandler)
      (condition : Option (ReplayConditionRef × ReplayConditionHandler))

/-- A resolved inference replay implementation and its dispatch priority. -/
structure ResolvedReplayRuleHandler where
  priority : Nat
  implementation : ReplayRuleImplementation

/-- Rule-indexed replay handlers, with the empty key reserved for wildcard handlers. -/
abbrev ReplayRuleRegistry :=
  Std.HashMap String (Array ResolvedReplayRuleHandler)

unsafe def getReplayRuleHandlersUnsafe : MetaM ReplayRuleRegistry := do
  let env ← getEnv
  let options ← getOptions
  let mut result : ReplayRuleRegistry := {}
  for (rule, entries) in (crushReplayRuleExt.getState env).toList do
    let handlers ← entries.filterMapM fun entry => do
      match env.evalConst ReplayRuleHandler options entry.declName with
      | .ok handler =>
        return some {
          priority := entry.priority
          implementation := .declaration entry.declName handler
        }
      | .error error =>
        throwError "failed to evaluate replay rule handler `{entry.declName}`: {error}"
    result := result.insert rule handlers
  for (rule, entries) in (crushReplayRulePatternExt.getState env).toList do
    let entries ← entries.mapM fun entry => do
      let condition ← entry.condition.mapM fun reference => do
        match env.evalConst ReplayConditionHandler options reference.declName with
        | .ok condition =>
          return (reference, condition)
        | .error error =>
          throwError "failed to evaluate replay condition \
            `{reference.label}`: {error}"
      return (entry, condition)
    result := result.alter rule fun current =>
      let current := current.getD #[]
      some <| entries.foldl (init := current) fun result entry =>
        result.push {
          priority := entry.1.priority
          implementation := .pattern entry.1 entry.2
        }
  for (rule, handlers) in result.toList do
    result := result.insert rule
      (handlers.qsort fun left right => left.priority > right.priority)
  return result

@[implemented_by getReplayRuleHandlersUnsafe]
opaque getReplayRuleHandlers : MetaM ReplayRuleRegistry

/-- Run exact-rule handlers followed by wildcard handlers. -/
def runReplayRuleHandlers (registry : ReplayRuleRegistry)
    (ctx : ReplayRuleContext) : TacticM (Option Expr) := do
  let handlers := registry.getD ctx.rule #[] ++ registry.getD "" #[]
  for entry in handlers do
    let saved ← saveState
    let snapshot ← KernelCheckSnapshot.capture
    try
      let result ←
        match entry.implementation with
        | .declaration _ handler =>
          handler ctx
        | .pattern handler condition => do
          let mut result := none
          for alternative in handler.alternatives do
            if alternative.rule == ctx.rule then
              if let some matched ← ctx.matchArgs alternative.args then
                if let some (reference, condition) := condition then
                  let applies ← try
                    liftMetaM <| withoutModifyingState (condition matched)
                  catch exception =>
                    throwError "replay condition `{reference.label}` failed:\n\
                      {exception.toMessageData}"
                  unless applies do
                    continue
                result ← matched.runTacticWithScopeFallback handler.tactic
                if result.isSome then break
          pure result
      match result with
      | some proof =>
        let proof ← kernelCheckProof snapshot ctx.target proof
        return some proof
      | none =>
        restoreState saved
    catch exception =>
      restoreState saved
      let source :=
        match entry.implementation with
        | .declaration declName _ => m!"handler `{declName}`"
        | .pattern _ _ => m!"pattern for `{ctx.rule}`"
      throwError "replay rule {source} failed:\n{exception.toMessageData}"
  return none

/-! ## Registration DSL -/

declare_syntax_cat crushReplaySymbol
declare_syntax_cat crushReplaySexpPattern
declare_syntax_cat crushReplayExprPattern
declare_syntax_cat crushReplayRulePattern
declare_syntax_cat crushReplayTermPattern

namespace ReplayParser

open Lean.Parser

def sexpKeyword : Parser := nonReservedSymbol "sexp"
def termKeyword : Parser := nonReservedSymbol "term"
def natKeyword : Parser := nonReservedSymbol "nat"
def intKeyword : Parser := nonReservedSymbol "int"
def stringKeyword : Parser := nonReservedSymbol "string"
def atomKeyword : Parser := nonReservedSymbol "atom"
def sortKeyword : Parser := nonReservedSymbol "sort"
def propKeyword : Parser := nonReservedSymbol "prop"
def ruleKeyword : Parser := nonReservedSymbol "rule"
def fencedTerm : Parser := withForbidden ">>" termParser
def fencedCondition : Parser := withForbidden "=>" termParser
def fencedTacticSeq : Parser :=
  withForbidden ">>" Lean.Parser.Tactic.tacticSeq

end ReplayParser

syntax ident : crushReplaySymbol
syntax str : crushReplaySymbol

syntax (name := crushReplaySexpIgnore) "_" : crushReplaySexpPattern
syntax (name := crushReplaySexpRest) ".." : crushReplaySexpPattern
syntax (name := crushReplaySexpString) str : crushReplaySexpPattern
syntax (name := crushReplaySexpNat) num : crushReplaySexpPattern
syntax (name := crushReplaySexpAtom) ident : crushReplaySexpPattern
syntax (name := crushReplaySexpExactAtom)
  "(" ReplayParser.atomKeyword str ")" : crushReplaySexpPattern
syntax (name := crushReplaySexpCapture)
  "(" ReplayParser.sexpKeyword ident ")" : crushReplaySexpPattern
syntax (name := crushReplayTermCapture)
  "(" ReplayParser.termKeyword ident ")" : crushReplaySexpPattern
syntax (name := crushReplayTypedTermCapture)
  "(" ReplayParser.termKeyword ident " : " term ")" : crushReplaySexpPattern
syntax (name := crushReplayNatCapture)
  "(" ReplayParser.natKeyword ident ")" : crushReplaySexpPattern
syntax (name := crushReplayIntCapture)
  "(" ReplayParser.intKeyword ident ")" : crushReplaySexpPattern
syntax (name := crushReplayStringCapture)
  "(" ReplayParser.stringKeyword ident ")" : crushReplaySexpPattern
syntax (name := crushReplayAtomCapture)
  "(" ReplayParser.atomKeyword ident ")" : crushReplaySexpPattern
syntax (name := crushReplaySortCapture)
  "(" ReplayParser.sortKeyword ident ")" : crushReplaySexpPattern
syntax (name := crushReplayPropCapture)
  "(" ReplayParser.propKeyword ident ")" : crushReplaySexpPattern
syntax (name := crushReplaySexpList)
  "(" crushReplaySexpPattern* ")" : crushReplaySexpPattern

syntax (name := crushReplayExprIgnore) "_" : crushReplayExprPattern
syntax (name := crushReplayExprRest) ".." : crushReplayExprPattern
syntax (name := crushReplayExprTerm)
  "(" ReplayParser.termKeyword ident ")" : crushReplayExprPattern
syntax (name := crushReplayExprTypedTerm)
  "(" ReplayParser.termKeyword ident " : " term ")" : crushReplayExprPattern

syntax (name := crushReplayRulePat)
  "(" crushReplaySymbol crushReplaySexpPattern* ")" : crushReplayRulePattern
syntax (name := crushReplayOrdinaryTermPat)
  "(" crushReplaySymbol crushReplayExprPattern* ")" : crushReplayTermPattern
syntax (name := crushReplayIndexedTermPat)
  "(" "(" "_" crushReplaySymbol crushReplaySexpPattern* ")"
    crushReplayExprPattern* ")" : crushReplayTermPattern

/--
Register an Alethe inference handler written as a pattern and a Lean tactic.

The tactic runs against a closed goal containing only the replayed premises and
values captured by the pattern.
-/
syntax (name := registerCrushReplayRule)
  "register_crush_replay" ReplayParser.ruleKeyword (ppSpace prio)? ppSpace
    "<<" ppLine crushReplayRulePattern
    (ppSpace "|" ppSpace crushReplayRulePattern)*
    (ppSpace "if" ppSpace ReplayParser.fencedCondition)? ppSpace "=>" ppSpace
    "by" ppSpace ReplayParser.fencedTacticSeq ppLine ">>" : command

/--
Register the inverse of a custom SMT operator as a pattern and Lean term.
-/
syntax (name := registerCrushReplayTerm)
  "register_crush_replay" ReplayParser.termKeyword (ppSpace prio)? ppSpace
    "<<" ppLine crushReplayTermPattern
    (ppSpace "|" ppSpace crushReplayTermPattern)* ppSpace "=>" ppSpace
    ReplayParser.fencedTerm ppLine ">>" : command

open Elab.Command in
private partial def replaySymbolString (stx : Syntax) : CommandElabM String := do
  if let some value := stx.isStrLit? then
    return value
  if stx.isIdent then
    return stx.getId.toString
  match stx.getArgs with
  | #[child] => replaySymbolString child
  | _ => throwErrorAt stx "expected an SMT symbol identifier or string"

open Elab.Command in
private partial def elabReplaySexpPattern
    (stx : Syntax) : CommandElabM ReplaySexpPattern := do
  match stx with
  | `(crushReplaySexpPattern| _) =>
    return .ignore
  | `(crushReplaySexpPattern| ..) =>
    return .rest
  | `(crushReplaySexpPattern| $value:str) =>
    let some value := value.raw.isStrLit?
      | throwErrorAt value "invalid string pattern"
    return .exactString value
  | `(crushReplaySexpPattern| $value:num) =>
    let some value := value.raw.isNatLit?
      | throwErrorAt value "invalid numeral pattern"
    return .exactNat value
  | `(crushReplaySexpPattern| (atom $value:str)) =>
    let some value := value.raw.isStrLit?
      | throwErrorAt value "invalid atom pattern"
    return .exactAtom value
  | `(crushReplaySexpPattern| (sexp $name:ident)) =>
    return .sexp name.getId.eraseMacroScopes
  | `(crushReplaySexpPattern| (term $name:ident)) =>
    return .term name.getId.eraseMacroScopes none
  | `(crushReplaySexpPattern| (term $name:ident : $type:term)) =>
    return .term name.getId.eraseMacroScopes (some type)
  | `(crushReplaySexpPattern| (nat $name:ident)) =>
    return .nat name.getId.eraseMacroScopes
  | `(crushReplaySexpPattern| (int $name:ident)) =>
    return .int name.getId.eraseMacroScopes
  | `(crushReplaySexpPattern| (string $name:ident)) =>
    return .string name.getId.eraseMacroScopes
  | `(crushReplaySexpPattern| (atom $name:ident)) =>
    return .atom name.getId.eraseMacroScopes
  | `(crushReplaySexpPattern| (sort $name:ident)) =>
    return .sort name.getId.eraseMacroScopes
  | `(crushReplaySexpPattern| (prop $name:ident)) =>
    return .prop name.getId.eraseMacroScopes
  | `(crushReplaySexpPattern| ($patterns:crushReplaySexpPattern*)) =>
    return .list (← patterns.mapM elabReplaySexpPattern)
  | `(crushReplaySexpPattern| $value:ident) =>
    return .exactAtom value.getId.toString
  | _ =>
    throwErrorAt stx "unsupported replay S-expression pattern"

open Elab.Command in
private def elabReplayExprPattern
    (stx : Syntax) : CommandElabM ReplayExprPattern := do
  match stx with
  | `(crushReplayExprPattern| _) =>
    return .ignore
  | `(crushReplayExprPattern| ..) =>
    return .rest
  | `(crushReplayExprPattern| (term $name:ident)) =>
    return .term name.getId.eraseMacroScopes none
  | `(crushReplayExprPattern| (term $name:ident : $type:term)) =>
    return .term name.getId.eraseMacroScopes (some type)
  | _ =>
    throwErrorAt stx "unsupported replay expression pattern"

private partial def replaySexpPatternCaptures (stx : Syntax) : Array Name :=
  match stx with
  | `(crushReplaySexpPattern| (sexp $name:ident))
  | `(crushReplaySexpPattern| (term $name:ident))
  | `(crushReplaySexpPattern| (term $name:ident : $_))
  | `(crushReplaySexpPattern| (nat $name:ident))
  | `(crushReplaySexpPattern| (int $name:ident))
  | `(crushReplaySexpPattern| (string $name:ident))
  | `(crushReplaySexpPattern| (atom $name:ident))
  | `(crushReplaySexpPattern| (sort $name:ident))
  | `(crushReplaySexpPattern| (prop $name:ident)) =>
    #[name.getId.eraseMacroScopes]
  | `(crushReplaySexpPattern| ($patterns:crushReplaySexpPattern*)) =>
    patterns.foldl
      (fun captures pattern =>
        captures ++ replaySexpPatternCaptures pattern) #[]
  | _ =>
    #[]

private def replayExprPatternCaptures (stx : Syntax) : Array Name :=
  match stx with
  | `(crushReplayExprPattern| (term $name:ident))
  | `(crushReplayExprPattern| (term $name:ident : $_)) =>
    #[name.getId.eraseMacroScopes]
  | _ =>
    #[]

open Elab.Command in
private partial def resolveReplaySyntax
    (captures : Array Name) : Syntax → CommandElabM Syntax
  | .ident info rawVal value preResolved => do
    if captures.contains value.eraseMacroScopes then
      return .ident info rawVal value preResolved
    let declarations ← resolveGlobalName value (enableLog := false)
    let namespaces ← resolveNamespaceCore value (allowEmpty := true)
    let preResolved :=
      declarations.map (fun (name, fields) =>
        Syntax.Preresolved.decl name fields) ++
      namespaces.map Syntax.Preresolved.namespace ++
      preResolved
    return .ident info rawVal value preResolved
  | .node info kind args =>
    return .node info kind (← args.mapM (resolveReplaySyntax captures))
  | stx =>
    return stx

open Elab.Command in
private partial def resolveReplaySexpPattern
    (captures : Array Name) :
    ReplaySexpPattern → CommandElabM ReplaySexpPattern
  | .term name (some guard) =>
    return .term name (some ⟨← resolveReplaySyntax captures guard.raw⟩)
  | .list patterns =>
    return .list (← patterns.mapM (resolveReplaySexpPattern captures))
  | pattern =>
    return pattern

open Elab.Command in
private def resolveReplayExprPattern
    (captures : Array Name) :
    ReplayExprPattern → CommandElabM ReplayExprPattern
  | .term name (some guard) =>
    return .term name (some ⟨← resolveReplaySyntax captures guard.raw⟩)
  | pattern =>
    return pattern

private def validateReplayCaptures
    (alternatives : Array (Syntax × Array Name)) :
    Elab.Command.CommandElabM Unit := do
  let some (firstSyntax, expected) := alternatives[0]? | return
  for i in [:expected.size] do
    if expected.extract 0 i |>.contains expected[i]! then
      throwErrorAt firstSyntax
        s!"duplicate replay pattern binding `{expected[i]!}`"
  for (stx, captures) in alternatives do
    for i in [:captures.size] do
      if captures.extract 0 i |>.contains captures[i]! then
        throwErrorAt stx
          s!"duplicate replay pattern binding `{captures[i]!}`"
    unless captures.size == expected.size &&
        captures.all expected.contains do
      throwErrorAt stx
        s!"all replay pattern alternatives must bind the same names; \
          expected {expected}, got {captures}"

open Elab Command in
private def compileReplayCondition
    (condition : TSyntax `term) : CommandElabM ReplayConditionRef :=
  liftTermElabM do
    let valueSyntax ←
      `(fun ctx => ReplayCondition.check $condition ctx)
    let type := mkConst ``ReplayConditionHandler
    let value ← Term.withoutErrToSorry <| Term.withSynthesize <|
      Term.elabTermEnsuringType valueSyntax type
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    if value.hasSorry then
      throwErrorAt condition "replay condition contains `sorry`"
    if value.hasMVar || value.hasLevelMVar then
      throwErrorAt condition
        "replay condition contains unresolved metavariables"
    let name :=
      mkPrivateName (← getEnv)
        (← mkFreshUserName `_crushReplayCondition)
    let declaration ←
      mkDefinitionValInferringUnsafe name [] type value .opaque
    addAndCompile <| .defnDecl declaration
    return {
      declName := name
      label := condition.raw.reprint.getD "condition" |>.trimAscii.toString
    }

private structure ExpandedReplayRulePattern where
  source : Syntax
  ruleName : String
  args : Array ReplaySexpPattern
  captures : Array Name

open Elab.Command in
private def expandReplayRulePattern
    (stx : Syntax) : CommandElabM ExpandedReplayRulePattern := do
  let `(crushReplayRulePattern|
      ($rule:crushReplaySymbol $patterns:crushReplaySexpPattern*)) := stx
    | throwErrorAt stx "invalid replay rule pattern"
  return {
    source := stx
    ruleName := ← replaySymbolString rule
    args := ← patterns.mapM elabReplaySexpPattern
    captures := patterns.foldl
      (fun captures pattern =>
        captures ++ replaySexpPatternCaptures pattern) #[]
  }

private structure ExpandedReplayTermPattern where
  source : Syntax
  head : String
  indices : Array ReplaySexpPattern
  args : Array ReplayExprPattern
  captures : Array Name

open Elab.Command in
private def expandReplayTermPattern
    (stx : Syntax) : CommandElabM ExpandedReplayTermPattern := do
  match stx with
  | `(crushReplayTermPattern|
      ($head:crushReplaySymbol $args:crushReplayExprPattern*)) =>
    return {
      source := stx
      head := ← replaySymbolString head
      indices := #[]
      args := ← args.mapM elabReplayExprPattern
      captures := args.foldl
        (fun captures pattern =>
          captures ++ replayExprPatternCaptures pattern) #[]
    }
  | `(crushReplayTermPattern|
      ((_ $head:crushReplaySymbol $indices:crushReplaySexpPattern*)
        $args:crushReplayExprPattern*)) =>
    return {
      source := stx
      head := ← replaySymbolString head
      indices := ← indices.mapM elabReplaySexpPattern
      args := ← args.mapM elabReplayExprPattern
      captures :=
        indices.foldl
          (fun captures pattern =>
            captures ++ replaySexpPatternCaptures pattern) #[] ++
        args.foldl
          (fun captures pattern =>
            captures ++ replayExprPatternCaptures pattern) #[]
    }
  | _ =>
    throwErrorAt stx "invalid replay term pattern"

open Elab Command in
elab_rules : command
  | `(command| register_crush_replay rule $[$priority:prio]?
      << $first:crushReplayRulePattern
         $[| $rest:crushReplayRulePattern]*
         $[if $condition:term]? =>
        by $tactics:tacticSeq >>) => do
    let alternatives ←
      (#[first.raw] ++ rest.map (·.raw)).mapM expandReplayRulePattern
    validateReplayCaptures
      (alternatives.map fun alternative =>
        (alternative.source, alternative.captures))
    let some first := alternatives[0]?
      | throwError "replay registration requires at least one pattern"
    let captures := first.captures
    let alternatives ← alternatives.mapM fun alternative => do
      return {
        alternative with
        args := ← alternative.args.mapM
          (resolveReplaySexpPattern captures)
      }
    let priority ←
      match priority with
      | some priority => liftMacroM <| evalPrio priority
      | none => pure (eval_prio default)
    let tactic ← `(tactic| ($tactics))
    let tactic : TSyntax `tactic :=
      ⟨← resolveReplaySyntax captures tactic.raw⟩
    let condition ← condition.mapM compileReplayCondition
    let alternatives := alternatives.map fun alternative => {
      rule := alternative.ruleName
      args := alternative.args
    }
    modifyEnv fun env =>
      crushReplayRulePatternExt.addEntry env {
        alternatives
        condition
        tactic
        priority
      }
  | `(command| register_crush_replay term $[$priority:prio]?
      << $first:crushReplayTermPattern
         $[| $rest:crushReplayTermPattern]* =>
        $body:term >>) => do
    let alternatives ←
      (#[first.raw] ++ rest.map (·.raw)).mapM expandReplayTermPattern
    validateReplayCaptures
      (alternatives.map fun alternative =>
        (alternative.source, alternative.captures))
    let some first := alternatives[0]?
      | throwError "replay registration requires at least one pattern"
    let captures := first.captures
    let alternatives ← alternatives.mapM fun alternative => do
      return {
        alternative with
        indices := ← alternative.indices.mapM
          (resolveReplaySexpPattern captures)
        args := ← alternative.args.mapM
          (resolveReplayExprPattern captures)
      }
    let priority ←
      match priority with
      | some priority => liftMacroM <| evalPrio priority
      | none => pure (eval_prio default)
    let body : TSyntax `term :=
      ⟨← resolveReplaySyntax captures body.raw⟩
    let alternatives := alternatives.map fun alternative => {
      head := alternative.head
      indices := alternative.indices
      args := alternative.args
    }
    modifyEnv fun env =>
      crushReplayTermPatternExt.addEntry env {
        alternatives
        body
        priority
      }

end Crush
