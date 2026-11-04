import Lean
import Lean.LibrarySuggestions.Default
import Crush.Translation.Monad
import Crush.Translation.Unfold
import Crush.Solver.KernelCheck

/-!
# Collecting facts from the goal

Collect local propositions, visible local data equations, explicit hints, relevant
unfolding equations, optional library premises, and the negated goal. Bare `crush`
uses all local facts; an explicit list restricts them unless it contains `*`.
Each fact retains its proof and source description for trusted discharge,
reconstruction, and diagnostics. Polymorphic hints are prepared for specialization.
-/

open Lean Meta

namespace Crush

/-- A proposition to assert, with its provenance. `negated` marks the (single)
negated goal so diagnostics can distinguish it. -/
structure Fact where
  /-- The proposition (a `Prop`-typed `Expr`). -/
  prop    : Expr
  /-- The proof of `prop`, when it is a hypothesis (none for the negated goal). -/
  proof   : Option Expr
  descr   : String
  negated : Bool := false
  /-- For a rewritten negated goal, a proof of `originalNegation → prop`.
  Alethe replay applies it to the original `¬goal` hypothesis before replaying
  the normalized assertion. Ordinary facts carry their rewritten proof directly. -/
  negationTransform : Option Expr := none
  /-- A specialized equality connecting the original negated goal to its
  normalized assertion. Core-directed reconstruction always receives this bridge,
  because the solver no longer needs to cite the equations after rewriting. -/
  reconstructionProof : Option Expr := none
  /-- Equation facts remain quantified SMT fallbacks but are not normalized by
  their own rewrite rule. -/
  isEquation : Bool := false
  /-- Generate bounded ground instances before SMT translation. Enabled for
  explicit hints, selected library premises, and local hypotheses when `*` is
  present in an explicit hint list. -/
  instantiateTerms : Bool := false
  /-- Proof of the quantified fact that produced this ground instance. Retained
  as provenance even when preprocessing replaces the parent assertion. -/
  instanceOf : Option Expr := none
  deriving Inhabited

/-- The resolved fact sources requested by the tactic's argument grammar. Produced
by the tactic front-end; `collectFacts` turns it into the actual `Fact` array.

`terms` are proof terms the user named explicitly (lemmas or hypotheses); `eqnLemma`
names are equation lemmas already resolved from `u[…]`/`d[…]` hints. `allHyps`
requests every local `Prop` hypothesis — the default when no `[…]` list is given, or
when the list contains `*`. -/
structure Hints where
  /-- Explicit proof terms (already elaborated) with a description each. -/
  terms    : Array (Expr × String) := #[]
  /-- Equation-lemma constant names gathered from `u[…]`/`d[…]`. -/
  eqnLemmas : Array Name := #[]
  /-- Whether to sweep in every local `Prop` hypothesis. -/
  allHyps  : Bool := true
  /-- Whether swept local hypotheses enter bounded ground instantiation.
  Bare `crush` leaves this off; an explicit `*` turns it on. -/
  instantiateHyps : Bool := false
  /-- Whether automatic library premise selection may add facts. An explicit
  `[...]` list sets this to false so the list remains a strict restriction. -/
  allowPremiseSelection : Bool := true
  deriving Inhabited

/-- Facts plus the selected equations that should normalize them before
monomorphization. `collectFacts` remains as the compatibility wrapper returning
only `facts`; the tactic driver uses this richer result. -/
structure FactCollection where
  facts            : Array Fact := #[]
  rewriteLemmas    : Array Name := #[]
  selectedPremises : Nat := 0
  deriving Inhabited

/-- Whether a library theorem can be used as a backward rule for the current goal.

Library suggestion engines optimize for recall and may return propositions that merely
share vocabulary with the goal. Sending those propositions to SMT is both expensive and,
for highly polymorphic higher-order lemmas, can create irrelevant encodings. This
speculative `apply` check retains rules whose conclusions really unify with the goal and
rolls back every metavariable assignment it makes. -/
private def premiseAppliesToGoal (goal : MVarId) (declName : Name) : MetaM Bool :=
  goal.withContext do
    let saved ← saveState
    try
      let proof ← mkConstWithFreshMVarLevels declName
      discard <| goal.apply proof
      restoreState saved
      return true
    catch _ =>
      restoreState saved
      return false

/-- Require a proposition before forming the negated SMT goal. -/
def getPropositionalGoalType (goal : MVarId) : MetaM Expr := goal.withContext do
  let goalType ← instantiateMVars (← goal.getType)
  unless ← isProp goalType do
    throwError "crush: expected a proposition, but the goal has type `{goalType}`"
  return goalType

/-- Collect assertable facts from `goal` under `hints`, plus the (negated) goal.
Returns the facts and leaves the goal untouched (the tactic decides how to close
it). Only `Prop` propositions are collected; the goal's type is negated. -/
def collectFactsWithRewrite (goal : MVarId) (hints : Hints := {})
    (autoUnfold : Bool := true) (premiseMax : Nat := 0) : MetaM FactCollection :=
  goal.withContext do
    let mut facts := #[]
    -- Instantiate goal and hypothesis types before collecting relevance seeds;
    -- getUsedConstants does not follow assigned metavariables.
    let mut seeds : Array Name := #[]
    let mut seenPremises : Std.HashSet Name := {}
    let goalType ← getPropositionalGoalType goal
    seeds := seeds ++ goalType.getUsedConstants
    -- Local hypotheses, unless an explicit `[…]` list without `*` restricts us.
    if hints.allHyps then
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let ty ← instantiateMVars decl.type
        if (← isProp ty) then
          seeds := seeds ++ ty.getUsedConstants
          facts := facts.push {
            prop := ty
            proof := decl.toExpr
            descr := s!"hyp {decl.userName}"
            instantiateTerms := hints.instantiateHyps }
        else if !ty.consumeMData.isSort then
          -- Retain the defining equality of visible data lets; value? hides opaque have values.
          if let some value := decl.value? then
            let value ← instantiateMVars value
            let prop ← mkEq decl.toExpr value
            let proof := mkApp2 (mkConst ``id [0]) prop (← mkEqRefl value)
            seeds := seeds ++ prop.getUsedConstants
            facts := facts.push {
              prop
              proof := some proof
              descr := s!"let {decl.userName}" }
    -- Explicit term hints (lemmas or hypotheses the user named).
    for (proof, descr) in hints.terms do
      -- Restore leading binders for implicit hint parameters so monomorphization
      -- can specialize them. Keep universe metavariables flexible with levels := false;
      -- rigid universe parameters would prevent matching concrete query types.
      let proof ← if proof.hasExprMVar || proof.hasLevelMVar
                  then do pure (← abstractMVars proof (levels := false)).expr
                  else pure proof
      let ty ← inferType proof
      if (← isProp ty) then
        if let .const name _ := proof.getAppFn then
          seenPremises := seenPremises.insert name
        seeds := seeds ++ ty.getUsedConstants
        facts := facts.push {
          prop := ty
          proof := proof
          descr
          instantiateTerms := true }
      else
        throwError "crush: {descr} has type `{ty}`, which is not a `Prop`; \
                    only propositions can be asserted as facts."
    -- Bound library suggestions and send selected polymorphic proofs through specialization.
    let mut selectedPremises := 0
    if premiseMax > 0 && hints.allowPremiseSelection then
      -- Request a small surplus because selectors may ignore Config.filter;
      -- otherwise irrelevant suggestions can crowd usable rules out of the prefix.
      let candidateMax := min 128 (premiseMax * 4)
      let suggestions ← Lean.LibrarySuggestions.select goal {
        maxSuggestions := candidateMax
        caller := some "crush"
        filter := fun name => do
          let some info := (← getEnv).find? name | return false
          unless ← isProp info.type do return false
          return (← forbiddenReconstructionAxiom? name).isNone }
      for suggestion in suggestions do
        if selectedPremises >= premiseMax then break
        if seenPremises.contains suggestion.name then continue
        -- Selectors may ignore their filter. Never automatically select an
        -- admitted theorem; ordinary user axioms remain eligible premises.
        if (← forbiddenReconstructionAxiom? suggestion.name).isSome then continue
        unless ← premiseAppliesToGoal goal suggestion.name do continue
        seenPremises := seenPremises.insert suggestion.name
        let proof ← mkConstWithFreshMVarLevels suggestion.name
        let ty ← inferType proof
        unless ← isProp ty do continue
        seeds := seeds ++ ty.getUsedConstants
        facts := facts.push {
          prop := ty
          proof := some proof
          descr := s!"premise {suggestion.name}"
          instantiateTerms := true }
        selectedPremises := selectedPremises + 1
    -- Fresh universe metavariables let explicit equation hints specialize at use.
    let mut eqnLemmas := hints.eqnLemmas
    let mut rewriteLemmas := hints.eqnLemmas
    -- Collect only reachable marked equations; explicit unfolding hints take precedence.
    if autoUnfold then
      eqnLemmas := eqnLemmas ++ (← relevantAutoUnfoldLemmas seeds)
      rewriteLemmas := eqnLemmas ++ (← relevantReducibleRewriteLemmas seeds)
    else
      rewriteLemmas := eqnLemmas
    let mut seenEqn : Std.HashSet Name := {}
    for lemName in eqnLemmas do
      if seenEqn.contains lemName then continue
      seenEqn := seenEqn.insert lemName
      let proof ← mkConstWithFreshMVarLevels lemName
      let ty ← inferType proof
      if (← isProp ty) then
        facts := facts.push {
          prop := ty
          proof := proof
          descr := s!"eqn {lemName}"
          isEquation := true }
    -- The negated goal.
    facts := facts.push {
      prop := mkNot goalType
      proof := none
      descr := "negated goal"
      negated := true }
    return { facts, rewriteLemmas, selectedPremises }

/-- Compatibility wrapper returning only the collected fact array. -/
def collectFacts (goal : MVarId) (hints : Hints := {}) (autoUnfold : Bool := true) :
    MetaM (Array Fact) := do
  return (← collectFactsWithRewrite goal hints autoUnfold).facts

end Crush
