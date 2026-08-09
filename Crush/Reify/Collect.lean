import Lean
import Lean.LibrarySuggestions.Default
import Crush.Translation.Monad
import Crush.Translation.Unfold
open Lean Meta

/-!
# Collecting facts from the goal

Gathers the propositions to send to the solver: local hypotheses (those of type
`Prop`), explicit user-provided term hints, equation lemmas from unfold/defeq hints,
and the goal itself. The goal is *negated* — `crush` proves `G` by asserting the
hypotheses together with `¬G` and checking for `unsat`, the standard refutation
setup.

The set of facts is governed by `Hints` (parsed from the tactic's argument grammar,
see `Crush/Frontend/Tactic.lean`):

* bare `crush` collects **all** local `Prop` hypotheses (the common case);
* `crush [t₁, …]` collects only the listed terms (plus the goal), matching
  Sledgehammer/`auto` semantics where an explicit list is a *restriction*;
* `crush [t₁, …, *]` collects the listed terms **and** all local hypotheses;
* `crush u[f]` adds `f`'s equation lemmas (definitional unfolding);
* `crush d[f]` adds `f`'s unfold equation (`f x = …`) as a definitional equality.

Each collected fact carries a `descr` for provenance, so an unsat core or a failure
message can name its source. Optional premise selection uses Lean core's
`LibrarySuggestions` engine.
-/

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
  explicit hints and selected library premises, not every local hypothesis. -/
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

/-- Collect assertable facts from `goal` under `hints`, plus the (negated) goal.
Returns the facts and leaves the goal untouched (the tactic decides how to close
it). Only `Prop` propositions are collected; the goal's type is negated. -/
def collectFactsWithRewrite (goal : MVarId) (hints : Hints := {})
    (autoUnfold : Bool := true) (premiseMax : Nat := 0) : MetaM FactCollection :=
  goal.withContext do
    let mut facts := #[]
    -- Constants seen across goal + hypotheses + hints, seeding auto-unfold relevance.
    -- The goal/hyp types are instantiated first: after a tactic like `induction` the
    -- goal type carries unassigned metavariables that `getUsedConstants` does not
    -- traverse, so without this a constant like the recursive function under proof is
    -- invisible to relevance and its `@[crush_unfold]` equations never get folded in.
    let mut seeds : Array Name := #[]
    let mut seenPremises : Std.HashSet Name := {}
    let goalType ← instantiateMVars (← goal.getType)
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
            descr := s!"hyp {decl.userName}" }
    -- Explicit term hints (lemmas or hypotheses the user named).
    for (proof, descr) in hints.terms do
      -- Re-abstract leftover mvars into leading binders. Elaborating a bare
      -- polymorphic lemma (`crush [List.append_assoc]`) auto-binds its `{α}` into a
      -- metavariable, so the fact arrives as `∀ (as … : List ?m), …` — the leading
      -- type binder gone, reading as monomorphic over an abstract sort disconnected
      -- from the goal, which monomorphization then can't specialize. `abstractMVars`
      -- restores the `∀ α`-binder (sound: the abstracted term proves the more general
      -- proposition by construction); a hint with no leftover mvars is unchanged.
      -- `levels := false` keeps each unassigned universe an mvar, not a rigid param —
      -- else `Type u` would not unify with a candidate's `Type 0` and the fact would
      -- stay un-instantiable, the very failure this fixes.
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
    -- Lean core's premise selector supplies relevant library theorems. Keep this
    -- bounded and proposition-only; selected polymorphic theorems flow through
    -- the same monomorphization path as explicit hints.
    let mut selectedPremises := 0
    if premiseMax > 0 && hints.allowPremiseSelection then
      let suggestions ← Lean.LibrarySuggestions.select goal {
        maxSuggestions := premiseMax
        caller := some "crush"
        filter := fun name => do
          let some info := (← getEnv).find? name | return false
          isProp info.type }
      for suggestion in suggestions do
        if selectedPremises >= premiseMax then break
        if seenPremises.contains suggestion.name then continue
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
    -- Equation lemmas from `u[…]`/`d[…]` hints. Fresh level metavariables so a
    -- universe-polymorphic equation lemma instantiates at use.
    let mut eqnLemmas := hints.eqnLemmas
    -- Auto-unfold: equation lemmas of `@[crush_unfold]`/`@[crush_defeq]` definitions
    -- reachable from the collected constants. Relevance-filtered so an unrelated marked
    -- definition contributes nothing (see `relevantAutoUnfoldLemmas`). Explicit hints
    -- still win — a name already requested by `u[…]`/`d[…]` is de-duplicated below.
    if autoUnfold then
      eqnLemmas := eqnLemmas ++ (← relevantAutoUnfoldLemmas seeds)
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
    return { facts, rewriteLemmas := eqnLemmas, selectedPremises }

/-- Compatibility wrapper returning only the collected fact array. -/
def collectFacts (goal : MVarId) (hints : Hints := {}) (autoUnfold : Bool := true) :
    MetaM (Array Fact) := do
  return (← collectFactsWithRewrite goal hints autoUnfold).facts

end Crush
