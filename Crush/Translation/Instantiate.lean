import Lean
import Lean.Meta.Sym
import Crush.Frontend.Config
import Crush.Frontend.Collect
import Crush.Translation.Pattern

open Lean Meta

/-!
# Proof-producing ground term instantiation

SMT E-matching only instantiates a quantified fact after a matching ground term
already exists. This misses common forward chains where one lemma creates the term
that triggers the next:

```
step : ∀ x, R x (next x)
lift : ∀ x y, R x y → P (witness y)
```

This pass generates bounded ground instances of explicit hints and selected library
premises before translation. Pattern matches are preferred: a generated `R a (next
a)` fact directly determines the `x := a, y := next a` instance of `lift`. If no
pattern matches yet, ground query terms seed triggerless lemmas such as `step`.

Every generated proposition is obtained by applying the original Lean proof term.
The pass therefore adds only logical consequences of user-supplied facts. A
ground-first query may omit instantiated universal templates to prevent SMT
E-matching from recreating unbounded term growth. The complete fallback always
retains every original fact: finitely many ground instances cannot replace a
universal fact when proving a quantified goal.
-/

namespace Crush

/-- Normalize expressions on entry to symbolic matching. `Sym.isDefEqI` assumes
reducible declarations have already been unfolded, and maximal sharing makes its
pointer-keyed caches effective. -/
private def preprocessExprS (e : Expr) : Sym.SymM Expr := do
  let e ← Sym.instantiateMVarsS e
  Sym.shareCommon (← Sym.unfoldReducible e)

/-- Result and diagnostics for bounded ground instantiation. -/
structure InstantiationReport where
  facts       : Array Fact := #[]
  /-- A soundly weakened first query containing generated instances but omitting
  their quantified templates. This is offered only after reaching a fixpoint:
  a truncated instance set is unlikely to prove the goal and can consume the
  full solver timeout before the complete `facts` query is tried. If this query
  is satisfiable or unknown, callers retry with `facts`; an unsatisfiable result
  is already conclusive. -/
  groundFacts : Option (Array Fact) := none
  generated   : Nat := 0
  exhausted   : Bool := false
  deriving Inhabited

private structure GroundOccurrence where
  expr    : Expr
  head?   : Option Expr := none
  origins : Array Nat := #[]
  deriving Inhabited

private structure GroundCandidate where
  expr : Expr
  type : Expr
  deriving Inhabited

private structure GroundCollection where
  terms       : Array GroundCandidate := #[]
  occurrences : Array Expr := #[]

private structure OccurrenceIndex where
  byHead : Std.HashMap Expr (Array GroundOccurrence) := {}

private structure OccurrenceRoutes where
  head?   : Option Expr := none
  origins : Array (Array Nat) := #[]
  deriving Inhabited

private structure OccurrenceStore where
  byExpr : Std.HashMap Expr OccurrenceRoutes := {}
  order  : Array Expr := #[]

private def isClassType (ty : Expr) : Sym.SymM Bool :=
  return (Sym.isClass? (← getEnv) ty).isSome

/-- Binder domains handled by the simply-typed higher-order encoding. A
nondependent arrow is a first-class value; genuinely dependent functions remain
unsupported by both instantiation and SMT lowering. -/
private def isUnsupportedValueDomain (ty : Expr) : Bool :=
  ty.isSort || (ty.isForall && !ty.isArrow)

private def isPropExpr (e : Expr) : Sym.SymM Bool := do
  let ty ← preprocessExprS (← Sym.inferType e)
  return ty.isProp

@[inline] private def isDefEqS (left right : Expr) : Sym.SymM Bool :=
  if Sym.isSameExpr left right then pure true else Sym.isDefEqI left right

/-- The rigid head of a normalized application. Distinct rigid heads cannot
definitionally match, so they form a cheap occurrence index. -/
private def rigidHead? (e : Expr) : Option Expr :=
  match e with
  | .mdata _ body => rigidHead? body
  | _ => match e.getAppFn with
  | head@(.const ..) | head@(.fvar ..) => some head
  | _ => none

/-- Ground propositions and data terms that a template pattern may match, plus
the data terms suitable for fallback instantiation.

Collect proposition subexpressions as well as whole facts. A useful trigger may
sit below a conjunction, implication, or negation; its polarity is irrelevant
because matching only chooses arguments for an already-proved template.

Classification infers and normalizes each subexpression's type once. Application
spines are traversed by their arguments rather than through every binary prefix:
a proper prefix has function type and can be neither a ground term nor a
proposition occurrence. -/
private partial def collectGround (e : Expr) : Sym.SymM GroundCollection := do
  let terms ← IO.mkRef (#[] : Array GroundCandidate)
  let occurrences ← IO.mkRef (#[] : Array Expr)
  let termSeen ← IO.mkRef ({} : Std.HashSet Expr)
  let occurrenceSeen ← IO.mkRef ({} : Std.HashSet Expr)
  let rec go (e : Expr) : Sym.SymM Unit := do
    if !e.hasLooseBVars && !e.hasExprMVar && !e.hasLevelMVar then
      let classification ←
        try
          let ty ← preprocessExprS (← Sym.inferType e)
          if ty.isProp then
            pure (some (ty, false))
          else if ty.isSort || (ty.isForall && !ty.isArrow) || (← isClassType ty) then
            pure none
          else if ty.isArrow then
            -- Function values participate in application-pattern matching, but
            -- never enter the fallback candidate pool.
            pure (some (ty, false))
          else
            pure (some (ty, true))
        catch _ =>
          pure none
      if let some (ty, isTerm) := classification then
        let seen ← occurrenceSeen.get
        unless seen.contains e do
          occurrenceSeen.set (seen.insert e)
          occurrences.modify (·.push e)
        if isTerm then
          let seen ← termSeen.get
          unless seen.contains e do
            termSeen.set (seen.insert e)
            terms.modify (·.push { expr := e, type := ty })
    match e with
    | .app .. =>
      for arg in e.getAppArgs do go arg
      match e.getAppFn with
      | .lam .. | .letE .. | .mdata .. | .proj .. => go e.getAppFn
      | _ => pure ()
    | .lam _ ty body _ | .forallE _ ty body _ => go ty; go body
    | .letE _ ty value body _ => go ty; go value; go body
    | .mdata _ body | .proj _ _ body => go body
    | _ => pure ()
  go e
  return { terms := ← terms.get, occurrences := ← occurrences.get }

/-- Ground constructor applications must survive instance simplification.

Such a term may be the witness that a generated fact contributes to an
existential goal, or the trigger for another template. Erasing one is a
conservative signal that the simplified proposition could become disconnected
from the query. -/
private partial def collectGroundConstructors (env : Environment) (e : Expr) :
    Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut seen : Std.HashSet Expr := {}
  let rec go (e : Expr) : StateM (Array Expr × Std.HashSet Expr) Unit := do
    let (out, seen) ← get
    if !e.hasLooseBVars && !e.hasExprMVar && !e.hasLevelMVar then
      if let .const name _ := e.getAppFn then
        if env.isConstructor name && !seen.contains e then
          set (out.push e, seen.insert e)
    match e with
    | .app .. =>
      for arg in e.getAppArgs do go arg
      match e.getAppFn with
      | .lam .. | .letE .. | .mdata .. | .proj .. => go e.getAppFn
      | _ => pure ()
    | .lam _ ty body _ | .forallE _ ty body _ => go ty; go body
    | .letE _ ty value body _ => go ty; go value; go body
    | .mdata _ body | .proj _ _ body => go body
    | _ => pure ()
  ((go e).run (out, seen)).2.1

/-- Whether a marked fact can actually produce a ground value instance.

Proposition binders are transparent for this test: a theorem such as
`∀ x, P x → ∀ y, Q y → R x y` can be specialized at both `x` and `y` while
retaining `P x` and `Q y` as premises. Ordinary ground hints and
proposition-only implications still stay out of the template loop. -/
private partial def hasLeadingValueBinder (ty : Expr) : Sym.SymM Bool := do
  match ty with
  | .forallE name dom body info =>
    if ← isPropExpr dom then
      withLocalDecl name info dom fun binder =>
        hasLeadingValueBinder (body.instantiate1 binder)
    else if isUnsupportedValueDomain dom then
      return false
    else if info == .instImplicit && (← isClassType dom) then
      withLocalDecl name info dom fun binder =>
        hasLeadingValueBinder (body.instantiate1 binder)
    else
      return true
  | _ => return false

/-- A closed data term suitable for a leading value binder.

Local free variables are ground query terms. Loose variables, metavariables,
propositions, types, functions, and type-class dictionaries are not. -/
private def isGroundTerm (e : Expr) : Sym.SymM Bool := do
  if e.hasLooseBVars || e.hasExprMVar || e.hasLevelMVar then return false
  try
    let ty ← preprocessExprS (← Sym.inferType e)
    if ty.isProp || isUnsupportedValueDomain ty then return false
    return !(← isClassType ty)
  catch _ =>
    return false

private def binderTypeS (binder : Expr) : Sym.SymM Expr :=
  binder.fvarId!.getType

/-- Open application/proposition patterns containing at least one template binder. -/
private partial def collectGroundPatterns (e : Expr) (binders : Array Expr) :
    Sym.SymM (Array Expr) := do
  let out ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let rec go (e : Expr) : Sym.SymM Unit := do
    if Pattern.containsBinder e binders then
      let isBare :=
        match e with
        | .fvar id => (Pattern.binderIndex? binders id).isSome
        | _ => false
      unless isBare do
        let usable ←
          try
            pure ((← isPropExpr e) || !e.getAppArgs.isEmpty)
          catch _ =>
            pure false
        if usable then
          let known ← seen.get
          unless known.contains e do
            seen.set (known.insert e)
            out.modify (·.push e)
    match e with
    | .app .. =>
      for arg in e.getAppArgs do go arg
      match e.getAppFn with
      | .lam .. | .letE .. | .mdata .. | .proj .. => go e.getAppFn
      | _ => pure ()
    | .lam _ ty body _ | .forallE _ ty body _ => go ty; go body
    | .letE _ ty value body _ => go ty; go value; go body
    | .mdata _ body | .proj _ _ body => go body
    | _ => pure ()
  go e
  out.get

/-- Insert an occurrence in expected constant time while maintaining a provenance
antichain for that expression. A route from fewer producers is eligible for every
template that a superset route is, so supersets only multiply matching work. -/
private def OccurrenceStore.add (store : OccurrenceStore) (expr : Expr)
    (origins : Array Nat := #[]) : OccurrenceStore := Id.run do
  let some routes := store.byExpr.get? expr | return {
    byExpr := store.byExpr.insert expr {
      head? := rigidHead? expr
      origins := #[origins] }
    order := store.order.push expr }
  for existing in routes.origins do
    if Pattern.originsSubset existing origins then return store
  let retained := routes.origins.filter fun existing =>
    !Pattern.originsSubset origins existing
  return { store with
    byExpr := store.byExpr.insert expr {
      routes with origins := retained.push origins } }

private def OccurrenceStore.toArray (store : OccurrenceStore) :
    Array GroundOccurrence := Id.run do
  let mut out := #[]
  for expr in store.order do
    let routes := store.byExpr.getD expr {}
    for origins in routes.origins do
      out := out.push { expr, head? := routes.head?, origins }
  return out

private def indexOccurrences (occurrences : Array GroundOccurrence) :
    OccurrenceIndex :=
  occurrences.foldl (init := {}) fun index occurrence =>
    match occurrence.head? with
    | some head =>
      { index with
        byHead := index.byHead.insert head
          ((index.byHead.getD head #[]).push occurrence) }
    | none => index

/-- Derive complete leading-binder substitutions from matching query expressions. -/
private partial def derivePatternSubstitutions (ty : Expr)
    (occurrences : Array GroundOccurrence) (occurrenceIndex : OccurrenceIndex)
    (templateIndex budget : Nat) :
    Sym.SymM (Array Pattern.Substitution) := do
  if budget == 0 then return #[]
  let derive (openedTy : Expr) (binders : Array Expr) :
      Sym.SymM (Array Pattern.Substitution) := do
    if binders.isEmpty then return #[]
    let patterns ← collectGroundPatterns openedTy binders
    let empty := Array.replicate binders.size none
    let limit := max budget (binders.size * budget)
    let mut evidence : Array Pattern.PartialSubstitution := #[]
    for pattern in patterns do
      if evidence.size >= limit then break
      let matching :=
        match rigidHead? pattern with
        | some head => occurrenceIndex.byHead.getD head #[]
        | none => occurrences
      for occurrence in matching do
        if evidence.size >= limit then break
        if occurrence.origins.contains templateIndex then continue
        if let some subst ← Pattern.matchPattern isGroundTerm Sym.inferType binderTypeS
            isDefEqS pattern occurrence.expr binders empty then
          evidence := Pattern.addEvidence evidence subst occurrence.origins limit
    evidence ← Pattern.closeEvidence isDefEqS evidence limit binders.size
    return Pattern.completeEvidence evidence budget
  let deriveWithPremises (ty : Expr) (binders premises : Array Expr) :
      Sym.SymM (Array Pattern.Substitution) := do
    derive (← Sym.mkForallFVarsS premises ty) binders
  let rec openBinders (ty : Expr) (binders premises : Array Expr) :
      Sym.SymM (Array Pattern.Substitution) := do
    match ty with
    | .forallE name dom body info =>
      if ← isPropExpr dom then
        withLocalDecl name info dom fun premise =>
          openBinders (body.instantiate1 premise) binders
            (premises.push premise)
      else if isUnsupportedValueDomain dom then
        deriveWithPremises ty binders premises
      else if info == .instImplicit && (← isClassType dom) then
        match ← Sym.synthInstance? dom with
        | .some value =>
          openBinders (body.instantiate1 value) binders premises
        | _ => deriveWithPremises ty binders premises
      else
        withLocalDecl name info dom fun binder =>
          openBinders (body.instantiate1 binder) (binders.push binder)
            premises
    | _ => deriveWithPremises ty binders premises
  openBinders (← Sym.instantiateMVarsS ty) #[] #[]

/-- Apply a complete pattern-derived substitution to a quantified proof. -/
private partial def instantiateAt (proof ty : Expr) (values : Array Expr) :
    Sym.SymM (Option (Expr × Expr)) := do
  let rec go (proof ty : Expr) (index : Nat) :
      Sym.SymM (Option (Expr × Expr)) := do
    match ty with
    | .forallE name dom body info =>
      if ← isPropExpr dom then
        withLocalDecl name info dom fun premise => do
          let some (proof, prop) ←
              go (mkApp proof premise) (body.instantiate1 premise) index
            | return none
          return some (
            ← Sym.mkLambdaFVarsS #[premise] proof,
            ← Sym.mkForallFVarsS #[premise] prop)
      else if info == .instImplicit && (← isClassType dom) then
        match ← Sym.synthInstance? dom with
        | .some value =>
          return ← go (mkApp proof value) (body.instantiate1 value) index
        | _ => return none
      else
        if isUnsupportedValueDomain dom || index >= values.size then return none
        let value := values[index]!
        unless ← isDefEqS (← Sym.inferType value) dom do return none
        go (mkApp proof value) (body.instantiate1 value) (index + 1)
    | _ =>
      if index != values.size || !(← isPropExpr ty) then return none
      return some (proof, ty)
  go proof ty 0

/-- Fallback used only when no query pattern can trigger a template yet.

Only one leading value binder is seeded this way. Multiple unconstrained binders
would create an `N^k` Cartesian product; those templates wait for pattern evidence
that determines their arguments together. -/
private partial def fallbackInstances (proof ty : Expr)
    (candidates : Array GroundCandidate) (budget : Nat) :
    Sym.SymM (Array (Expr × Expr)) := do
  let out ← IO.mkRef (#[] : Array (Expr × Expr))
  let rec go (proof ty : Expr) (applied : Nat) : Sym.SymM Unit := do
    if (← out.get).size >= budget then return
    match ty with
    | .forallE _ dom body info =>
      if ← isPropExpr dom then
        if applied > 0 then out.modify (·.push (proof, ty))
      else if info == .instImplicit && (← isClassType dom) then
        match ← Sym.synthInstance? dom with
        | .some value => go (mkApp proof value) (body.instantiate1 value) applied
        | _ => pure ()
      else if dom.isSort || dom.isForall then
        pure ()
      else if applied > 0 then
        pure ()
      else
        for candidate in candidates do
          if (← out.get).size >= budget then break
          if ← isDefEqS candidate.type dom then
            go (mkApp proof candidate.expr) (body.instantiate1 candidate.expr)
              (applied + 1)
    | _ =>
      if applied > 0 && (← isPropExpr ty) then out.modify (·.push (proof, ty))
  go proof ty 0
  out.get

/-- Add bounded ground consequences of marked quantified facts.

Pattern-derived instances run before fallback seeding in each round. A template
with any usable pattern evidence does not also take the Cartesian fallback, which
keeps the pass focused. Trigger occurrences carry their producing templates as
provenance, so a template cannot feed itself directly or through a cycle and grow
terms such as `x`, `next x`, `next (next x)`, ... until the budget is consumed. -/
private def instantiateGroundFactsS (cfg : Config) (facts : Array Fact) :
    Sym.SymM InstantiationReport := do
  if cfg.instFuel == 0 || cfg.instRounds == 0 then return { facts }
  let mut templates : Array Fact := #[]
  let mut templateSources : Array Nat := #[]
  let normalizedProps ← IO.mkRef ({} : Std.HashMap Expr Expr)
  for sourceIndex in [0:facts.size] do
    let fact := facts[sourceIndex]!
    if fact.instantiateTerms && fact.proof.isSome && !fact.negated then
      let prop ← preprocessExprS fact.prop
      normalizedProps.modify (·.insert fact.prop prop)
      if ← hasLeadingValueBinder prop then
        templates := templates.push { fact with prop }
        templateSources := templateSources.push sourceIndex
  if templates.isEmpty then return { facts }
  let simpContext ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let env ← getEnv
  let templateProps : Std.HashSet Expr :=
    templates.foldl (init := {}) fun seen template => seen.insert template.prop
  let generatedFacts ← IO.mkRef (#[] : Array Fact)
  let candidates ← IO.mkRef (#[] : Array GroundCandidate)
  let candidateSeen ← IO.mkRef ({} : Std.HashSet Expr)
  let occurrences ← IO.mkRef ({} : OccurrenceStore)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let generated ← IO.mkRef (0 : Nat)
  let exhausted ← IO.mkRef false
  for sourceIndex in [0:facts.size] do
    let fact := facts[sourceIndex]!
    let prop ←
      match (← normalizedProps.get).get? fact.prop with
      | some prop => pure prop
      | none =>
        let prop ← preprocessExprS fact.prop
        normalizedProps.modify (·.insert fact.prop prop)
        pure prop
    seen.modify fun known => (known.insert fact.prop).insert prop
    let ground ← collectGround prop
    unless templateProps.contains prop do
      for term in ground.terms do
        let seen ← candidateSeen.get
        unless seen.contains term.expr do
          candidateSeen.set (seen.insert term.expr)
          candidates.modify (·.push term)
    let mut factOrigins : Array Nat := #[]
    for templateIndex in [0:templateSources.size] do
      if templateSources[templateIndex]! == sourceIndex then
        factOrigins := factOrigins.push templateIndex
    for expr in ground.occurrences do
      occurrences.modify fun current => current.add expr factOrigins
  let addInstance (templateIndex : Nat) (template : Fact) (proof prop : Expr)
      (origins : Array Nat) : Sym.SymM Bool := do
    let prop ← preprocessExprS prop
    let (simpResult, _) ← simp prop simpContext
    let (proof, prop) ←
      match simpResult.proof? with
      | none => pure (proof, prop)
      | some _ =>
        let simplified ← preprocessExprS simpResult.expr
        let originalConstructors := collectGroundConstructors env prop
        let simplifiedConstructors := collectGroundConstructors env simplified
        if !simplified.isConstOf ``True &&
            originalConstructors.all simplifiedConstructors.contains then
          pure (← simpResult.mkEqMP proof, simplified)
        else
          pure (proof, prop)
    let known ← seen.get
    if known.contains prop then return false
    if (← generated.get) >= cfg.instFuel then
      exhausted.set true
      return false
    seen.set (known.insert prop)
    generated.modify (· + 1)
    trace[crush.inst] "generated {template.descr}@ground: {prop}"
    generatedFacts.modify (·.push {
      template with
      prop
      proof := some proof
      descr := s!"{template.descr}@ground"
      instantiateTerms := false
      instanceOf := template.proof })
    let origins := Pattern.mergeOrigins origins #[templateIndex]
    for expr in (← collectGround prop).occurrences do
      occurrences.modify fun current => current.add expr origins
    if (← generated.get) >= cfg.instFuel then exhausted.set true
    return true
  let mut reachedFixpoint := false
  for _round in [0:cfg.instRounds] do
    let before ← generated.get
    let roundOccurrences := (← occurrences.get).toArray
    let roundOccurrenceIndex := indexOccurrences roundOccurrences
    let roundCandidates ← candidates.get
    let mut hadPattern := Array.replicate templates.size false
    -- Prefer exact matches against facts already present at the start of the round.
    for i in [0:templates.size] do
      if ← exhausted.get then break
      let template := templates[i]!
      let some proof := template.proof | continue
      let remaining := cfg.instFuel - (← generated.get)
      let substitutions ←
        derivePatternSubstitutions template.prop roundOccurrences
          roundOccurrenceIndex i remaining
      unless substitutions.isEmpty do
        hadPattern := hadPattern.set! i true
      for substitution in substitutions do
        if ← exhausted.get then break
        if let some (instanceProof, instanceProp) ←
            instantiateAt proof template.prop substitution.values then
          discard <| addInstance i template instanceProof instanceProp
            substitution.origins
    -- Triggerless templates need query terms to create their first ground fact.
    for i in [0:templates.size] do
      if ← exhausted.get then break
      if hadPattern[i]! then continue
      let template := templates[i]!
      let some proof := template.proof | continue
      let remaining := cfg.instFuel - (← generated.get)
      for (instanceProof, instanceProp) in
          ← fallbackInstances proof template.prop roundCandidates remaining do
        if ← exhausted.get then break
        discard <| addInstance i template instanceProof instanceProp #[]
    if (← generated.get) == before then
      reachedFixpoint := true
      break
  if !reachedFixpoint && (← generated.get) > 0 then exhausted.set true
  let exhausted ← exhausted.get
  let generatedFacts ← generatedFacts.get
  let result := facts ++ generatedFacts
  let groundFacts ←
    if exhausted || generatedFacts.isEmpty then
      pure none
    else
      let templateSourceSet :=
        templateSources.foldl (init := ({} : Std.HashSet Nat)) (·.insert ·)
      let mut reduced : Array Fact := #[]
      for sourceIndex in [0:facts.size] do
        unless templateSourceSet.contains sourceIndex do
          reduced := reduced.push facts[sourceIndex]!
      pure (some (reduced ++ generatedFacts))
  return {
    facts := result
    groundFacts
    generated := ← generated.get
    exhausted }

/-- Run the complete pass in one symbolic-computation session. `SymM` caches
type inference and restricted definitional equality by shared-expression
identity, which are the dominant repeated operations in ground matching. -/
def instantiateGroundFacts (cfg : Config) (facts : Array Fact) :
    MetaM InstantiationReport :=
  Sym.SymM.run (instantiateGroundFactsS cfg facts)

end Crush
