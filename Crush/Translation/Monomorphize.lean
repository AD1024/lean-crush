import Lean
import Crush.Frontend.Config
import Crush.Reify.Collect
import Crush.Translation.Monad
open Lean Meta

/-!
# Lemma-instantiation monomorphization

Datatype monomorphization (in `Crush/Translation/Translate.lean`) turns a
fully-applied parametric *type* into a real SMT datatype. This module handles the
other half: a *polymorphic fact* is specialized to the concrete types the query
actually mentions.

## Why this is needed

The translation keys each SMT symbol on a constant *together with its type
arguments*, so `@app Int` and `@app α` are different symbols with different sorts —
they have to be, since their SMT sorts genuinely differ. That means a polymorphic
fact is, before this pass, **disconnected from the goal it is meant to support**.
For a polymorphic `app`, the equation lemma and a goal about `app` at `Int` emit as:

```smtlib
; the equation lemma, at an abstract instantiation
(assert (forall ((q_1 s_0)) (= (app2_6 List_2_nil q_5) q_5)))
; the goal, at Int
(assert (not (= (app2_19 List_20_nil y_24) y_24)))
```

Two unrelated function symbols over two unrelated datatypes, so the lemma cannot
possibly discharge the goal. Worth stressing that this bites **even when the goal is
ground**: it is the *fact* being polymorphic that breaks the connection, not the
goal. That is why a hand-written monomorphic `append : List Int → List Int → List Int`
worked where the polymorphic one did not.

This pass rewrites `∀ (α : Type), P α` into `P Int`, `P Bool`, … for the types the
query mentions, so the resulting facts talk about the *same* symbols as the goal.

## Soundness direction

Instantiation only ever *weakens* the asserted set: `P Int` is a consequence of
`∀ α, P α`, and a polymorphic fact that gets instantiated is dropped in favour of its
instances. Asserting weaker facts can make `unsat` *harder* to reach, never easier,
so this pass cannot cause a false `unsat` — it can only cost completeness. That is
the safe direction to err in, and it is why exhausting the fuel budget is a
completeness matter (reported as a diagnostic) rather than a soundness one.

## Bounds and reporting

`crush.mono.fuel` caps the total number of generated instances and
`crush.mono.rounds` caps the saturation rounds; either at `0` disables the pass.
On exhaustion the caller is told what was dropped rather than being handed a
silently truncated set.

## Known boundary

Only the *leading* binder telescope is instantiated: in `∀ α, P α → ∀ β, Q β` the
`β` is not reached, because instantiating it would mean going under the `P α`
binder and re-abstracting. Every equation lemma and essentially every real
polymorphic lemma has its type binders up front, so this covers the payload case;
the nested position is a documented gap rather than a silent one.
-/

namespace Crush

/-- A candidate type to instantiate a lemma's leading type binder at: a subterm that
is a genuine first-order SMT *data sort*.

"Ground" means free of metavariables and loose bound variables; a local *free*
variable is allowed (`List α` over an fvar `α` is already a real SMT datatype over an
opaque element sort, so admitting fvars is what lets a polymorphic lemma be proved).

Excluded, because instantiating a `{α : Type}` binder at them yields malformed SMT and
only ever shrinks the instance set (a completeness cost, never soundness):
* **`Prop`/`Sort` itself** — a proposition maps to `Bool`, not a sort. A universe-
  polymorphic lemma binds `{γ : Sort u}` and `Sort u` unifies with `Sort 0`, so
  without the `Sort (n+1)` check below a predicate application `P x : Prop` in the
  goal would be collected and, say, `Function.comp_def`'s `{γ}` instantiated at it —
  emitting `(... False)` where a sort belongs and cross-producting into a blow-up.
* **Function types** — the higher-order case defunctionalization handles at *use*, not
  by monomorphizing a type binder at an arrow. -/
private def isGroundType (e : Expr) : MetaM Bool := do
  if e.hasExprMVar || e.hasLooseBVars then return false
  let ew ← whnf e
  if ew.isSort || ew.isArrow then return false
  -- A data type lives in `Type _`, i.e. its own type is `Sort (n+1)`; reject `Sort 0`.
  match ← whnf (← inferType e) with
  | .sort l => return !l.isZero
  | _ => return false

/-- Collect instantiation candidates from `e`: every ground subterm that is a type.

Traverses the whole expression rather than only application arguments, so a type
mentioned solely in a binder (`∀ xs : List Int, …`) is still found. Deduplicated by
the `Expr` itself; `isDefEq`-level canonicalization happens later, at use. -/
private partial def collectCandidates (e : Expr) : MetaM (Array Expr) := do
  let (_, out) ← go e |>.run (#[], {})
  return out.1
where
  go (e : Expr) : StateRefT (Array Expr × Std.HashSet Expr) MetaM Unit := do
    -- Record `e` itself when it is a type; then recurse into its structure. A type
    -- can contain another (`List Int` contains `Int`), so both happen. Membership is
    -- hashed: the traversal covers whole expressions, where a linear scan is quadratic.
    if ← isGroundType e then
      unless (← get).2.contains e do
        modify fun (out, seen) => (out.push e, seen.insert e)
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => return

/-- Does `ty` have a leading binder we could instantiate at a type? -/
private def hasInstantiableBinder (ty : Expr) : MetaM Bool := do
  let .forallE _ dom _ _ := ty | return false
  return (← whnf dom).isSort

private structure AppPattern where
  head     : Expr
  argIndex : Nat
  pattern  : Expr

private structure TypeOccurrence where
  expr    : Expr
  origins : Array Nat := #[]
  deriving Inhabited

private structure AppOccurrence where
  head    : Expr
  args    : Array Expr
  origins : Array Nat := #[]
  deriving Inhabited

private structure PartialSubstitution where
  values  : Array (Option Expr)
  origins : Array Nat := #[]
  deriving Inhabited

private structure DerivedSubstitution where
  values  : Array Expr
  origins : Array Nat := #[]
  deriving Inhabited

/-- Whether `e` contains one of the opened leading type-binder fvars. -/
private partial def containsBinder (e : Expr) (binders : Array Expr) : Bool :=
  match e with
  | .fvar id => binders.any fun binder => binder.fvarId! == id
  | .app f a => containsBinder f binders || containsBinder a binders
  | .lam _ ty body _ | .forallE _ ty body _ =>
    containsBinder ty binders || containsBinder body binders
  | .letE _ ty value body _ =>
    containsBinder ty binders || containsBinder value binders
      || containsBinder body binders
  | .mdata _ body | .proj _ _ body => containsBinder body binders
  | _ => false

private def sameHead (a b : Expr) : Bool :=
  match a, b with
  | .const an _, .const bn _ => an == bn
  | .fvar aid, .fvar bid => aid == bid
  | _, _ => false

/-- Collect informative type patterns and explicit type arguments of applications.

For `Except ε α`, the whole constructor application is retained and its children
are not added as independent candidates. For `f α x`, the explicit type argument
is also indexed by `(f, argument-position)`, allowing a query occurrence `f Int a`
to derive `α := Int` directly. Bare binder patterns are retained only as a fallback
when no structured/application match constrains that binder. -/
private partial def collectPatterns (e : Expr) (binders : Array Expr) :
    MetaM (Array Expr × Array AppPattern) := do
  let typePatterns ← IO.mkRef (#[] : Array Expr)
  let appPatterns ← IO.mkRef (#[] : Array AppPattern)
  let rec go (e : Expr) (typePosition : Bool := false) : MetaM Unit := do
    -- Binder domains and declared result types are known type positions. Avoid
    -- asking `inferType`/`whnf` about arbitrary open terms: Lean treats a loose
    -- value bvar there as a panic rather than a recoverable error.
    if typePosition && !e.hasLooseBVars && containsBinder e binders && !e.isForall then
      let patterns ← typePatterns.get
      unless patterns.contains e do typePatterns.set (patterns.push e)
      return
    let fn := e.getAppFn
    let args := e.getAppArgs
    unless args.isEmpty do
      if fn.isConst || fn.isFVar then
        for i in [0:args.size] do
          let arg := args[i]!
          -- Explicit type arguments contain the opened type fvars syntactically.
          -- Ordinary value arguments do not; `matchPattern` additionally requires
          -- any binder target to be a ground type before accepting the evidence.
          if !arg.hasLooseBVars && containsBinder arg binders then
            let patterns ← appPatterns.get
            unless patterns.any (fun p =>
                sameHead p.head fn && p.argIndex == i && p.pattern == arg) do
              appPatterns.set (patterns.push { head := fn, argIndex := i, pattern := arg })
    match e with
    | .app f a => go f; go a
    | .lam _ ty body _ | .forallE _ ty body _ => go ty true; go body
    | .letE _ ty value body _ => go ty true; go value; go body
    | .mdata _ body | .proj _ _ body => go body typePosition
    | _ => pure ()
  go e
  return (← typePatterns.get, ← appPatterns.get)

/-- Collect first-order application spines from a query proposition. -/
private partial def collectApplications (e : Expr) : Array AppOccurrence :=
  Id.run do
    let mut out : Array AppOccurrence := #[]
    let rec go (e : Expr) : StateM (Array AppOccurrence) Unit := do
      let fn := e.getAppFn
      let args := e.getAppArgs
      unless args.isEmpty do
        if fn.isConst || fn.isFVar then
          unless (← get).any (fun occurrence =>
              sameHead occurrence.head fn && occurrence.args == args) do
            modify (·.push { head := fn, args })
      match e with
      | .app f a => go f; go a
      | .lam _ ty body _ | .forallE _ ty body _ => go ty; go body
      | .letE _ ty value body _ => go ty; go value; go body
      | .mdata _ body | .proj _ _ body => go body
      | _ => pure ()
    let (_, result) := (go e).run out
    return result

/-- Index of an opened type-binder fvar. -/
private def binderIndex? (binders : Array Expr) (id : FVarId) : Option Nat := Id.run do
  for i in [0:binders.size] do
    if binders[i]!.fvarId! == id then return some i
  return none

/-- Match a type/application pattern against a query expression, deriving a partial
substitution for the opened leading type binders. Fixed pieces must be definitionally
equal; repeated binder occurrences must receive definitionally equal targets. -/
private partial def matchPattern (pattern target : Expr) (binders : Array Expr)
    (initial : Array (Option Expr)) : MetaM (Option (Array (Option Expr))) := do
  let rec go (pattern target : Expr) (subst : Array (Option Expr)) :
      MetaM (Option (Array (Option Expr))) := do
    if pattern.hasLooseBVars || target.hasLooseBVars then return none
    if let .fvar id := pattern then
      if let some index := binderIndex? binders id then
        unless ← isGroundType target do return none
        unless ← isDefEqReadOnly (← inferType target) (← id.getType) do return none
        match subst[index]! with
        | none => return some (subst.set! index (some target))
        | some previous =>
          return if ← isDefEqReadOnly previous target then some subst else none
    unless containsBinder pattern binders do
      return if ← isDefEqReadOnly pattern target then some subst else none
    match pattern, target with
    | .app pf pa, .app tf ta =>
      let some subst ← go pf tf subst | return none
      go pa ta subst
    | .mdata _ body, _ => go body target subst
    | _, .mdata _ body => go pattern body subst
    | _, _ => return none
  go pattern target initial

private def isBareBinderPattern (pattern : Expr) (binders : Array Expr) : Option Nat :=
  match pattern with
  | .fvar id => binderIndex? binders id
  | _ => none

private def originsSubset (left right : Array Nat) : Bool :=
  left.all right.contains

/-- A merge is useful only if both substitutions provide a binder absent from the other.
Otherwise the merged values equal one input while its provenance is less permissive, so
that input already dominates the result. -/
private def substitutionsComplementary (left right : Array (Option Expr)) : Bool :=
  let leftAdds := (Array.zip left right).any fun
    | (some _, none) => true
    | _ => false
  let rightAdds := (Array.zip left right).any fun
    | (none, some _) => true
    | _ => false
  leftAdds && rightAdds

private def mergeOrigins (left right : Array Nat) : Array Nat := Id.run do
  let mut out := left
  for origin in right do
    unless out.contains origin do out := out.push origin
  return out

/-- Merge compatible partial substitutions. -/
private def mergeSubstitutions (a b : Array (Option Expr)) :
    MetaM (Option (Array (Option Expr))) := do
  if a.size != b.size then return none
  let mut merged := a
  for i in [0:a.size] do
    match a[i]!, b[i]! with
    | none, some value => merged := merged.set! i (some value)
    | some left, some right =>
      unless ← isDefEqReadOnly left right do return none
    | _, _ => pure ()
  return some merged

/-- Derive relevant leading-type substitutions for `ty` from query type shapes and
applications.

Structured matches have priority. A bare `α` fallback is used only when no
structured type or same-head application occurrence constrained `α`; this preserves
cross-fact saturation (`Int` can seed a fact that introduces `List Int`) without
letting `Except ε α` independently cross-product every generated type into both
binders. -/
private partial def deriveSubstitutions (ty : Expr) (queryTypes : Array TypeOccurrence)
    (queryApps : Array AppOccurrence) (budget : Nat) :
    MetaM (Array DerivedSubstitution) := do
  if budget == 0 then return #[]
  let derive (openedTy : Expr) (binders : Array Expr) :
      MetaM (Array DerivedSubstitution) := do
    if binders.isEmpty then return #[]
    let empty := Array.replicate binders.size none
    let (typePatterns, appPatterns) ← collectPatterns openedTy binders
    let mut evidence : Array PartialSubstitution := #[]
    let evidenceLimit := max budget (binders.size * budget)
    let addEvidence (evidence : Array PartialSubstitution)
        (values : Array (Option Expr)) (origins : Array Nat) :
        Array PartialSubstitution := Id.run do
      unless evidence.size < evidenceLimit && values.any Option.isSome do
        return evidence
      for i in [0:evidence.size] do
        let existing := evidence[i]!
        if existing.values == values then
          -- Keep the least restrictive provenance. Fixed-query evidence has no
          -- origins and therefore dominates every generated route to the same
          -- substitution.
          if originsSubset existing.origins origins then return evidence
          if originsSubset origins existing.origins then
            return evidence.set! i { values, origins }
      return evidence.push { values, origins }
    -- Same-head explicit type arguments are the strongest relevance signal.
    for pattern in appPatterns do
      for occurrence in queryApps do
        if sameHead pattern.head occurrence.head then
          if let some target := occurrence.args[pattern.argIndex]? then
            if let some subst ← matchPattern pattern.pattern target binders empty then
              evidence := addEvidence evidence subst occurrence.origins
    -- Match structured data shapes such as `Except ε α` and `List α`.
    for pattern in typePatterns do
      if (isBareBinderPattern pattern binders).isSome then continue
      for target in queryTypes do
        if let some subst ← matchPattern pattern target.expr binders empty then
          evidence := addEvidence evidence subst target.origins
    -- Fall back to all query types only for a binder not constrained above.
    let mut covered := Array.replicate binders.size false
    for candidate in evidence do
      for i in [0:binders.size] do
        if candidate.values[i]!.isSome then covered := covered.set! i true
    for pattern in typePatterns do
      let some index := isBareBinderPattern pattern binders | continue
      if covered[index]! then continue
      for target in queryTypes do
        if let some subst ← matchPattern pattern target.expr binders empty then
          evidence := addEvidence evidence subst target.origins
    -- Close compatible partial substitutions under merge. At most `n` merge
    -- rounds are needed to fill `n` binders.
    for _ in [0:binders.size] do
      let before := evidence.size
      let snapshot := evidence
      for i in [0:snapshot.size] do
        for j in [0:i] do
          if evidence.size >= evidenceLimit then break
          let left := snapshot[i]!
          let right := snapshot[j]!
          unless substitutionsComplementary left.values right.values do continue
          if let some merged ← mergeSubstitutions left.values right.values then
            evidence := addEvidence evidence merged
              (mergeOrigins left.origins right.origins)
      if evidence.size == before then break
    let mut out : Array DerivedSubstitution := #[]
    for candidate in evidence do
      if out.size >= budget then break
      let mut full : Array Expr := #[]
      let mut complete := true
      for value in candidate.values do
        match value with
        | some value => full := full.push value
        | none => complete := false
      if complete then
        let mut retained := false
        for i in [0:out.size] do
          let existing := out[i]!
          if existing.values == full then
            retained := true
            if originsSubset candidate.origins existing.origins then
              out := out.set! i { values := full, origins := candidate.origins }
            break
        unless retained do
          out := out.push { values := full, origins := candidate.origins }
    return out
  let rec openBinders (ty : Expr) (binders : Array Expr) :
      MetaM (Array DerivedSubstitution) := do
    match ty with
    | .forallE name dom body _ =>
      let domW ← whnf dom
      if domW.isSort then
        withLocalDeclD name dom fun binder =>
          openBinders (body.instantiate1 binder) (binders.push binder)
      else
        derive ty binders
    | _ => derive ty binders
  openBinders ty #[]

/-- Instantiate all leading type binders according to one query-derived
substitution, then synthesize the instance-implicit binders that follow. -/
private partial def specializationAtCore (proof ty : Expr) (subst : Array Expr) :
    MetaM (Option (Expr × Expr)) := do
  let mut proof := proof
  let mut ty := ty
  for candidate in subst do
    let .forallE _ dom body _ := ty | return none
    let domW ← whnf dom
    unless domW.isSort do return none
    unless ← Meta.isDefEqGuarded (← inferType candidate) domW do return none
    proof := mkApp proof candidate
    ty := body.instantiate1 candidate
  dischargeInstances proof ty
where
  /-- Fill instance-implicit binders left after the type arguments are fixed, e.g.
  the `[DecidableEq α]` of a lemma once `α := Int`. -/
  dischargeInstances (proof ty : Expr) : MetaM (Option (Expr × Expr)) := do
    match ty with
    | .forallE _ dom body .instImplicit =>
      match ← trySynthInstance (← whnf dom) with
      | .some value => dischargeInstances (mkApp proof value) (body.instantiate1 value)
      | _ => return none
    | _ => return some (proof, ty)

/-- Specialize transactionally and freeze the resulting expressions before rollback. -/
private def specializationAt (proof ty : Expr) (subst : Array Expr) :
    MetaM (Option (Expr × Expr)) := do
  let saved ← Meta.saveState
  try
    match ← specializationAtCore proof ty subst with
    | none => return none
    | some (specializedProof, specializedType) =>
      let specializedProof ← instantiateMVars specializedProof
      let specializedType ← instantiateMVars specializedType
      if specializedProof.hasMVar || specializedType.hasMVar then
        return none
      return some (specializedProof, specializedType)
  finally
    saved.restore

/-- The result of the pass: the rewritten fact set, plus what it had to give up. -/
structure MonoReport where
  /-- Facts to send to the solver, with polymorphic ones replaced by instances. -/
  facts : Array Fact := #[]
  /-- Number of instances generated. -/
  generated : Nat := 0
  /-- Descriptions of polymorphic facts left un-instantiated (no candidate fit, or
  the budget ran out). Reported so a truncation is never silent. -/
  dropped : Array String := #[]
  /-- Descriptions of candidate instances that failed **certification** — the proof
  term did not actually have the proposition we attached to it (`inferType p` not
  defeq `t`). This should never fire: it indicates a bug in `specializations`, not a
  user error. Surfaced so such a bug is loud rather than silently translated. -/
  rejected : Array String := #[]
  /-- Whether a bound (fuel or rounds) was hit, as opposed to reaching a fixpoint. -/
  exhausted : Bool := false

/-- Specialize the polymorphic facts in `facts` at the types the query mentions.

Saturates: an instance can mention a type no earlier fact did (instantiating a
lemma about `List α` at `α := Int` introduces `List Int`), which may in turn let
another polymorphic fact instantiate. Repeats until no new instance appears, or
until `cfg.monoRounds` / `cfg.monoFuel` runs out.

The negated goal and every already-monomorphic fact pass through untouched. A
polymorphic fact that yields at least one instance is **replaced** by its instances
(keeping it would only re-introduce the disconnected abstract symbols this pass
exists to remove); one that yields none is kept as-is and named in `dropped`. -/
def monomorphizeFacts (cfg : Config) (facts : Array Fact) : MetaM MonoReport := do
  if cfg.monoFuel == 0 || cfg.monoRounds == 0 then
    return { facts }
  -- Split the fact set: polymorphic facts are the ones to specialize. The negated
  -- goal is never instantiated — it is the thing being refuted.
  let mut fixed : Array Fact := #[]
  let mut poly : Array Fact := #[]
  for f in facts do
    if !f.negated && f.proof.isSome && (← hasInstantiableBinder (← instantiateMVars f.prop)) then
      poly := poly.push f
    else
      fixed := fixed.push f
  if poly.isEmpty then
    return { facts }
  -- Seed type shapes and same-head application occurrences from the fixed query
  -- (above all the negated goal). Generated instances may extend these indices,
  -- but only pattern matches against them can produce another substitution.
  let mut queryTypes : Array TypeOccurrence := #[]
  let mut queryApps : Array AppOccurrence := #[]
  for f in fixed do
    for c in ← collectCandidates (← instantiateMVars f.prop) do
      unless queryTypes.any (fun occurrence =>
          occurrence.expr == c && occurrence.origins.isEmpty) do
        queryTypes := queryTypes.push { expr := c }
    for occurrence in collectApplications (← instantiateMVars f.prop) do
      unless queryApps.any (fun existing =>
          sameHead existing.head occurrence.head && existing.args == occurrence.args
            && existing.origins.isEmpty) do
        queryApps := queryApps.push occurrence
  let mut out := fixed
  let mut seen : Std.HashSet Expr := {}
  let mut generated := 0
  let mut instantiated := Array.replicate poly.size false
  let mut rejected : Array String := #[]
  let mut exhausted := false
  for _round in [0:cfg.monoRounds] do
    let mut newThisRound := 0
    for factIndex in [0:poly.size] do
      let f := poly[factIndex]!
      if generated >= cfg.monoFuel then
        exhausted := true
        break
      let some proof := f.proof | continue
      let ty ← instantiateMVars f.prop
      -- A generated shape may activate another fact, but never a fact already in
      -- its provenance. This preserves useful cross-fact saturation while ruling
      -- out self- and mutual-recursive type growth such as
      -- `List Int`, `List (List Int)`, ...
      let eligibleTypes := queryTypes.filter fun occurrence =>
        !occurrence.origins.contains factIndex
      let eligibleApps := queryApps.filter fun occurrence =>
        !occurrence.origins.contains factIndex
      let substitutions ← deriveSubstitutions ty eligibleTypes eligibleApps
        (cfg.monoFuel - generated)
      for substitution in substitutions do
        let some (p, t) ← specializationAt proof ty substitution.values | continue
        let t ← instantiateMVars t
        if seen.contains t then continue
        seen := seen.insert t
        -- **Optionally certify the instance before trusting it** (`crush.mono.certify`,
        -- off by default). `p` is `proof` applied to the chosen type/instance arguments
        -- and `t` is the corresponding instantiated proposition, so `p : t` holds by
        -- construction — but only if `specializations` built the two in lock-step.
        -- Nothing downstream re-checks this cheaply: `buildScript` translates `t` and
        -- never looks at `p` (the proof is consumed only during reconstruction). So
        -- under `trust`/`reconstructOrTrust` a defect here would translate a proposition
        -- with no valid Lean witness — an unsoundness the solver could not catch.
        -- Verifying `inferType p` is defeq `t` makes "every asserted instance is
        -- entailed by its stated proof" checked rather than argued. It is off by default
        -- because the default `reconstruct` policy already re-checks each proof through
        -- the kernel during replay, making the `isDefEq` redundant there; it earns its
        -- cost only under the trusting policies. A mismatch is a bug in this pass, so
        -- the instance is dropped and named loudly, never emitted.
        if cfg.monoCertify then
          let ok ←
            try isDefEqReadOnly (← inferType p) t
            catch _ => pure false
          unless ok do
            rejected := rejected.push s!"{f.descr}@inst"
            continue
        generated := generated + 1
        newThisRound := newThisRound + 1
        instantiated := instantiated.set! factIndex true
        out := out.push { f with prop := t, proof := some p, descr := s!"{f.descr}@inst" }
        let origins := mergeOrigins substitution.origins #[factIndex]
        -- Pattern-directed saturation: the new instance may expose a type shape or
        -- same-head application another fact requires. Its provenance prevents a
        -- dependency cycle from feeding the shape back into any producer.
        for c in ← collectCandidates t do
          unless queryTypes.any (fun occurrence =>
              occurrence.expr == c && occurrence.origins == origins) do
            queryTypes := queryTypes.push { expr := c, origins }
        for occurrence in collectApplications t do
          unless queryApps.any (fun existing =>
              sameHead existing.head occurrence.head && existing.args == occurrence.args
                && existing.origins == origins) do
            queryApps := queryApps.push { occurrence with origins }
      if generated >= cfg.monoFuel then
        exhausted := true
        break
    -- Fixpoint: a round that adds nothing will never add anything later either,
    -- since candidates only grow when an instance is added.
    if newThisRound == 0 then break
  if generated >= cfg.monoFuel then exhausted := true
  -- A polymorphic fact that produced no instance is kept verbatim: it is useless to
  -- the solver but harmless, and dropping it silently would hide the gap.
  let mut dropped : Array String := #[]
  for i in [0:poly.size] do
    let f := poly[i]!
    unless instantiated[i]! do
      out := out.push f
      dropped := dropped.push f.descr
  return { facts := out, generated, dropped, rejected, exhausted }

end Crush
