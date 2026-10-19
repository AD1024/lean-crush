import Lean
import Crush.Frontend.Config
import Crush.Frontend.Collect
import Crush.Translation.Monad
import Crush.Translation.Pattern

/-!
# Lemma-instantiation monomorphization

Specialize leading type and instance binders at query-relevant instantiations so
facts and goals refer to the same structurally keyed SMT symbols. Generated facts
apply their original proofs; replacing a universal fact by these consequences may
lose completeness but cannot strengthen the query.
Fuel and round limits bound saturation, and provenance prevents recursive type growth.
Report exhaustion and certification failures. Binders beneath intervening hypotheses
are outside this pass; unused polymorphic facts remain available to later translation.
-/

open Lean Meta

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
    -- Record types and their nested components; hashed membership avoids
    -- quadratic scans during whole-expression traversal.
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
private partial def collectTypePatterns (e : Expr) (binders : Array Expr) :
    MetaM (Array Expr × Array AppPattern) := do
  let typePatterns ← IO.mkRef (#[] : Array Expr)
  let appPatterns ← IO.mkRef (#[] : Array AppPattern)
  let rec go (e : Expr) (typePosition : Bool := false) : MetaM Unit := do
    -- Inspect known type positions only; inferType on a loose value bvar can panic.
    if typePosition && !e.hasLooseBVars && Pattern.containsBinder e binders && !e.isForall then
      let patterns ← typePatterns.get
      unless patterns.contains e do typePatterns.set (patterns.push e)
      return
    let fn := e.getAppFn
    let args := e.getAppArgs
    unless args.isEmpty do
      if fn.isConst || fn.isFVar then
        for i in [0:args.size] do
          let arg := args[i]!
          -- Type arguments contain opened type variables; matchPattern accepts
          -- binder evidence only when the target is itself a ground type.
          if !arg.hasLooseBVars && Pattern.containsBinder arg binders then
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

private def isBareBinderPattern (pattern : Expr) (binders : Array Expr) : Option Nat :=
  match pattern with
  | .fvar id => Pattern.binderIndex? binders id
  | _ => none

/-- Derive relevant leading-type substitutions for `ty` from query type shapes and
applications.

Structured matches have priority. A bare `α` fallback is used only when no
structured type or same-head application occurrence constrained `α`; this preserves
cross-fact saturation (`Int` can seed a fact that introduces `List Int`) without
letting `Except ε α` independently cross-product every generated type into both
binders. -/
private partial def deriveSubstitutions (ty : Expr) (queryTypes : Array TypeOccurrence)
    (queryApps : Array AppOccurrence) (budget : Nat) :
    MetaM (Array Pattern.Substitution) := do
  if budget == 0 then return #[]
  let derive (openedTy : Expr) (binders : Array Expr) :
      MetaM (Array Pattern.Substitution) := do
    if binders.isEmpty then return #[]
    let empty := Array.replicate binders.size none
    let (typePatterns, appPatterns) ← collectTypePatterns openedTy binders
    let mut evidence : Array Pattern.PartialSubstitution := #[]
    let evidenceLimit := max budget (binders.size * budget)
    -- Same-head explicit type arguments are the strongest relevance signal.
    for pattern in appPatterns do
      for occurrence in queryApps do
        if sameHead pattern.head occurrence.head then
          if let some target := occurrence.args[pattern.argIndex]? then
            if let some subst ← Pattern.matchPattern isGroundType inferType
                (fun binder => binder.fvarId!.getType) isDefEqReadOnly pattern.pattern target
                binders empty then
              evidence := Pattern.addEvidence evidence subst occurrence.origins evidenceLimit
    -- Match structured data shapes such as `Except ε α` and `List α`.
    for pattern in typePatterns do
      if (isBareBinderPattern pattern binders).isSome then continue
      for target in queryTypes do
        if let some subst ← Pattern.matchPattern isGroundType inferType
            (fun binder => binder.fvarId!.getType) isDefEqReadOnly pattern target.expr
            binders empty then
          evidence := Pattern.addEvidence evidence subst target.origins evidenceLimit
    -- Fall back to all query types only for a binder not constrained above.
    let mut covered := Array.replicate binders.size false
    for candidate in evidence do
      for i in [0:binders.size] do
        if candidate.values[i]!.isSome then covered := covered.set! i true
    for pattern in typePatterns do
      let some index := isBareBinderPattern pattern binders | continue
      if covered[index]! then continue
      for target in queryTypes do
        if let some subst ← Pattern.matchPattern isGroundType inferType
            (fun binder => binder.fvarId!.getType) isDefEqReadOnly pattern target.expr
            binders empty then
          evidence := Pattern.addEvidence evidence subst target.origins evidenceLimit
    evidence ← Pattern.closeEvidence isDefEqReadOnly evidence evidenceLimit binders.size
    return Pattern.completeEvidence evidence budget
  let rec openBinders (ty : Expr) (binders : Array Expr) :
      MetaM (Array Pattern.Substitution) := do
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
  -- Specialize polymorphic premises, never the negated goal being refuted.
  let mut fixed : Array Fact := #[]
  let mut poly : Array Fact := #[]
  for f in facts do
    if !f.negated && f.proof.isSome && (← hasInstantiableBinder (← instantiateMVars f.prop)) then
      poly := poly.push f
    else
      fixed := fixed.push f
  if poly.isEmpty then
    return { facts }
  -- Seed from the fixed query. Generated shapes can extend the indices,
  -- but new substitutions still require pattern evidence.
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
      -- Provenance forbids feeding generated shapes back into their producers,
      -- preventing self- and mutual-recursive type growth.
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
        -- Optional early certification localizes proof/proposition mismatches to
        -- specialization. Report and omit a failed instance; trusted discharge and
        -- reconstruction still perform their own proof checks.
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
        let origins := Pattern.mergeOrigins substitution.origins #[factIndex]
        -- Expose new patterns to other facts while provenance prevents dependency cycles.
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
    -- No new instance means no new candidates for a later round.
    if newThisRound == 0 then break
  if generated >= cfg.monoFuel then exhausted := true
  -- Retain uninstantiated facts for later translation instead of silently dropping them.
  let mut dropped : Array String := #[]
  for i in [0:poly.size] do
    let f := poly[i]!
    unless instantiated[i]! do
      out := out.push f
      dropped := dropped.push f.descr
  return { facts := out, generated, dropped, rejected, exhausted }

end Crush
