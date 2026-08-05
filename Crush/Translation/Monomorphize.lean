import Lean
import Crush.Frontend.Config
import Crush.Reify.Collect
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
  let (_, out) ← go e |>.run #[]
  return out
where
  go (e : Expr) : StateRefT (Array Expr) MetaM Unit := do
    -- Record `e` itself when it is a type; then recurse into its structure. A type
    -- can contain another (`List Int` contains `Int`), so both happen.
    if ← isGroundType e then
      unless (← get).contains e do
        modify (·.push e)
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

/-- All specializations of the fact `(proof : ty)` obtained by instantiating its
leading type binders at `cands`, together with the instance binders that follow.

Peels the leading telescope: a `Sort`-typed binder is instantiated at every
type-correct candidate (branching), an instance-implicit binder is discharged by
synthesis, and the first ordinary value binder stops the walk. Returns
`(proof, type)` pairs; `budget` bounds the number produced so a wide cross product
cannot run away. -/
private partial def specializations (proof ty : Expr) (cands : Array Expr)
    (budget : Nat) : MetaM (Array (Expr × Expr)) := do
  if budget == 0 then return #[]
  match ty with
  | .forallE _ dom body bi => do
    let domW ← whnf dom
    if domW.isSort then
      -- A type binder: branch over every candidate that fits this universe.
      let mut out : Array (Expr × Expr) := #[]
      for c in cands do
        if out.size >= budget then break
        -- The candidate must actually inhabit this binder's sort (`Type` vs `Prop`
        -- vs `Type 1`), else the application is ill-typed.
        unless ← isDefEq (← inferType c) domW do continue
        let proof' := mkApp proof c
        let ty' := body.instantiate1 c
        if ← hasInstantiableBinder ty' then
          -- More type binders to go: recurse, splitting the remaining budget.
          out := out ++ (← specializations proof' ty' cands (budget - out.size))
        else
          -- Discharge any instance binders now exposed, then take this instance.
          if let some inst ← dischargeInstances proof' ty' then
            out := out.push inst
      return out
    else if bi == .instImplicit then
      -- Not reachable from the top (a fact starts with its type binders), but keeps
      -- the walk total if a lemma leads with an instance argument.
      match ← trySynthInstance domW with
      | .some val => specializations (mkApp proof val) (body.instantiate1 val) cands budget
      | _ => return #[]
    else
      return #[]
  | _ => return #[]
where
  /-- Fill instance-implicit binders left after the type arguments are fixed, e.g.
  the `[DecidableEq α]` of a lemma once `α := Int`. A failure to synthesize means
  this instantiation is not usable, which is a dropped instance, not an error. -/
  dischargeInstances (proof ty : Expr) : MetaM (Option (Expr × Expr)) := do
    match ty with
    | .forallE _ dom body .instImplicit =>
      match ← trySynthInstance (← whnf dom) with
      | .some val => dischargeInstances (mkApp proof val) (body.instantiate1 val)
      | _ => return none
    | _ => return some (proof, ty)

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
  -- Seed candidates from the monomorphic facts (above all the negated goal): those
  -- are the types the query is actually about.
  let mut cands : Array Expr := #[]
  for f in fixed do
    for c in ← collectCandidates (← instantiateMVars f.prop) do
      unless cands.contains c do cands := cands.push c
  let mut out := fixed
  let mut seen : Std.HashSet Expr := {}
  let mut generated := 0
  let mut instantiated : Std.HashSet String := {}
  let mut rejected : Array String := #[]
  let mut exhausted := false
  for _round in [0:cfg.monoRounds] do
    let mut newThisRound := 0
    for f in poly do
      if generated >= cfg.monoFuel then
        exhausted := true
        break
      let some proof := f.proof | continue
      let ty ← instantiateMVars f.prop
      let insts ← specializations proof ty cands (cfg.monoFuel - generated)
      for (p, t) in insts do
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
            try isDefEq (← inferType p) t
            catch _ => pure false
          unless ok do
            rejected := rejected.push s!"{f.descr}@inst"
            continue
        generated := generated + 1
        newThisRound := newThisRound + 1
        instantiated := instantiated.insert f.descr
        out := out.push { f with prop := t, proof := some p, descr := s!"{f.descr}@inst" }
        -- Saturation: the new instance may mention types nothing else did.
        for c in ← collectCandidates t do
          unless cands.contains c do cands := cands.push c
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
  for f in poly do
    unless instantiated.contains f.descr do
      out := out.push f
      dropped := dropped.push f.descr
  return { facts := out, generated, dropped, rejected, exhausted }

end Crush
