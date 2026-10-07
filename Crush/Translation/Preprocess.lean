import Lean
import Lean.Meta.Injective
import Crush.Frontend.Collect
import Crush.Translation.Attr

open Lean Meta

/-!
# Proof-producing selected-definition normalization

Equation lemmas requested through `u[...]`, `d[...]`, or relevant
`@[crush_unfold]`/`@[crush_defeq]` attributes are useful in two different ways:

* quantified fallback facts let the SMT solver instantiate equations;
* direct rewriting exposes the exact applications already present in the query
  before monomorphization and translation.

The second path avoids depending on SMT quantifier instantiation for definitions
such as `List.Equiv`. This module builds a `simp only`-style context from the
selected equations and rewrites each non-equation fact. Rewritten hypotheses carry
kernel-checkable proofs produced by `simp`.

The negated goal has no proof until reconstruction introduces `hneg : ¬ goal`.
For it we retain a lambda `¬ goal → normalizedNegation`; Alethe replay applies that
lambda to `hneg` before associating the normalized assertion with its certificate
assumption.
-/

namespace Crush

/-- Result and diagnostics for selected-definition normalization. -/
structure NormalizeReport where
  facts     : Array Fact := #[]
  rewritten : Nat := 0
  deriving Inhabited

private partial def constructorEqLemmas (facts : Array Fact) : MetaM (Array Name) := do
  let env ← getEnv
  -- A general handler can intentionally reinterpret any subterm. Rewriting by
  -- Lean constructor semantics before translation would bypass that first-refusal
  -- contract (for example, a custom `Nat.succ` encoding).
  if hasTranslationHandlersInEnv env then return #[]
  let found ← IO.mkRef (#[] : Array Name)
  let seen ← IO.mkRef ({} : Std.HashSet Name)
  let addForEquality (lhs rhs : Expr) : MetaM Unit := do
    if lhs.hasLooseBVars || rhs.hasLooseBVars then return
    let hasTargetedLowering (e : Expr) : Bool :=
      match e.getAppFn with
      | .const name _ => hasLoweringsForInEnv env name
      | _ => false
    if hasTargetedLowering lhs || hasTargetedLowering rhs then return
    let some leftCtor ← isConstructorApp'? lhs | return
    let some rightCtor ← isConstructorApp'? rhs | return
    unless leftCtor.name == rightCtor.name do return
    if hasLoweringsForInEnv env leftCtor.name then return
    let lemma := mkInjectiveEqTheoremNameFor leftCtor.name
    unless env.contains lemma do return
    let known ← seen.get
    unless known.contains lemma do
      seen.set (known.insert lemma)
      found.modify (·.push lemma)
  let rec visit (e : Expr) : MetaM Unit := do
    match_expr e with
    | Eq _ lhs rhs => addForEquality lhs rhs
    | _ => pure ()
    match e with
    | .app f a => visit f; visit a
    | .lam _ ty body _ | .forallE _ ty body _ => visit ty; visit body
    | .letE _ ty value body _ => visit ty; visit value; visit body
    | .mdata _ body | .proj _ _ body => visit body
    | _ => pure ()
  for fact in facts do visit fact.prop
  found.get

/-- Selected-definition normalization is an optional optimization. Keep its search
bounded so a recursive equation cannot consume the enclosing tactic's entire budget. -/
private def normalizationMaxSteps : Nat := 1000
private def normalizationHeartbeatBudget : Nat := 2000000

private def tryNormalization {α : Type} (action : MetaM α) : MetaM (Option α) := do
  let saved ← saveState
  tryCatchRuntimeEx (do
    let now ← IO.getNumHeartbeats
    let ctx ← readThe Core.Context
    let remaining := ctx.maxHeartbeats - (now - ctx.initHeartbeats)
    let budget := if ctx.maxHeartbeats == 0 then normalizationHeartbeatBudget
      else min normalizationHeartbeatBudget (remaining / 2)
    if budget == 0 then
      throwError "crush: selected-definition normalization exhausted its local budget"
    withTheReader Core.Context
      ({ · with maxHeartbeats := budget, initHeartbeats := now }) do
        return some (← action)) fun _ => do
    saved.restore
    return none

private def selectedSimpContext (lemmas : Array Name) : MetaM Simp.Context := do
  let mut theorems : SimpTheorems := {}
  let mut seen : Std.HashSet Name := {}
  for lemma in lemmas do
    if seen.contains lemma then continue
    seen := seen.insert lemma
    theorems ← theorems.addConst lemma
  Simp.mkContext
    (config := { maxSteps := normalizationMaxSteps })
    (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)

private def negationTransformer (source : Expr) (result : Simp.Result) : MetaM Expr :=
  withLocalDeclD `h source fun h => do
    let normalized ← result.mkEqMP h
    mkLambdaFVars #[h] normalized

private def normalizeFact (ctx : Simp.Context) (fact : Fact) : MetaM (Option Fact) := do
  let source ← instantiateMVars fact.prop
  let (result, _) ← simp source ctx
  if result.expr == source && result.proof?.isNone then return none
  let proof ← fact.proof.mapM result.mkEqMP
  let negationTransform ←
    if fact.negated then some <$> negationTransformer source result
    else pure fact.negationTransform
  let reconstructionProof ←
    if fact.negated then some <$> result.getProof
    else pure fact.reconstructionProof
  return some {
    fact with
    prop := result.expr
    proof
    negationTransform
    reconstructionProof }

/-- Rewrite collected propositions using exactly the selected equation lemmas.

Equation facts themselves are retained verbatim as quantified fallback axioms.
Every other proof is transported across the simplifier's equality proof. Failed or
resource-limited normalization restores its state and retains the original facts;
this applies to context preparation as well as each individual simplification. -/
def normalizeFacts (facts : Array Fact) (lemmas : Array Name) :
    MetaM NormalizeReport := do
  let prepared ← tryNormalization do
    let constructorLemmas ← constructorEqLemmas facts
    let lemmas := lemmas ++ constructorLemmas
    if lemmas.isEmpty then return none
    return some (← selectedSimpContext lemmas)
  let some (some ctx) := prepared | return { facts }
  let mut out : Array Fact := #[]
  let mut rewritten := 0
  for fact in facts do
    if fact.isEquation then
      out := out.push fact
      continue
    let normalized ← tryNormalization (normalizeFact ctx fact)
    if let some (some normalized) := normalized then
      out := out.push normalized
      rewritten := rewritten + 1
    else
      out := out.push fact
  return { facts := out, rewritten }

end Crush
