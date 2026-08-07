import Lean
import Crush.Reify.Collect

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

private def selectedSimpContext (lemmas : Array Name) : MetaM Simp.Context := do
  let mut theorems : SimpTheorems := {}
  let mut seen : Std.HashSet Name := {}
  for lemma in lemmas do
    if seen.contains lemma then continue
    seen := seen.insert lemma
    theorems ← theorems.addConst lemma
  Simp.mkContext
    (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)

private def negationTransformer (source : Expr) (result : Simp.Result) : MetaM Expr :=
  withLocalDeclD `h source fun h => do
    let normalized ← result.mkEqMP h
    mkLambdaFVars #[h] normalized

/-- Rewrite collected propositions using exactly the selected equation lemmas.

Equation facts themselves are retained verbatim as quantified fallback axioms.
Every other proof is transported across the simplifier's equality proof. -/
def normalizeFacts (facts : Array Fact) (lemmas : Array Name) :
    MetaM NormalizeReport := do
  if lemmas.isEmpty then return { facts }
  let ctx ← selectedSimpContext lemmas
  let mut out : Array Fact := #[]
  let mut rewritten := 0
  for fact in facts do
    if fact.isEquation then
      out := out.push fact
      continue
    let source ← instantiateMVars fact.prop
    let (result, _) ← simp source ctx
    if result.expr == source && result.proof?.isNone then
      out := out.push fact
      continue
    let proof ← fact.proof.mapM result.mkEqMP
    let negationTransform ←
      if fact.negated then
        some <$> negationTransformer source result
      else
        pure fact.negationTransform
    let reconstructionProof ←
      if fact.negated then
        some <$> result.getProof
      else
        pure fact.reconstructionProof
    out := out.push {
      fact with
      prop := result.expr
      proof
      negationTransform
      reconstructionProof }
    rewritten := rewritten + 1
  return { facts := out, rewritten }

end Crush
