import Crush

/-!
Proof-domain function values need an encoding that respects proof irrelevance and
the proposition's truth. Both higher-order modes must refuse ordinary arrow sorts
for them, including closed domains and proof binders later in a curried telescope.
Logical implications and fully applied proof-argument erasure remain supported.
Refused premises leave no partial declarations; refused negated goals remain fatal.
-/

open Lean Meta Crush

namespace SoundnessProofDomains

private def expectProofDomainRefused (action : MetaM Unit) : MetaM Unit := do
  let refused ← try
    action
    pure false
  catch ex =>
    unless (← ex.toMessageData.toString).startsWith
        "crush: cannot translate a proof-domain function type:" do
      throw ex
    pure true
  unless refused do
    throwError "accepted a proof-domain function as an ordinary arrow"

run_meta do
  withLocalDeclD `p (mkSort .zero) fun p => do
    for mode in #[HOMode.defunctionalize, .native] do
      let cfg : Crush.Config := { hoMode := mode }
      for domain in #[mkConst ``False, mkConst ``True, p] do
        let arrow ← mkArrow domain (mkConst ``Int)
        let curried ← mkArrow (mkConst ``Int) arrow
        let nested ← mkArrow arrow (mkConst ``Int)
        for ty in #[arrow, curried, nested] do
          expectProofDomainRefused do discard <| TranslateM.run cfg (emitSort ty)
          expectProofDomainRefused do discard <| TranslateM.run cfg (declareArrowSort ty)
        let lam ← withLocalDeclD `h domain fun h =>
          mkLambdaFVars #[h] (mkIntLit 0)
        expectProofDomainRefused do discard <| TranslateM.run cfg (emitTerm lam)
        -- Quantified function values use the same sort boundary.
        let quantified ← withLocalDeclD `f arrow fun f => do
          mkForallFVars #[f] (← mkEq f f)
        expectProofDomainRefused do discard <| TranslateM.run cfg (emitTerm quantified)
      -- Prop as a domain contains propositions, not proofs.
      let arrow ← mkArrow (mkSort .zero) (mkConst ``Int)
      discard <| TranslateM.run cfg <| emitSort arrow

private theorem erasedApplications (p : Prop) (f : p → Int) :
    ∀ h₁ h₂ : p, f h₁ = f h₂ := fun _ _ => rfl

run_meta do
  for mode in #[HOMode.defunctionalize, .native] do
    withLocalDeclD `p (mkSort .zero) fun p => do
      let arrow ← mkArrow p (mkConst ``Int)
      withLocalDeclD `f arrow fun f => do
        let fact ← inferType (mkApp2 (mkConst ``erasedApplications) p f)
        discard <| TranslateM.run { hoMode := mode } <| emitTerm fact
      let implication ← mkArrow p p
      discard <| TranslateM.run { hoMode := mode } <| emitTerm implication

run_meta do
  let arrow ← mkArrow (mkConst ``False) (mkConst ``Int)
  let nested ← mkArrow arrow (mkConst ``Int)
  let prop ← withLocalDeclD `f nested fun f => do
    mkForallFVars #[f] (← mkEq f f)
  let unsupported : Fact := { prop, proof := none, descr := "proof-domain premise" }
  let goal : Fact := {
    prop := mkNot (mkConst ``False), proof := none, descr := "negated goal", negated := true }
  for mode in #[HOMode.defunctionalize, .native] do
    let cfg : Crush.Config := { backend := .cvc5, hoMode := mode }
    let (expected, _) ← buildScript cfg #[goal]
    let (actual, _) ← buildScript cfg #[unsupported, goal]
    unless SMT.scriptToString actual == SMT.scriptToString expected do
      throwError "a refused proof-domain premise retained partial declarations"
    expectProofDomainRefused do
      discard <| buildScript cfg #[{ unsupported with negated := true }]
    expectProofDomainRefused do
      discard <| buildScript { cfg with backend := .none } #[unsupported]

end SoundnessProofDomains
