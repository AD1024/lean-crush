import Crush.Solver.Alethe.ReplayAttr
import Crush.Solver.Alethe.BitBlast

/-!
# Checked replay of bit-blasted addition and multiplication

Handlers for `bv_bitblast_step_bvadd`, `bv_bitblast_step_bvmult` and
`bv_bitblast_step_bvequal`, proved with `add_eq_of_bits`, `mul_eq_of_bits` and
`eq_iff_of_bits`. Each step is kernel-checked before it is returned.
-/

open Lean Meta Elab Tactic

namespace Crush.Alethe.BitBlastRules

open Crush.Alethe.BitBlast

/-- A bit's `Bool` value, with `e = value` (or `e ↔ value = true` for a `Prop`). -/
structure Reified where
  value : Expr
  proof : Expr
  deriving Inhabited

/-- Reification state, shared across the certificate's DAG. -/
structure ReifyState where
  /-- Reified propositions, booleans and bits. -/
  terms : Std.HashMap Expr Reified := {}
  /-- Elements of list literals. -/
  lists : Std.HashMap Expr (Option (Array Expr)) := {}

abbrev ReifyM := StateRefT ReifyState MetaM

private def boolType : Expr := mkConst ``Bool

private def eqRefl (e : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolType e

private def eqTrans (a b c p q : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [1]) boolType a b c p q

private def getLsbD (w v k : Expr) : Expr := mkApp3 (mkConst ``BitVec.getLsbD) w v k

/-- The elements of a list literal. -/
private partial def listElems? (e : Expr) : Option (Array Expr) :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Option (Array Expr) :=
    match e.getAppFnArgs with
    | (``List.nil, #[_]) => some acc
    | (``List.cons, #[_, head, tail]) => go tail (acc.push head)
    | _ => none

/-- `listElems?`, computed once per list. -/
private def cachedListElems? (e : Expr) : ReifyM (Option (Array Expr)) := do
  if let some elems := (← get).lists[e]? then return elems
  let elems := listElems? e
  modify fun s => { s with lists := s.lists.insert e elems }
  return elems

private def cached (e : Expr) (k : ReifyM Reified) : ReifyM Reified := do
  if let some r := (← get).terms[e]? then return r
  let r ← k
  modify fun s => { s with terms := s.terms.insert e r }
  return r

mutual
  /-- `e ↔ value = true` for a decoded `Prop`. -/
  partial def reifyProp (e : Expr) : ReifyM Reified :=
    cached e (reifyPropCore e)

  partial def reifyPropCore (e : Expr) : ReifyM Reified := do
    if e.isConstOf ``True then
      return { value := mkConst ``Bool.true, proof := mkConst ``reify_true }
    if e.isConstOf ``False then
      return { value := mkConst ``Bool.false, proof := mkConst ``reify_false }
    if e.isAppOfArity ``Eq 3 && (e.getArg! 0).isConstOf ``Bool &&
        (e.getArg! 2).isConstOf ``Bool.true then
      let t := e.getArg! 1
      let r ← reifyBool t
      return { value := r.value, proof := mkApp3 (mkConst ``reify_eq_true) t r.value r.proof }
    if e.isAppOfArity ``And 2 then
      return ← propBinary ``reify_and ``Bool.and (e.getArg! 0) (e.getArg! 1)
    if e.isAppOfArity ``Or 2 then
      return ← propBinary ``reify_or ``Bool.or (e.getArg! 0) (e.getArg! 1)
    if e.isAppOfArity ``Not 1 then
      let p := e.getArg! 0
      -- Decoded xor.
      if p.isAppOfArity ``Iff 2 then
        return ← propBinary ``reify_xor ``Bool.xor (p.getArg! 0) (p.getArg! 1)
      let r ← reifyProp p
      return { value := mkApp (mkConst ``Bool.not) r.value
               proof := mkApp3 (mkConst ``reify_not) p r.value r.proof }
    if e.isAppOfArity ``Iff 2 then
      let p := e.getArg! 0
      let q := e.getArg! 1
      let rp ← reifyProp p
      let rq ← reifyProp q
      return { value := mkApp (mkConst ``Bool.not) (mkApp2 (mkConst ``Bool.xor) rp.value rq.value)
               proof := mkApp6 (mkConst ``reify_iff) p q rp.value rq.value rp.proof rq.proof }
    -- Opaque proposition.
    let inst := mkApp (mkConst ``Classical.propDecidable) e
    return { value := mkApp2 (mkConst ``Decidable.decide) e inst
             proof := mkApp (mkConst ``reify_prop_atom) e }

  partial def propBinary (lemma op : Name) (p q : Expr) : ReifyM Reified := do
    let rp ← reifyProp p
    let rq ← reifyProp q
    return { value := mkApp2 (mkConst op) rp.value rq.value
             proof := mkApp6 (mkConst lemma) p q rp.value rq.value rp.proof rq.proof }

  /-- `e = value` for a decoded `Bool`. -/
  partial def reifyBool (e : Expr) : ReifyM Reified :=
    cached e (reifyBoolCore e)

  partial def reifyBoolCore (e : Expr) : ReifyM Reified := do
    match e.getAppFnArgs with
    | (``Bool.xor, #[s, t]) => boolBinary ``reify_bxor ``Bool.xor s t
    | (``Bool.and, #[s, t]) => boolBinary ``reify_band ``Bool.and s t
    | (``Bool.or, #[s, t]) => boolBinary ``reify_bor ``Bool.or s t
    | (``Bool.not, #[s]) =>
      let r ← reifyBool s
      return { value := mkApp (mkConst ``Bool.not) r.value
               proof := mkApp3 (mkConst ``reify_bnot) s r.value r.proof }
    | (``Decidable.decide, #[p, inst]) =>
      let r ← reifyProp p
      return { value := r.value, proof := mkApp4 (mkConst ``reify_decide) p inst r.value r.proof }
    -- Expand a bit like an operand's, so both sides of a step agree.
    | (``BitVec.getLsbD, #[w, v, i]) =>
      match i.rawNatLit? <|> i.nat? with
      | some k => bitOf w v k
      | none => return { value := e, proof := eqRefl e }
    | _ => return { value := e, proof := eqRefl e }

  partial def boolBinary (lemma op : Name) (s t : Expr) : ReifyM Reified := do
    let rs ← reifyBool s
    let rt ← reifyBool t
    return { value := mkApp2 (mkConst op) rs.value rt.value
             proof := mkApp6 (mkConst lemma) s t rs.value rt.value rs.proof rt.proof }

  /-- `v.getLsbD k = value` for a decoded operand `v : BitVec w`. -/
  partial def bitOf (w v : Expr) (k : Nat) : ReifyM Reified :=
    let bit := getLsbD w v (mkNatLit k)
    cached bit (bitOfCore w v k bit)

  partial def bitOfCore (w v : Expr) (k : Nat) (bit : Expr) : ReifyM Reified := do
    let kE := mkNatLit k
    match v.getAppFnArgs with
    | (``BitVec.ofBoolListLE, #[bs]) =>
      if let some elems ← cachedListElems? bs then
        if let some e := elems[k]? then
          let r ← reifyBool e
          return { value := r.value
                   proof := eqTrans bit e r.value (mkApp2 (mkConst ``getLsbD_ofBoolListLE') bs kE)
                     r.proof }
    | (``BitVec.xor, #[n, x, y]) =>
      return ← bitBinary ``getLsbD_xor' ``reify_bxor ``Bool.xor ``BitVec.xor n x y k
    | (``BitVec.and, #[n, x, y]) =>
      return ← bitBinary ``getLsbD_and' ``reify_band ``Bool.and ``BitVec.and n x y k
    | (``BitVec.or, #[n, x, y]) =>
      return ← bitBinary ``getLsbD_or' ``reify_bor ``Bool.or ``BitVec.or n x y k
    | (``BitVec.not, #[n, x]) =>
      let some width := (← whnf n).rawNatLit? <|> (← getNatValue? n) | pure ()
      if k < width then
        let rx ← bitOf n x k
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, n])
        let notBit := mkApp (mkConst ``Bool.not) (getLsbD n x kE)
        return { value := mkApp (mkConst ``Bool.not) rx.value
                 proof := eqTrans bit notBit (mkApp (mkConst ``Bool.not) rx.value)
                   (mkApp4 (mkConst ``getLsbD_not') n x kE hk)
                   (mkApp3 (mkConst ``reify_bnot) (getLsbD n x kE) rx.value rx.proof) }
    | (``BitVec.ofNat, #[n, m]) =>
      -- A constant: the kernel evaluates its bit.
      if let (some width, some value) := (← getNatValue? n, ← getNatValue? m) then
        let b := if k < width && value.testBit k then ``Bool.true else ``Bool.false
        return { value := mkConst b, proof := eqRefl (mkConst b) }
    | _ => pure ()
    return { value := bit, proof := eqRefl bit }

  /-- Bit `k` of the bitwise operation `vecOp n x y`. -/
  partial def bitBinary (lemma reify op vecOp : Name) (n x y : Expr) (k : Nat) :
      ReifyM Reified := do
    let kE := mkNatLit k
    let rx ← bitOf n x k
    let ry ← bitOf n y k
    let raw := mkApp2 (mkConst op) (getLsbD n x kE) (getLsbD n y kE)
    let value := mkApp2 (mkConst op) rx.value ry.value
    return { value
             proof := eqTrans (getLsbD n (mkApp3 (mkConst vecOp) n x y) kE) raw value
               (mkApp4 (mkConst lemma) n x y kE)
               (mkApp6 (mkConst reify) (getLsbD n x kE) (getLsbD n y kE) rx.value ry.value
                 rx.proof ry.proof) }
end

/-- A proof of `∀ k, k < proofs.size → P k` from proofs of `P 0, …`. -/
private def forallLt (p : Expr) (proofs : Array Expr) : Expr := Id.run do
  let mut acc := mkApp (mkConst ``forall_lt_zero) p
  for h : n in [:proofs.size] do
    acc := mkApp4 (mkConst ``forall_lt_succ) p (mkNatLit n) acc proofs[n]
  return acc

/-- `fun k => [values].getD k false`. -/
private def bitFunction (values : Array Expr) : MetaM Expr := do
  let list ← mkListLit boolType values.toList
  return .lam `k (mkConst ``Nat)
    (mkApp4 (mkConst ``List.getD [0]) boolType list (.bvar 0) (mkConst ``Bool.false)) .default

/-- Whether the kernel accepts `proof : expected`. -/
private def kernelAccepts (expected proof : Expr) : MetaM Bool := do
  match Kernel.check (← getEnv) (← getLCtx) (mkApp2 (mkConst ``id [0]) expected proof) with
  | .ok _ => return true
  | .error _ => return false

/-- Replay `L ∘ R = ofBoolListLE bits` for cvc5's adder (`multiply := false`) or
multiplier. -/
def replayBitBlast (ctx : ReplayRuleContext) (multiply : Bool) : TacticM (Option Expr) := do
  let target ← instantiateMVars ctx.target
  if target.hasMVar then return none
  let some (_, lhs, rhs) := target.eq? | return none
  let op := if multiply then ``BitVec.mul else ``BitVec.add
  let (opName, #[w, l, r]) := lhs.getAppFnArgs | return none
  unless opName == op do return none
  let (``BitVec.ofBoolListLE, #[bs]) := rhs.getAppFnArgs | return none
  let some outs := listElems? bs | return none
  let width := outs.size
  if width == 0 then return none
  unless ← isDefEq w (mkNatLit width) do return none
  let build : ReifyM Expr := do
    let mut aValues := #[]
    let mut aProofs := #[]
    let mut bValues := #[]
    let mut bProofs := #[]
    for k in [:width] do
      let ra ← bitOf w l k
      let rb ← bitOf w r k
      aValues := aValues.push ra.value
      aProofs := aProofs.push ra.proof
      bValues := bValues.push rb.value
      bProofs := bProofs.push rb.proof
    let a ← bitFunction aValues
    let b ← bitFunction bValues
    let mut vProofs := #[]
    for i in [:width] do
      let ri ← reifyBool outs[i]!
      let iE := mkNatLit i
      vProofs := vProofs.push <| eqTrans (getLsbD w rhs iE) outs[i]! ri.value
        (mkApp2 (mkConst ``getLsbD_ofBoolListLE') bs iE) ri.proof
    let nat := mkConst ``Nat
    let bitEq (v f : Expr) : Expr :=
      .lam `k nat (mkApp3 (mkConst ``Eq [1]) boolType (getLsbD w v (.bvar 0)) (mkApp f (.bvar 0)))
        .default
    let circuit :=
      if multiply then mkApp3 (mkConst ``mulRow) a b (mkNatLit (width - 1))
      else mkApp2 (mkConst ``addSum) a b
    let lemma := if multiply then ``mul_eq_of_bits else ``add_eq_of_bits
    return mkAppN (mkConst lemma)
      #[w, l, r, rhs, a, b, forallLt (bitEq l a) aProofs, forallLt (bitEq r b) bProofs,
        forallLt (bitEq rhs circuit) vProofs]
  let proof ← try build.run' {} catch _ => return none
  unless ← kernelAccepts target proof do
    trace[crush.replay] "bit-blast step {ctx.stepId}: the circuit does not match cvc5's"
    return none
  return some proof

/-- The conjuncts of `c₀ ∧ (c₁ ∧ …)`, with the remaining conjunction after each. -/
private partial def conjuncts (e : Expr) : Array (Expr × Expr) :=
  go e #[]
where
  go (e : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
    if e.isAppOfArity ``And 2 then go (e.getArg! 1) (acc.push (e.getArg! 0, e))
    else acc.push (e, e)

/-- `c ↔ v₁ = v₂` for a decoded bit equation `c`. -/
private def reifyBitEq (c : Expr) : ReifyM (Option Expr) := do
  if c.isAppOfArity ``Iff 2 then
    let p := c.getArg! 0
    let q := c.getArg! 1
    let rp ← reifyProp p
    let rq ← reifyProp q
    return some (mkApp6 (mkConst ``reify_iff_eq) p q rp.value rq.value rp.proof rq.proof)
  if c.isAppOfArity ``Eq 3 && (c.getArg! 0).isConstOf ``Bool then
    let s := c.getArg! 1
    let t := c.getArg! 2
    let rs ← reifyBool s
    let rt ← reifyBool t
    return some (mkApp6 (mkConst ``reify_beq) s t rs.value rt.value rs.proof rt.proof)
  return none

/-- Replay `(A = B) ↔ ⋀ᵢ (aᵢ ↔ bᵢ)`, cvc5's bit-blasted equality. -/
def replayBitBlastEqual (ctx : ReplayRuleContext) : TacticM (Option Expr) := do
  let target ← instantiateMVars ctx.target
  if target.hasMVar then return none
  let some (lhs, conj) := target.iff? | return none
  let some (type, A, B) := lhs.eq? | return none
  -- The carrier may be an alias of `BitVec w`.
  let (``BitVec, #[w]) := (← whnf type).getAppFnArgs | return none
  let parts := conjuncts conj
  let width := parts.size
  unless ← isDefEq w (mkNatLit width) do return none
  let build : ReifyM (Option Expr) := do
    let mut aValues := #[]
    let mut aProofs := #[]
    let mut bValues := #[]
    let mut bProofs := #[]
    let mut cProofs := #[]
    for k in [:width] do
      let ra ← bitOf w A k
      let rb ← bitOf w B k
      aValues := aValues.push ra.value
      aProofs := aProofs.push ra.proof
      bValues := bValues.push rb.value
      bProofs := bProofs.push rb.proof
      let some hc ← reifyBitEq parts[k]!.1 | return none
      cProofs := cProofs.push hc
    let a ← bitFunction aValues
    let b ← bitFunction bValues
    let nat := mkConst ``Nat
    let bitEq (v f : Expr) : Expr :=
      .lam `k nat (mkApp3 (mkConst ``Eq [1]) boolType (getLsbD w v (.bvar 0)) (mkApp f (.bvar 0)))
        .default
    let p := Expr.lam `k nat
      (mkApp3 (mkConst ``Eq [1]) boolType (mkApp a (.bvar 0)) (mkApp b (.bvar 0))) .default
    let n := mkNatLit width
    -- Fold the conjunction from its last conjunct.
    let last := width - 1
    let mut chain := mkApp4 (mkConst ``conj_last) parts[last]!.1 p (mkNatLit last) cProofs[last]!
    for j in [:last] do
      let i := last - 1 - j
      let hin ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, n])
      chain := mkAppN (mkConst ``conj_cons)
        #[parts[i]!.1, parts[i + 1]!.2, p, mkNatLit i, n, cProofs[i]!, chain, hin]
    let hC := mkApp4 (mkConst ``conj_all) conj p n chain
    return some <| mkAppN (mkConst ``eq_iff_of_bits)
      #[w, A, B, a, b, forallLt (bitEq A a) aProofs, forallLt (bitEq B b) bProofs, conj, hC]
  let some proof ← (try build.run' {} catch _ => pure none) | return none
  unless ← kernelAccepts target proof do
    trace[crush.replay] "bit-blast step {ctx.stepId}: the bit equations do not match"
    return none
  return some proof

@[crush_replay_rule "bv_bitblast_step_bvequal"]
def replayBitBlastEq : ReplayRuleHandler := replayBitBlastEqual

@[crush_replay_rule "bv_bitblast_step_bvadd"]
def replayBitBlastAdd : ReplayRuleHandler := fun ctx => replayBitBlast ctx false

@[crush_replay_rule "bv_bitblast_step_bvmult"]
def replayBitBlastMul : ReplayRuleHandler := fun ctx => replayBitBlast ctx true

end Crush.Alethe.BitBlastRules
