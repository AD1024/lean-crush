import Lean

open Lean

/-!
Shared pattern matching and provenance management for type monomorphization and
ground-term instantiation. The traversal is monad-polymorphic so each pass retains its
own groundness, type-inference, and definitional-equality policy.
-/

namespace Crush.Pattern

/-- Binder assignments inferred from one or more query occurrences. -/
structure PartialSubstitution where
  values  : Array (Option Expr)
  origins : Array Nat := #[]
  deriving Inhabited

/-- A complete binder assignment and the occurrences that produced it. -/
structure Substitution where
  values  : Array Expr
  origins : Array Nat := #[]
  deriving Inhabited

/-- Whether `e` contains one of the opened template binders. -/
partial def containsBinder (e : Expr) (binders : Array Expr) : Bool :=
  match e with
  | .fvar id => binders.any fun binder => binder.fvarId! == id
  | .app f a => containsBinder f binders || containsBinder a binders
  | .lam _ ty body _ | .forallE _ ty body _ =>
    containsBinder ty binders || containsBinder body binders
  | .letE _ ty value body _ =>
    containsBinder ty binders || containsBinder value binders ||
      containsBinder body binders
  | .mdata _ body | .proj _ _ body => containsBinder body binders
  | _ => false

/-- Index of an opened template-binder fvar. -/
def binderIndex? (binders : Array Expr) (id : FVarId) : Option Nat := Id.run do
  for i in [0:binders.size] do
    if binders[i]!.fvarId! == id then return some i
  return none

def originsSubset (left right : Array Nat) : Bool :=
  left.all right.contains

def mergeOrigins (left right : Array Nat) : Array Nat :=
  right.foldl (init := left) fun origins origin =>
    if origins.contains origin then origins else origins.push origin

/-- A merge is useful only if each substitution provides a binder absent from the other. -/
def substitutionsComplementary (left right : Array (Option Expr)) : Bool :=
  let leftAdds := (Array.zip left right).any fun
    | (some _, none) => true
    | _ => false
  let rightAdds := (Array.zip left right).any fun
    | (none, some _) => true
    | _ => false
  leftAdds && rightAdds

/-- Match an opened template expression against a ground query expression. -/
@[specialize] partial def matchPattern {m : Type → Type} [Monad m]
    (isGround : Expr → m Bool) (inferType : Expr → m Expr)
    (binderType : Expr → m Expr) (isDefEq : Expr → Expr → m Bool) (pattern target : Expr)
    (binders : Array Expr) (initial : Array (Option Expr)) :
    m (Option (Array (Option Expr))) := do
  let rec go (pattern target : Expr) (subst : Array (Option Expr)) :
      m (Option (Array (Option Expr))) := do
    if pattern.hasLooseBVars || target.hasLooseBVars then return none
    if let .fvar id := pattern then
      if let some index := binderIndex? binders id then
        unless ← isGround target do return none
        unless ← isDefEq (← inferType target) (← binderType binders[index]!) do
          return none
        match subst[index]! with
        | none => return some (subst.set! index (some target))
        | some previous =>
          return if ← isDefEq previous target then some subst else none
    unless containsBinder pattern binders do
      return if ← isDefEq pattern target then some subst else none
    match pattern, target with
    | .app pf pa, .app tf ta =>
      let some subst ← go pf tf subst | return none
      go pa ta subst
    | .mdata _ body, _ => go body target subst
    | _, .mdata _ body => go pattern body subst
    | _, _ => return none
  go pattern target initial

/-- Merge compatible partial substitutions. -/
@[specialize] def mergeSubstitutions {m : Type → Type} [Monad m]
    (isDefEq : Expr → Expr → m Bool) (left right : Array (Option Expr)) :
    m (Option (Array (Option Expr))) := do
  if left.size != right.size then return none
  let mut merged := left
  for i in [0:left.size] do
    match left[i]!, right[i]! with
    | none, some value => merged := merged.set! i (some value)
    | some a, some b =>
      unless ← isDefEq a b do return none
    | _, _ => pure ()
  return some merged

/-- Retain the least restrictive provenance route for each partial substitution. -/
def addEvidence (evidence : Array PartialSubstitution)
    (values : Array (Option Expr)) (origins : Array Nat) (limit : Nat) :
    Array PartialSubstitution := Id.run do
  unless evidence.size < limit && values.any Option.isSome do return evidence
  for i in [0:evidence.size] do
    let existing := evidence[i]!
    if existing.values == values then
      if originsSubset existing.origins origins then return evidence
      if originsSubset origins existing.origins then
        return evidence.set! i { values, origins }
  return evidence.push { values, origins }

/-- Close partial substitutions under useful compatible merges. -/
@[specialize] def closeEvidence {m : Type → Type} [Monad m]
    (isDefEq : Expr → Expr → m Bool) (initial : Array PartialSubstitution)
    (limit rounds : Nat) : m (Array PartialSubstitution) := do
  let mut evidence := initial
  for _ in [0:rounds] do
    let before := evidence.size
    let snapshot := evidence
    for i in [0:snapshot.size] do
      if evidence.size >= limit then break
      let left := snapshot[i]!
      for j in [0:i] do
        if evidence.size >= limit then break
        let right := snapshot[j]!
        unless substitutionsComplementary left.values right.values do continue
        if let some merged ← mergeSubstitutions isDefEq left.values right.values then
          evidence := addEvidence evidence merged
            (mergeOrigins left.origins right.origins) limit
    if evidence.size == before then break
  return evidence

/-- Keep complete substitutions, deduplicating equal values by minimal provenance. -/
def completeEvidence (evidence : Array PartialSubstitution) (limit : Nat) :
    Array Substitution := Id.run do
  let mut out : Array Substitution := #[]
  for candidate in evidence do
    if out.size >= limit then break
    let mut values : Array Expr := #[]
    let mut complete := true
    for value in candidate.values do
      match value with
      | some value => values := values.push value
      | none => complete := false
    if complete then
      let mut retained := false
      for i in [0:out.size] do
        let existing := out[i]!
        if existing.values == values then
          retained := true
          if originsSubset candidate.origins existing.origins then
            out := out.set! i { values, origins := candidate.origins }
          break
      unless retained do
        out := out.push { values, origins := candidate.origins }
  return out

end Crush.Pattern
