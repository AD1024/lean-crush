import Lean

/-!
# Automatic unfolding: `@[crush_unfold]` and `@[crush_defeq]`

`crush_unfold` supplies equation lemmas and `crush_defeq` supplies a single unfold
equation, corresponding to explicit `u[...]` and `d[...]` hints. Automatic collection
follows only marked definitions reachable from query constants, preventing unrelated
recursive equations from entering SMT. Attribute scope and erasure are preserved;
unavailable automatic bodies are reported and skipped.
-/

open Lean Meta

namespace Crush

/-- How a marked definition contributes its equations. -/
inductive UnfoldKind where
  /-- Full equation-lemma set (`u[f]`-style). -/
  | unfold
  /-- Single unfold equation `f.eq_def` (`d[f]`-style). -/
  | defeq
  deriving Inhabited, BEq

/-- Definitions marked for automatic unfolding, with their kind. Local and scoped
attributes follow Lean's section and namespace scopes. -/
initialize crushUnfoldExt :
    SimpleScopedEnvExtension (Name × UnfoldKind) (Std.HashMap Name UnfoldKind) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun m (n, k) => m.insert n k
  }

/-- Attribute erasure changes only the current scope, like erasing a simp lemma. -/
private def eraseUnfoldAttribute (declName : Name) (kind : UnfoldKind)
    (attributeName : String) : CoreM Unit := do
  unless (crushUnfoldExt.getState (← getEnv)).get? declName == some kind do
    throwError "cannot erase [{attributeName}] from `{declName}`: the attribute is not active"
  modifyEnv fun env => crushUnfoldExt.modifyState env (·.erase declName)

/-- The equation-lemma names for a single constant under a given kind. Shared by the
attribute machinery and the `u[…]`/`d[…]` hint parser so both resolve identically.

`unfold` prefers the per-clause equation set and falls back to the unfold equation (so
non-recursive `def`s are covered); `defeq` always uses the unfold equation. Returns
`#[]` if the constant genuinely has no equations (rather than erroring — the caller
decides whether that is a problem). -/
def eqnLemmasFor (n : Name) (kind : UnfoldKind) : MetaM (Array Name) := do
  match kind with
  | .unfold =>
    match ← getEqnsFor? n with
    | some eqns => return eqns
    | none =>
      match ← getUnfoldEqnFor? n (nonRec := true) with
      | some eqn => return #[eqn]
      | none => return #[]
  | .defeq =>
    match ← getUnfoldEqnFor? n (nonRec := true) with
    | some eqn => return #[eqn]
    | none => return #[]

/-- The attribute parser names match the public names so both adding and erasing
attributes use the same spelling. -/
syntax (name := crush_unfold) "crush_unfold" : attr
syntax (name := crush_defeq) "crush_defeq" : attr

/-- `@[crush_unfold]` — fold a definition's full equation-lemma set into every `crush`
query (like `u[f]`). Two separate attributes share one extension; each checks at
attribute time that the target actually has equations, so a misuse (on an `axiom`,
`opaque`, or structure) is a declaration-time error rather than a silent no-op. -/
initialize registerBuiltinAttribute {
  name := `crush_unfold
  descr := "Fold this definition's equation lemmas into every `crush` query (like `u[f]`)."
  applicationTime := .afterCompilation
  add := fun declName _stx attrKind => do
    let hasEqns ← MetaM.run' do
      return (← getEqnsFor? declName).isSome
        || (← getUnfoldEqnFor? declName (nonRec := true)).isSome
    unless hasEqns do
      throwError "@[crush_unfold] expects a definition with equational lemmas, but \
                  `{declName}` has none (is it an `axiom`, `opaque`, or structure?)."
    crushUnfoldExt.add (declName, .unfold) attrKind
  erase := fun declName => eraseUnfoldAttribute declName .unfold "crush_unfold"
}

/-- `@[crush_defeq]` — fold a definition's single unfold equation (`f.eq_def`) into
every `crush` query (like `d[f]`). -/
initialize registerBuiltinAttribute {
  name := `crush_defeq
  descr := "Fold this definition's unfold equation into every `crush` query (like `d[f]`)."
  applicationTime := .afterCompilation
  add := fun declName _stx attrKind => do
    let hasEqn ← MetaM.run' do
      return (← getUnfoldEqnFor? declName (nonRec := true)).isSome
    unless hasEqn do
      throwError "@[crush_defeq] expects a definition with an unfold equation, but \
                  `{declName}` has none."
    crushUnfoldExt.add (declName, .defeq) attrKind
  erase := fun declName => eraseUnfoldAttribute declName .defeq "crush_defeq"
}

/-- All equation-lemma names contributed by marked definitions **relevant** to `seeds`
— the constants appearing in the goal and hypotheses. Relevance is transitive through
the marked set: if a marked `f` is reachable and its body mentions a marked `g`, then
`g`'s equations are included too, since unfolding `f` exposes `g`.

This keeps a query from being flooded with quantified equations for definitions it
never touches, which is what turns auto-unfold from a convenience into a source of
solver instantiation loops. -/
def relevantAutoUnfoldLemmas (seeds : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let marked := crushUnfoldExt.getState env
  if marked.isEmpty then return #[]
  -- Transitive closure over marked constants reachable from the seeds.
  let mut frontier := seeds
  let mut seen : Std.HashSet Name := {}
  let mut relevant : Array (Name × UnfoldKind) := #[]
  while !frontier.isEmpty do
    let n := frontier.back!
    frontier := frontier.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some kind := marked.get? n then
      -- Follow into this definition's body: constants it uses may be marked too.
      if let some ci := env.find? n then
        let some body := ci.value? | do
          logWarning m!"crush: skipping automatic unfolding of `{n}` because its definition body is unavailable"
          continue
        relevant := relevant.push (n, kind)
        for c in body.getUsedConstants do
          unless seen.contains c do frontier := frontier.push c
  -- Resolve each relevant marked constant to its equation lemmas.
  let mut names : Array Name := #[]
  for (n, kind) in relevant do
    names := names ++ (← eqnLemmasFor n kind)
  return names

/-- Rewrite equations for directly relevant predicates marked `@[reducible]`.

Unlike `@[crush_unfold]`, these equations are intended only for proof-producing
preprocessing, not as quantified SMT facts. The standard `@[reducible]` annotation
already asks Lean automation to look through a definition; honoring that signal here
is particularly useful for lightweight predicate wrappers.

Recursive predicates contribute their per-constructor equations rather than a
general unfold equation. `simp only` can therefore reduce `p []` or `p (x :: xs)`
without expanding a symbolic `p xs`, and no recursive universal axiom reaches SMT.
Users can still opt into that stronger quantified fallback with
`@[crush_unfold]`. -/
def relevantReducibleRewriteLemmas (seeds : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut frontier := seeds
  let mut seen : Std.HashSet Name := {}
  let mut names : Array Name := #[]
  while !frontier.isEmpty do
    let n := frontier.back!
    frontier := frontier.pop
    if seen.contains n then continue
    seen := seen.insert n
    unless ← Lean.isReducible n do continue
    let some ci := env.find? n | continue
    -- Recognize predicates from their final Sort 0 without opening binders.
    let rec returnsProp : Expr → Bool
      | .forallE _ _ body _ => returnsProp body
      | .sort .zero => true
      | _ => false
    unless returnsProp ci.type do continue
    let eqns ← eqnLemmasFor n .unfold
    if eqns.isEmpty then continue
    names := names ++ eqns
    -- Follow relevant predicate wrappers through equation types. A recursive
    -- body may reference an unrealized worker, while equations are the rules used here.
    for eqn in eqns do
      let some eqnInfo := (← getEnv).find? eqn | continue
      for c in eqnInfo.type.getUsedConstants do
        unless seen.contains c do frontier := frontier.push c
  return names

end Crush
