import Lean
open Lean Meta

/-!
# Automatic unfolding: `@[crush_unfold]` and `@[crush_defeq]`

Marking a definition with `@[crush_unfold]` (or `@[crush_defeq]`) folds its equation
lemmas into *every* `crush` query automatically, so a recursive function used in a goal
no longer needs an explicit `u[f]`/`d[f]` hint on each call. This is the `@[simp]`-style
ergonomic: annotate the definition once, and every subsequent `crush` sees its
equations.

* `@[crush_unfold]` — like `u[f]`: the full equation-lemma set (`getEqnsFor?`, falling
  back to the unfold equation), i.e. one fact per defining clause.
* `@[crush_defeq]` — like `d[f]`: the single unfold equation `f.eq_def`.

**Relevance filtering is essential.** A recursive function's equations are *quantified
axioms*; handing the solver a pile of unrelated ones invites instantiation loops (the
same divergence documented for guarded recursive datatypes). So `crush` includes a
marked definition's equations only when that definition is **reachable from the goal or
a hypothesis** — transitively through the marked set. A `@[crush_unfold]` function the
query never mentions costs nothing. `set_option crush.autoUnfold false` disables the
whole mechanism.
-/

namespace Crush

/-- How a marked definition contributes its equations. -/
inductive UnfoldKind where
  /-- Full equation-lemma set (`u[f]`-style). -/
  | unfold
  /-- Single unfold equation `f.eq_def` (`d[f]`-style). -/
  | defeq
  deriving Inhabited, BEq

/-- Persistent set of definitions marked for automatic unfolding, with their kind.
Keyed by the definition's `Name`; the value records `unfold` vs. `defeq`. -/
initialize crushUnfoldExt :
    SimplePersistentEnvExtension (Name × UnfoldKind) (Std.HashMap Name UnfoldKind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, k) => m.insert n k
    addImportedFn := fun ms => ms.foldl (fun acc arr =>
      arr.foldl (fun acc (n, k) => acc.insert n k) acc) {}
  }

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

/-- The user-facing attribute keywords. `registerBuiltinAttribute` keys on `name`, so
without these the attribute would have to be written `@[crushUnfoldAttr]`; the `syntax`
declarations give the friendly `@[crush_unfold]` / `@[crush_defeq]` spellings. -/
syntax (name := crushUnfoldAttr) "crush_unfold" : attr
syntax (name := crushDefeqAttr) "crush_defeq" : attr

/-- `@[crush_unfold]` — fold a definition's full equation-lemma set into every `crush`
query (like `u[f]`). Two separate attributes share one extension; each checks at
attribute time that the target actually has equations, so a misuse (on an `axiom`,
`opaque`, or structure) is a declaration-time error rather than a silent no-op. -/
initialize registerBuiltinAttribute {
  name := `crushUnfoldAttr
  descr := "Fold this definition's equation lemmas into every `crush` query (like `u[f]`)."
  applicationTime := .afterCompilation
  add := fun declName _stx _ => do
    let hasEqns ← MetaM.run' do
      return (← getEqnsFor? declName).isSome
        || (← getUnfoldEqnFor? declName (nonRec := true)).isSome
    unless hasEqns do
      throwError "@[crush_unfold] expects a definition with equational lemmas, but \
                  `{declName}` has none (is it an `axiom`, `opaque`, or structure?)."
    modifyEnv fun env => crushUnfoldExt.addEntry env (declName, .unfold)
}

/-- `@[crush_defeq]` — fold a definition's single unfold equation (`f.eq_def`) into
every `crush` query (like `d[f]`). -/
initialize registerBuiltinAttribute {
  name := `crushDefeqAttr
  descr := "Fold this definition's unfold equation into every `crush` query (like `d[f]`)."
  applicationTime := .afterCompilation
  add := fun declName _stx _ => do
    let hasEqn ← MetaM.run' do
      return (← getUnfoldEqnFor? declName (nonRec := true)).isSome
    unless hasEqn do
      throwError "@[crush_defeq] expects a definition with an unfold equation, but \
                  `{declName}` has none."
    modifyEnv fun env => crushUnfoldExt.addEntry env (declName, .defeq)
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
      relevant := relevant.push (n, kind)
      -- Follow into this definition's body: constants it uses may be marked too.
      if let some ci := env.find? n then
        for c in ci.value!.getUsedConstants do
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
    -- Predicates have declaration type `... → Prop`; no binder instantiation is
    -- needed to recognize the final `Sort 0`.
    let rec returnsProp : Expr → Bool
      | .forallE _ _ body _ => returnsProp body
      | .sort .zero => true
      | _ => false
    unless returnsProp ci.type do continue
    let eqns ← eqnLemmasFor n .unfold
    if eqns.isEmpty then continue
    names := names ++ eqns
    -- Follow chains of reducible predicate wrappers without scanning unrelated
    -- declarations from the imported environment. Inspect equation types rather
    -- than `ci.value`: a freshly compiled recursive definition may keep its
    -- private worker unrealized, while these are the exact rules used below.
    for eqn in eqns do
      let some eqnInfo := (← getEnv).find? eqn | continue
      for c in eqnInfo.type.getUsedConstants do
        unless seen.contains c do frontier := frontier.push c
  return names

end Crush
