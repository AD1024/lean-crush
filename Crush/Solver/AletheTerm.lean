import Lean
import Crush.SMT.Sexp
import Crush.Translation.Monad
open Lean Meta

/-!
# Alethe terms → Lean `Expr`

Proof replay (`Crush/Solver/AletheReplay.lean`) has to restate each Alethe step as a Lean
proposition, so it needs the *inverse* of translation: an Alethe S-expression back to the
Lean term it denotes. Translation is one-directional, so this module reconstructs the
inverse from two sources:

* `TranslateState.nameToExpr` — the emitted-symbol → Lean-head map recorded during
  translation, for uninterpreted symbols (`f`, `a`, `b`);
* a fixed table for the theory operators and literals crush emits (`=`, `not`, `or`,
  arithmetic, …), which have no entry in that map because they are structural.

Everything here is **partial by design**: `toExpr?` returns `none` for any construct it
cannot map faithfully, and the caller (replay) then declines the step. That keeps the
module sound on its own — failing to translate can only *lose* a replay, never fabricate
one, because a returned `Expr` is only ever used as a goal statement that Lean must then
actually prove.

## `:named` sharing

cvc5 shares subterms via `(! t :named @p_1)` and later refers to `@p_1`. A definition can
appear *inside* the very term that a later step references, so the bindings must be
collected in a pre-pass (`collectNamed`) before any term is translated; `Alethe.stripAnnot`
in the parser deliberately drops the annotations, which would otherwise leave `@p_k` as a
dangling atom with no meaning.
-/

namespace Crush.Alethe

open Crush.SMT

/-- The `(! t :named @p_k)` bindings in a proof, mapped `@p_k ↦ t` (with nested
annotations kept, so a definition may itself mention earlier names).

Collected over the *unstripped* S-expressions, since the parser's `stripAnnot` removes
exactly the information this needs. -/
partial def collectNamed (s : Sexp) (acc : Std.HashMap String Sexp := {}) :
    Std.HashMap String Sexp :=
  match s with
  | .list xs =>
    -- `(! t :named @p_k …)` — bind `@p_k ↦ t`, then descend into `t`.
    let acc :=
      if xs.size ≥ 4 && xs[0]? == some (.atom "!") && xs[2]? == some (.atom ":named") then
        match xs[1]?, xs[3]? with
        | some t, some (Sexp.atom nm) => acc.insert nm t
        | _, _ => acc
      else acc
    xs.foldl (fun a x => collectNamed x a) acc
  | _ => acc

/-- Strip `(! t :kw v …)` annotation wrappers, keeping the payload. Mirrors the parser's
`stripAnnot`, repeated here because `collectNamed` must run on unstripped input. -/
partial def stripAnnots : Sexp → Sexp
  | .list xs =>
    if xs.size ≥ 2 && xs[0]? == some (.atom "!") then
      match xs[1]? with
      | some t => stripAnnots t
      | none => .list (xs.map stripAnnots)
    else .list (xs.map stripAnnots)
  | s => s

/-- Context for translating Alethe terms back to Lean. -/
structure TermCtx where
  /-- Emitted SMT symbol → Lean head term (from `TranslateState.nameToExpr`). -/
  symbols : Std.HashMap String Expr
  /-- `:named` sharing bindings, `@p_k ↦ term`. -/
  named   : Std.HashMap String Sexp
  /-- Alethe-bound variables (from `forall`/`choice` binders) in scope. -/
  locals  : Std.HashMap String Expr := {}

/-- Numeric literal, if `s` is one. Alethe prints integers bare and negatives as
`(- n)`, which the caller handles as an application. -/
private def natLit? (s : String) : Option Nat := s.toNat?

/-- Coerce a term into a `Prop`, for a position where SMT expects a formula.

SMT-LIB has one `Bool` sort where Lean distinguishes `Bool` from `Prop`, so a translated
operand that came back `Bool`-sorted has to be lifted (`b` ↦ `b = true`) before it can sit
under `Not`/`Or`/`And`. Skipping this produced ill-typed terms that the *kernel* caught
(`¬q` with `q : Bool`) — sound, but a lost replay. -/
private def toProp (e : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType e)
  if ty.isProp then return e
  else if ty.isConstOf ``Bool then mkEq e (mkConst ``Bool.true)
  else return e

/-- Binary SMT-LIB theory operators, mapped to the Lean constant to apply. Built with the
standard instances, matching what the translator consumed on the way out. `=` and `=>` are
handled separately (`=` is `Iff` on `Prop`-sorted operands; `=>` is a Lean arrow). -/
private def binOp? : String → Option Name
  | "+"  => some ``HAdd.hAdd
  | "-"  => some ``HSub.hSub
  | "*"  => some ``HMul.hMul
  | "<"  => some ``LT.lt
  | "<=" => some ``LE.le
  | ">"  => some ``GT.gt
  | ">=" => some ``GE.ge
  | _    => none

/-- The Lean type an SMT sort denotes, for a quantifier binder.

The theory sorts are fixed; an *opaque* sort (`declare-sort`) is looked up in the same
symbol map, since the translator records the Lean type it came from. `none` for anything
else, which declines the enclosing quantifier rather than guessing a type. -/
def sortToType? (ctx : TermCtx) : Sexp → MetaM (Option Expr)
  | .atom "Int"  => return some (mkConst ``Int)
  | .atom "Bool" => return some (mkConst ``Bool)
  | .atom "String" => return some (mkConst ``String)
  | .atom s => return ctx.symbols.get? s
  | _ => return none

/-- Translate an Alethe term to the Lean term it denotes, or `none` if any part of it
cannot be mapped. `fuel` bounds the recursion through `:named` indirection (a malformed
proof could otherwise cycle).

The theory operators are matched by their SMT-LIB names, which is what crush emits; the
Lean side is built with the standard instances, matching what the translator consumed. -/
partial def toExpr? (ctx : TermCtx) (fuel : Nat) (s : Sexp) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  match s with
  | .str _ => return none
  | .atom a =>
    -- A `:named` reference expands to its definition.
    if a.startsWith "@" then
      match ctx.named.get? a with
      | some t => toExpr? ctx (fuel - 1) (stripAnnots t)
      | none => return none
    else if a == "true" then return some (mkConst ``True)
    else if a == "false" then return some (mkConst ``False)
    -- An Alethe-bound variable, then a translated symbol, then a numeral.
    else if let some e := ctx.locals.get? a then return some e
    else if let some e := ctx.symbols.get? a then return some e
    else if let some n := natLit? a then
      return some (← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Int), some (mkNatLit n), none])
    else return none
  | .list xs =>
    let some (Sexp.atom head) := xs[0]? | return none
    let args := xs.extract 1 xs.size
    -- Quantifiers bind variables, so they are handled before the argument pass (which
    -- would translate the binder list as a term). `(forall ((x S) …) body)`.
    if head == "forall" || head == "exists" then
      let some (Sexp.list binders) := args[0]? | return none
      let some body := args[1]? | return none
      -- Introduce one Lean fvar per binder, then rebuild the quantifier over them.
      let rec goBinders (i : Nat) (ctx : TermCtx) (fvars : Array Expr) :
          MetaM (Option Expr) := do
        if i ≥ binders.size then
          let some b ← toExpr? ctx (fuel - 1) body | return none
          let b ← toProp b
          if head == "forall" then return some (← mkForallFVars fvars b)
          else
            -- `∃` is not a binder former in `Expr`; build it with `Exists`.
            let mut e := b
            for v in fvars.reverse do
              e ← mkAppM ``Exists #[← mkLambdaFVars #[v] e]
            return some e
        else
          let some (Sexp.list bind) := binders[i]? | return none
          let some (Sexp.atom vname) := bind[0]? | return none
          let some sortSexp := bind[1]? | return none
          let some ty ← sortToType? ctx sortSexp | return none
          withLocalDeclD (Name.mkSimple vname) ty fun v =>
            goBinders (i + 1) { ctx with locals := ctx.locals.insert vname v }
              (fvars.push v)
      return ← goBinders 0 ctx #[]
    -- Translate all arguments; any untranslatable argument fails the whole term.
    let mkArgs : MetaM (Option (Array Expr)) := do
      let mut out := #[]
      for a in args do
        let some e ← toExpr? ctx (fuel - 1) a | return none
        out := out.push e
      return some out
    -- `ite` needs a `Decidable` instance to rebuild; declined for now.
    if head == "ite" then return none
    let some as ← mkArgs | return none
    -- Right-nested n-ary connective, matching how the translator flattens `∨`/`∧`. The
    -- operands sit in formula positions, so each is lifted to `Prop` first.
    let nary (c : Name) (unit : Expr) : MetaM Expr := do
      if as.isEmpty then return unit
      let ps ← as.mapM toProp
      let mut e := ps.back!
      for i in [1:ps.size] do
        e ← mkAppM c #[ps[ps.size - 1 - i]!, e]
      return e
    match head, as.size with
    | "not", 1 => return some (mkApp (mkConst ``Not) (← toProp as[0]!))
    | "=", 2 =>
      -- SMT `=` on two formulas is Lean `Iff`; on data it is `Eq`. Only *both* sides
      -- being `Prop` makes it `Iff` — a `Bool`-sorted equation stays an `Eq` on `Bool`,
      -- which is what the translator emitted and what `decide` can evaluate.
      let t0 ← whnf (← inferType as[0]!)
      let t1 ← whnf (← inferType as[1]!)
      if t0.isProp && t1.isProp then return some (← mkAppM ``Iff #[as[0]!, as[1]!])
      else if t0.isProp != t1.isProp then
        -- Mixed `Prop`/`Bool`: lift both so the equation is well-formed as an `Iff`.
        return some (← mkAppM ``Iff #[← toProp as[0]!, ← toProp as[1]!])
      else return some (← mkEq as[0]! as[1]!)
    | "or", _  => return some (← nary ``Or (mkConst ``False))
    | "and", _ => return some (← nary ``And (mkConst ``True))
    | "=>", 2  => return some (← mkArrow (← toProp as[0]!) (← toProp as[1]!))
    | "-", 1   => return some (← mkAppM ``Neg.neg #[as[0]!])
    | _, 2 =>
      match binOp? head with
      | some c => return some (← mkAppM c #[as[0]!, as[1]!])
      | none   => uninterp as
    | _, _ => uninterp as
where
  /-- An uninterpreted symbol applied to translated arguments: rebuild `head args…`.
  A mis-rebuilt (ill-typed) application is rejected rather than returned. -/
  uninterp (as : Array Expr) : MetaM (Option Expr) := do
    let .list xs := s | return none
    let some (Sexp.atom head) := xs[0]? | return none
    let some fn := ctx.symbols.get? head | return none
    try
      let e ← mkAppM' fn as
      let _ ← inferType e
      return some e
    catch _ => return none

/-- A clause `(cl t₁ … tₙ)` as the Lean proposition it asserts: the disjunction of its
literals, and `False` for the empty clause. -/
def clauseToExpr? (ctx : TermCtx) (fuel : Nat) (lits : Array Sexp) : MetaM (Option Expr) := do
  if lits.isEmpty then return some (mkConst ``False)
  let mut out := #[]
  for l in lits do
    let some e ← toExpr? ctx fuel l | return none
    -- Clause literals are formulas; a `Bool`-sorted one must be lifted before it can be
    -- a disjunct (Lean's `Or` takes `Prop`s).
    out := out.push (← toProp e)
  let mut e := out.back!
  for i in [1:out.size] do
    e ← mkAppM ``Or #[out[out.size - 1 - i]!, e]
  return some e

end Crush.Alethe
