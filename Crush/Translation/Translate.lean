import Lean
import Crush.SMT.Syntax
import Crush.Translation.Monad
import Crush.Translation.Attr
open Lean Meta

/-!
# The translation driver: `Expr → SMT.Term`

Lowers a (monomorphic, first-order-after-encoding) Lean `Expr` into an
`SMT.Term`, dispatching to user `@[crush_translate]` handlers before the default
structural translator. This is the piece that constructs the `TranslationCtx`
closures (`emitTerm`/`emitSort`/`declare`) handlers recurse through.

Milestone-1 scope: propositional/Boolean structure, equality, quantifiers over a
declared sort, `Int`/`Nat` (Nat via Int with a `≥ 0` guard on quantifiers), and
uninterpreted functions/atoms. Bit-vectors, strings, datatypes, and the HO
encoding land in later milestones; anything unrecognized becomes a fresh
uninterpreted symbol so translation degrades rather than crashing.
-/

namespace Crush

open SMT

/-- A legal, non-panicking symbol hint from a Lean name (last component, or a
fallback for anonymous/numeric names). `Name.getString!` panics on those. -/
def nameHint : Name → String
  | .str _ s => s
  | .num p _ => nameHint p
  | .anonymous => "f"

/-- The natural-number value of an `@OfNat.ofNat _ (n : Nat lit) _`, if literal.
The numeral argument is a raw `Expr.lit (.natVal _)`, so we read it directly. -/
def getNatLit? (e : Expr) : TranslateM (Option Nat) := do
  match_expr e with
  | OfNat.ofNat _ n _ =>
    match (← whnf n) with
    | .lit (.natVal k) => return some k
    | _ => return none
  | _ => return none

/-- Track which sorts have had their `declare-sort` emitted, reusing the name map
with a sentinel key so we don't re-declare. -/
def declaredSort (name : String) : TranslateM Bool := do
  return (← get).atomToName.contains s!"__sortdecl__{name}"

def markSortDeclared (name : String) : TranslateM Unit :=
  modify fun s => { s with atomToName := s.atomToName.insert s!"__sortdecl__{name}" name }

/-- Whether a function symbol has been declared. -/
def declaredFun (name : String) : TranslateM Bool := do
  return (← get).atomToName.contains s!"__fundecl__{name}"

def markFunDeclared (name : String) : TranslateM Unit :=
  modify fun s => { s with atomToName := s.atomToName.insert s!"__fundecl__{name}" name }

/-- Head-and-args view that treats a bare constant/fvar as a nullary application. -/
def getAppFnArgs' (e : Expr) : Expr × Array Expr :=
  (e.getAppFn, e.getAppArgs)

/-- Sort translation. Interpreted Lean types map to SMT sorts; everything else
becomes a declared uninterpreted sort keyed by the type's canonical form. -/
partial def emitSort (e : Expr) : TranslateM SSort := do
  let e ← whnf e
  match e with
  | .const ``Bool _ => return .app (.symb "Bool") #[]
  | .const ``Nat _  => return .app (.symb "Int") #[]
  | .const ``Int _  => return .app (.symb "Int") #[]
  | .sort _         => return .app (.symb "Bool") #[]  -- Prop / Sort ↦ Bool
  | _ =>
    -- Non-dependent arrow → we do not (yet) emit a first-order function sort here;
    -- function-typed things are handled by the HO-encoding layer upstream. For a
    -- base uninterpreted type, declare a nullary sort.
    let key := toString (← ppExpr e)
    let name ← TranslateM.symbolFor key (← sortHint e)
    -- Ensure a `declare-sort` is emitted once.
    if !(← declaredSort name) then
      TranslateM.emitCommand (.declSort name 0)
      markSortDeclared name
    return .app (.symb name) #[]
where
  sortHint (e : Expr) : TranslateM String := do
    match e with
    | .const n _ => return nameHint n
    | _ => return "s"

/-- The `declare` callback exposed to handlers: emit commands from a thunk once
per key, returning a stable symbol. -/
partial def declareViaThunk (key hint : String)
    (gen : String → TranslateM (Array SMT.Command)) : TranslateM String := do
  let name ← TranslateM.symbolFor key hint
  if !(← declaredFun name) then
    let cmds ← gen name
    for c in cmds do TranslateM.emitCommand c
    markFunDeclared name
  return name

mutual
  /-- Translate a term, trying user handlers first. -/
  partial def emitTerm (e : Expr) : TranslateM SMT.Term := do
    let e ← instantiateMVars e
    -- A quantifier-bound variable renders as its SMT name, never a declaration.
    if let .fvar fid := e then
      if let some vname ← TranslateM.boundVar? fid then
        return .const vname
    -- Fast path for the structural logical/theory core.
    match ← structural? e with
    | some t => return t
    | none =>
      -- Try user handlers on the applied head.
      let (fn, args) := getAppFnArgs' e
      let ctx : TranslationCtx := {
        fn, args
        emitTerm := emitTerm
        emitSort := emitSort
        declare  := declareViaThunk }
      for h in (← getTranslationHandlers) do
        if let some t ← h ctx then
          return t
      -- Default: uninterpreted function/atom applied to translated args.
      defaultApp fn args

  /-- Recognize the built-in logical/arithmetic structure. Returns `none` to let
  handlers / the default path take over. -/
  partial def structural? (e : Expr) : TranslateM (Option SMT.Term) := do
    match e with
    | .const ``True _  => return some (.lit (.bool true))
    | .const ``False _ => return some (.lit (.bool false))
    | .const ``Bool.true _  => return some (.lit (.bool true))
    | .const ``Bool.false _ => return some (.lit (.bool false))
    | _ =>
    -- Numeric literals: `@OfNat.ofNat _ n _` and negation.
    match_expr e with
    | OfNat.ofNat _ _ _ =>
      match ← getNatLit? e with
      | some n => return some (.lit (.num n))
      | none => return none
    | Neg.neg _ _ a =>
      return some (.symbApp "-" #[← emitTerm a])
    | HDiv.hDiv _ _ _ _ a b => return some (.symbApp "div" #[← emitTerm a, ← emitTerm b])
    | HMod.hMod _ _ _ _ a b => return some (.symbApp "mod" #[← emitTerm a, ← emitTerm b])
    | _ =>
    match_expr e with
    | And a b => return some (.symbApp "and" #[← emitTerm a, ← emitTerm b])
    | Or a b  => return some (.symbApp "or" #[← emitTerm a, ← emitTerm b])
    | Not a   => return some (.symbApp "not" #[← emitTerm a])
    | Iff a b => return some (.symbApp "=" #[← emitTerm a, ← emitTerm b])
    | Eq _ a b => return some (.symbApp "=" #[← emitTerm a, ← emitTerm b])
    | HAdd.hAdd _ _ _ _ a b => return some (.symbApp "+" #[← emitTerm a, ← emitTerm b])
    | HMul.hMul _ _ _ _ a b => return some (.symbApp "*" #[← emitTerm a, ← emitTerm b])
    | HSub.hSub _ _ _ _ a b => return some (.symbApp "-" #[← emitTerm a, ← emitTerm b])
    | LE.le _ _ a b => return some (.symbApp "<=" #[← emitTerm a, ← emitTerm b])
    | LT.lt _ _ a b => return some (.symbApp "<" #[← emitTerm a, ← emitTerm b])
    | GE.ge _ _ a b => return some (.symbApp ">=" #[← emitTerm a, ← emitTerm b])
    | GT.gt _ _ a b => return some (.symbApp ">" #[← emitTerm a, ← emitTerm b])
    | _ =>
      -- Implication and quantifiers need binder handling.
      if e.isArrow then
        let some t ← tryImplication e | return none
        return some t
      match e with
      | .forallE _ ty body _ =>
        if (← isProp ty) then
          -- `p → q` as a Prop implication.
          let a ← emitTerm ty
          let b ← emitTermUnderNothing body
          return some (.symbApp "=>" #[a, b])
        else
          quantifier true ty body
      | .app (.app (.const ``Exists _) _) (.lam _ ty body _) =>
        quantifier false ty body
      | .lit (.natVal n) => return some (.lit (.num n))
      | _ => return none

  /-- `p → q` where `p : Prop`. -/
  partial def tryImplication (e : Expr) : TranslateM (Option SMT.Term) := do
    match e with
    | .forallE _ ty body _ =>
      if body.hasLooseBVar 0 then return none
      return some (.symbApp "=>" #[← emitTerm ty, ← emitTerm body])
    | _ => return none

  /-- Body of a non-dependent Prop implication translated without introducing a
  binder (the bound variable does not occur). -/
  partial def emitTermUnderNothing (body : Expr) : TranslateM SMT.Term := do
    emitTerm body

  /-- Translate `∀ (x : ty), body` / `∃ (x : ty), body` over a non-Prop sort.
  A fresh SMT-bound variable is introduced; a `Nat` domain gets a `≥ 0` guard.
  The SMT quantifier uses the *named* binder form (not de Bruijn), so we register
  the introduced fvar → name mapping and reference it directly. -/
  partial def quantifier (isForall : Bool) (ty body : Expr) : TranslateM (Option SMT.Term) := do
    let sort ← emitSort ty
    let vname ← TranslateM.freshSymbol "q"
    -- Enter the binder with a real fvar so `body` becomes a closed Expr, and bind
    -- that fvar to the SMT variable name so occurrences render as `vname`.
    let inner ← withLocalDeclD (Name.mkSimple vname) ty fun x => do
      TranslateM.withBoundVar x.fvarId! vname (emitTerm (body.instantiate1 x))
    let guarded ← guardNat isForall ty vname inner
    if isForall then
      return some (.forallE #[(vname, sort)] guarded)
    else
      return some (.existsE #[(vname, sort)] guarded)

  /-- Add a `≥ 0` guard for Nat-domained quantifiers. -/
  partial def guardNat (isForall : Bool) (ty : Expr) (vname : String) (body : SMT.Term) :
      TranslateM SMT.Term := do
    let ty ← whnf ty
    if ty.isConstOf ``Nat then
      let ge0 := Term.symbApp ">=" #[.const vname, .lit (.num 0)]
      if isForall then return .symbApp "=>" #[ge0, body]
      else return .symbApp "and" #[ge0, body]
    else
      return body

  /-- Uninterpreted-function fallback: declare the head, translate the args. -/
  partial def defaultApp (fn : Expr) (args : Array Expr) : TranslateM SMT.Term := do
    let key := toString (← ppExpr fn)
    let hint ← headHint fn
    let name ← TranslateM.symbolFor key hint
    if !(← declaredFun name) then
      let argSorts ← args.mapM (fun a => do emitSort (← inferType a))
      let resSort ← emitSort (← inferType (mkAppN fn args))
      TranslateM.emitCommand (.declFun name argSorts resSort)
      markFunDeclared name
    let sargs ← args.mapM emitTerm
    return .app (.symb name) sargs

  partial def headHint (fn : Expr) : TranslateM String := do
    match fn with
    | .const n _ => return nameHint n
    | .fvar fid => return nameHint (← fid.getUserName)
    | _ => return "f"
end

end Crush
