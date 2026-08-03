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

/-- Whether `e`'s Lean type is `Nat` (so it is encoded as a non-negative `Int`). -/
def isNatTyped (e : Expr) : TranslateM Bool := do
  return (← whnf (← inferType e)).isConstOf ``Nat

/-- Emit the non-negativity well-formedness constraint for a `Nat`-encoded symbol
`name` of arity `arity`. Nullary → `(assert (>= name 0))`; higher arity →
a universally-quantified guard over fresh vars. Emitted once per symbol.

This is the fix for the soundness bug where a `Nat` variable encoded as `Int`
could take negative values in the solver — making false goals like
`∀ n : Nat, n - 1 < n` wrongly provable. Mirrors lean-auto's `addWFConstraint`. -/
def emitNatWF (name : String) (argSorts : Array SSort) : TranslateM Unit := do
  if argSorts.isEmpty then
    TranslateM.emitCommand (.assert (.symbApp ">=" #[.const name, .lit (.num 0)]))
  else
    let mut binders : Array (String × SSort) := #[]
    let mut appArgs : Array SMT.Term := #[]
    for s in argSorts do
      let v ← TranslateM.freshSymbol "w"
      binders := binders.push (v, s)
      appArgs := appArgs.push (.const v)
    let body := Term.symbApp ">=" #[.app (.symb name) appArgs, .lit (.num 0)]
    TranslateM.emitCommand (.assert (.forallE binders body))

/-- A supported (non-recursive, non-parametric, non-indexed, `Type`-valued)
inductive we can emit as an SMT datatype. Enumerations and simple structures. -/
def isSupportedDatatype (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? n | return false
  if iv.numParams != 0 || iv.numIndices != 0 || iv.isRec then return false
  if n == ``Nat || n == ``Int || n == ``Bool then return false
  return iv.type.getForallBody.isType

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
  /-- Sort translation. Interpreted Lean types map to SMT theory sorts; supported
  inductives are declared as SMT datatypes; everything else becomes a declared
  nullary uninterpreted sort keyed by the type's canonical form. -/
  partial def emitSort (e : Expr) : TranslateM SSort := do
    let e ← whnf e
    match e with
    | .const ``Bool _ => return .app (.symb "Bool") #[]
    | .const ``Nat _  => return .app (.symb "Int") #[]
    | .const ``Int _  => return .app (.symb "Int") #[]
    | .sort _         => return .app (.symb "Bool") #[]  -- Prop / Sort ↦ Bool
    | .const n _ =>
      if ← isSupportedDatatype n then
        return .app (.symb (← declareDatatype n)) #[]
      else
        declareUninterpretedSort e
    | _ => declareUninterpretedSort e

  /-- Emit a `declare-sort` for an opaque type, once. -/
  partial def declareUninterpretedSort (e : Expr) : TranslateM SSort := do
    let key := toString (← ppExpr e)
    let hint := match e with | .const n _ => nameHint n | _ => "s"
    let name ← TranslateM.symbolFor key hint
    if !(← declaredSort name) then
      TranslateM.emitCommand (.declSort name 0)
      markSortDeclared name
    return .app (.symb name) #[]

  /-- Declare a supported inductive as an SMT datatype (idempotent); return its
  sort symbol. One SMT constructor per Lean constructor, positional selectors. -/
  partial def declareDatatype (n : Name) : TranslateM String := do
    let key := s!"__datatype__{n}"
    if let some name := (← get).atomToName.get? key then
      return name
    let sortName ← TranslateM.symbolFor key (nameHint n)
    let iv ← getConstInfoInduct n
    let mut ctorDecls : Array CtorDecl := #[]
    for ctorName in iv.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let selDecls ← forallTelescopeReducing ctorInfo.type fun args _ => do
        let mut sels : Array (String × SSort) := #[]
        for i in [0:args.size] do
          let s ← emitSort (← inferType args[i]!)
          sels := sels.push (s!"{nameHint ctorName}_sel{i}", s)
        return sels
      ctorDecls := ctorDecls.push { name := nameHint ctorName, selDecls }
    TranslateM.emitCommand (.declDatatypes #[(sortName, 0, { ctors := ctorDecls })])
    return sortName

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
      -- A constructor of a supported datatype → the SMT constructor symbol.
      if let some t ← ctorApp? fn args then
        return t
      -- A structure projection → the SMT selector.
      if let some t ← projApp? fn args then
        return t
      -- Default: uninterpreted function/atom applied to translated args.
      defaultApp fn args

  /-- If `fn` is a projection of a supported single-constructor datatype, translate
  `fn s` to the SMT selector `<ctor>_sel<i> s`. -/
  partial def projApp? (fn : Expr) (args : Array Expr) : TranslateM (Option SMT.Term) := do
    let .const pn _ := fn | return none
    let some info ← getProjectionFnInfo? pn | return none
    if !(← isSupportedDatatype info.ctorName.getPrefix) then return none
    -- Projections take the structure as the argument after `info.numParams`.
    let some structArg := args[info.numParams]? | return none
    let _ ← declareDatatype info.ctorName.getPrefix
    let sel := s!"{nameHint info.ctorName}_sel{info.i}"
    let extraArgs := args.extract (info.numParams + 1) args.size
    let sarg ← emitTerm structArg
    let sextra ← extraArgs.mapM emitTerm
    return some (.app (.symb sel) (#[sarg] ++ sextra))

  /-- If `fn` is a constructor of a supported datatype, translate the application
  to the corresponding SMT constructor symbol applied to the translated args
  (ensuring the datatype is declared first). -/
  partial def ctorApp? (fn : Expr) (args : Array Expr) : TranslateM (Option SMT.Term) := do
    let .const cn _ := fn | return none
    let env ← getEnv
    let some (.ctorInfo ci) := env.find? cn | return none
    if !(← isSupportedDatatype ci.induct) then return none
    let _ ← declareDatatype ci.induct
    let sargs ← args.mapM emitTerm
    return some (.app (.symb (nameHint cn)) sargs)

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
    | Ne _ a b => return some (.symbApp "not" #[.symbApp "=" #[← emitTerm a, ← emitTerm b]])
    | HAdd.hAdd _ _ _ _ a b => return some (.symbApp "+" #[← emitTerm a, ← emitTerm b])
    | HMul.hMul _ _ _ _ a b => return some (.symbApp "*" #[← emitTerm a, ← emitTerm b])
    | HSub.hSub _ _ _ _ a b =>
      -- `Nat` subtraction truncates at 0: `a - b = if a >= b then a - b else 0`.
      -- Encoding it as plain SMT `-` (which can go negative) is unsound.
      let sa ← emitTerm a
      let sb ← emitTerm b
      if (← isNatTyped e) then
        return some (.symbApp "ite"
          #[.symbApp ">=" #[sa, sb], .symbApp "-" #[sa, sb], .lit (.num 0)])
      else
        return some (.symbApp "-" #[sa, sb])
    | LE.le _ _ a b => return some (.symbApp "<=" #[← emitTerm a, ← emitTerm b])
    | LT.lt _ _ a b => return some (.symbApp "<" #[← emitTerm a, ← emitTerm b])
    | GE.ge _ _ a b => return some (.symbApp ">=" #[← emitTerm a, ← emitTerm b])
    | GT.gt _ _ a b => return some (.symbApp ">" #[← emitTerm a, ← emitTerm b])
    | ite _ c _ a b =>
      -- `if c then a else b`; the condition `c : Prop` becomes an SMT Bool term.
      return some (.symbApp "ite" #[← emitTerm c, ← emitTerm a, ← emitTerm b])
    | cond _ b t e =>
      -- `Bool.cond`/`cond` with a `Bool` scrutinee.
      return some (.symbApp "ite" #[← emitTerm b, ← emitTerm t, ← emitTerm e])
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

  /-- Uninterpreted-function fallback: declare the head, translate the args.

  If the head's result type is `Nat`, we additionally emit its non-negativity
  well-formedness constraint (`emitNatWF`) so the `Int` encoding cannot assign it
  a negative value — closing the soundness hole for `Nat`-valued atoms/functions
  (a bare `n : Nat` free variable, `f : α → Nat`, etc.). -/
  partial def defaultApp (fn : Expr) (args : Array Expr) : TranslateM SMT.Term := do
    let key := toString (← ppExpr fn)
    let hint ← headHint fn
    let name ← TranslateM.symbolFor key hint
    if !(← declaredFun name) then
      let argSorts ← args.mapM (fun a => do emitSort (← inferType a))
      let appExpr := mkAppN fn args
      let resTy ← whnf (← inferType appExpr)
      let resSort ← emitSort resTy
      TranslateM.emitCommand (.declFun name argSorts resSort)
      markFunDeclared name
      if resTy.isConstOf ``Nat then
        emitNatWF name argSorts
    let sargs ← args.mapM emitTerm
    return .app (.symb name) sargs

  partial def headHint (fn : Expr) : TranslateM String := do
    match fn with
    | .const n _ => return nameHint n
    | .fvar fid => return nameHint (← fid.getUserName)
    | _ => return "f"
end

end Crush
