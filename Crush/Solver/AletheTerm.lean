import Lean
import Crush.SMT.Sexp
import Crush.Solver.AletheAttr
import Crush.Translation.Monad
open Lean Meta

/-!
# Alethe terms → Lean `Expr`

Proof replay (`Crush/Solver/AletheReplay.lean`) restates each Alethe step as a Lean
proposition, so it needs the *inverse* of translation. Translation is one-directional, so
this module reconstructs the inverse from two sources:

* `TranslateState.nameToExpr` — the emitted-symbol → Lean-head map recorded during
  translation, for uninterpreted symbols (`f`, `a`, `b`);
* a fixed table for the theory operators and literals crush emits (`=`, `not`, `or`,
  arithmetic, …), which are structural and so have no entry in that map.

`toExpr?` is **partial by design**: `none` for anything it cannot map faithfully, which
makes the caller decline the step. A returned `Expr` is only ever used as a goal statement
Lean must then prove, so a bad translation loses a replay rather than fabricating one.

## `:named` sharing

cvc5 shares subterms via `(! t :named @p_1)` and later refers to `@p_1`. A definition can
appear *inside* the very term that a later step references, so the bindings must be
collected in a pre-pass (`collectNamed`) before any term is translated; `Alethe.stripAnnot`
in the parser deliberately drops the annotations, which would otherwise leave `@p_k` as a
dangling atom with no meaning.
-/

namespace Crush.Alethe

open Crush.SMT

/-- The `(! t :named @p_k)` bindings in a proof, mapped `@p_k ↦ t` (nested annotations
kept, so a definition may itself mention earlier names).

Must run on the *unstripped* S-expressions: the parser's `stripAnnot` removes exactly the
information this collects. -/
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
  /-- User inverse decoders, resolved once for this replay. -/
  decoders : AletheDecoderRegistry := {}

/-- Expand Alethe `:named` references while preserving the surrounding term shape. -/
private partial def expandNamed? (ctx : TermCtx) (fuel : Nat) (term : Sexp) :
    Option Sexp := do
  if fuel == 0 then failure
  match term with
  | .atom name =>
    if name.startsWith "@" then
      match ctx.named.get? name with
      | some value => expandNamed? ctx (fuel - 1) (stripAnnots value)
      | none => return term
    else
      return term
  | .list parts =>
    return .list (← parts.mapM fun part => expandNamed? ctx (fuel - 1) part)
  | .str _ => return term

/-- Integer literal, if `s` is one. cvc5 uses both `(- n)` and signed atoms such as `-1`
in Alethe certificates. -/
private def intLit? (s : String) : Option Int := s.toInt?

/-- Parse an unsigned numeral in the given radix. -/
private def parseRadix? (radix : Nat) (digits : String) : Option Nat := do
  let mut value := 0
  for char in digits.toList do
    let digit ←
      if char.isDigit then some (char.toNat - '0'.toNat)
      else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
      else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
      else none
    if digit ≥ radix then failure
    value := value * radix + digit
  return value

/-- A binary or hexadecimal SMT bit-vector atom. -/
private def bitVecAtom? (atom : String) : Option (Nat × Nat) := do
  if atom.startsWith "#b" then
    let digits := (atom.drop 2).toString
    return (digits.length, ← parseRadix? 2 digits)
  if atom.startsWith "#x" then
    let digits := (atom.drop 2).toString
    return (4 * digits.length, ← parseRadix? 16 digits)
  none

/-- Construct a bit-vector literal. -/
private def mkBitVecLit (width value : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit width) (mkNatLit value)

/-- The statically known width of a reconstructed bit-vector expression. -/
private def bitVecWidth? (value : Expr) : MetaM (Option Nat) := do
  let type ← whnf (← inferType value)
  let .app (.const ``BitVec _) width := type | return none
  getNatValue? (← whnf width)

/-- A nonnegative concrete index printed as either an SMT integer or a Lean natural. -/
private def indexValue? (value : Expr) : MetaM (Option Nat) := do
  if let some natural ← getNatValue? value then return some natural
  let some integer ← getIntValue? value | return none
  if integer < 0 then return none
  return some integer.toNat

/-- Lean counterpart of SMT-LIB `str.substr`, whose indices count codepoints. -/
def stringSubstr (s : String) (start count : Int) : String :=
  if start < 0 then ""
  else ((s.drop start.toNat).take count.toNat).copy

/-- Apply trailing instance arguments left unapplied after the explicit arguments. -/
private partial def applyTrailingInstances (e : Expr) : MetaM Expr := do
  let type ← whnf (← inferType e)
  match type with
  | .forallE _ domain _ binderInfo =>
    if binderInfo.isInstImplicit then
      applyTrailingInstances (mkApp e (← synthInstance domain))
    else
      return e
  | _ =>
    return e

/-- Build a fully applied Lean constant and reject ill-typed applications. -/
private def mkAppChecked? (name : Name) (args : Array Expr) : MetaM (Option Expr) := do
  try
    let e ← applyTrailingInstances (← mkAppM name args)
    let e ← instantiateMVars e
    let _ ← inferType e
    return some e
  catch _ =>
    return none

/-- Rebuild `String.contains` with the same canonical dependent searcher dictionaries
accepted by the string lowering. Lean cannot infer the searcher family from the two value
arguments alone when this application is assembled with `mkAppM`. -/
private def stringContains? (value pattern : Expr) : MetaM (Option Expr) := do
  try
    let searcher :=
      mkApp
        (mkConst ``String.Slice.Pattern.ForwardSliceSearcher.instToForwardSearcher_1)
        pattern
    let e := mkAppN (mkConst ``String.contains) #[
      mkConst ``String,
      mkConst ``String.Slice.Pattern.ForwardSliceSearcher,
      mkConst ``String.Slice.Pattern.ForwardSliceSearcher.instIteratorIdSearchStep,
      mkConst
        ``String.Slice.Pattern.ForwardSliceSearcher.instIteratorLoopIdSearchStep [.zero],
      value,
      pattern,
      searcher]
    let _ ← inferType e
    return some e
  catch _ =>
    return none

/-- SMT string concatenation is variadic. Fold it left so cvc5's flattened
`(str.++ a b c)` matches the binary Lean term `(a ++ b) ++ c`. -/
private def stringAppend? (args : Array Expr) : MetaM (Option Expr) := do
  if args.isEmpty then return some (Lean.toExpr "")
  let mut result := args[0]!
  for i in [1:args.size] do
    let some next ← mkAppChecked? ``HAppend.hAppend #[result, args[i]!]
      | return none
    result := next
  return some result

/-- Fold an n-ary arithmetic application using Lean's binary operation. -/
private def foldArithmetic? (op : Name) (args : Array Expr) (unit : Int) :
    MetaM (Option Expr) := do
  if args.isEmpty then return some (Lean.toExpr unit)
  let mut result := args[0]!
  for i in [1:args.size] do
    let some next ← mkAppChecked? op #[result, args[i]!]
      | return none
    result := next
  return some result

/-- Keep source-level `Nat` terms at `Nat` when cvc5 prints their nonnegative SMT
integer constants without type information. -/
private def alignNatNumerals (args : Array Expr) : MetaM (Array Expr) := do
  let types ← args.mapM fun arg => do whnf (← inferType arg)
  unless types.any (·.isConstOf ``Nat) do return args
  let mut aligned := #[]
  for (arg, type) in args.zip types do
    if type.isConstOf ``Int then
      let some value ← getIntValue? arg | return args
      if value < 0 then return args
      aligned := aligned.push (mkNatLit value.toNat)
    else
      aligned := aligned.push arg
  return aligned

/-- Integer absolute value used by cvc5's nonlinear-arithmetic certificates. -/
def intAbs (value : Int) : Int :=
  if value < 0 then -value else value

private def symbolValue (value : Expr) : MetaM Expr := do
  let type ← whnf (← inferType value)
  if type.isConstOf ``Nat then
    return mkApp (mkConst ``Int.ofNat) value
  return value

/-- Recover a source `Nat` argument from its SMT integer representation. -/
private def natArgument? (arg : Expr) : MetaM (Option Expr) := do
  let type ← whnf (← inferType arg)
  if type.isConstOf ``Nat then return some arg
  unless type.isConstOf ``Int do return none
  if arg.isAppOfArity ``Int.ofNat 1 then
    return some arg.getAppArgs[0]!
  if let some value ← getIntValue? arg then
    if value < 0 then return none
    return some (mkNatLit value.toNat)
  return some (mkApp (mkConst ``Int.toNat) arg)

/-- Recover a source `Bool` argument from an SMT formula. -/
private def boolArgument? (arg : Expr) : MetaM (Option Expr) := do
  let type ← whnf (← inferType arg)
  if type.isConstOf ``Bool then return some arg
  unless type.isProp do return none
  if arg.isConstOf ``True then return some (mkConst ``Bool.true)
  if arg.isConstOf ``False then return some (mkConst ``Bool.false)
  let decision := mkApp (mkConst ``Classical.propDecidable) arg
  return some (mkApp2 (mkConst ``decide) arg decision)

/-- Align SMT integer arguments with source-level `Nat` domains before applying a
recorded Lean function. -/
private partial def alignFunctionArgs (fn : Expr) (args : Array Expr) :
    MetaM (Option (Array Expr)) := do
  go (← inferType fn) 0 #[]
where
  go (type : Expr) (index : Nat) (aligned : Array Expr) :
      MetaM (Option (Array Expr)) := do
    if index == args.size then return some aligned
    match ← whnf type with
    | .forallE _ domain body .default =>
      let domain ← whnf domain
      let arg : Expr ←
        if domain.isConstOf ``Nat then do
          let candidate ← natArgument? args[index]!
          pure (candidate.getD args[index]!)
        else if domain.isConstOf ``Bool then do
          let candidate ← boolArgument? args[index]!
          pure (candidate.getD args[index]!)
        else
          pure args[index]!
      unless ← isDefEq domain (← inferType arg) do return none
      go (body.instantiate1 arg) (index + 1) (aligned.push arg)
    | .forallE _ domain body _ =>
      let implicit ← mkFreshExprMVar domain
      go (body.instantiate1 implicit) index aligned
    | _ => return none

/-- Coerce a term into a `Prop`, for a position where SMT expects a formula.

SMT-LIB has one `Bool` sort where Lean distinguishes `Bool` from `Prop`, so a `Bool`-sorted
operand must be lifted (`b` ↦ `b = true`) before it can sit under `Not`/`Or`/`And`.
Without this the kernel rejects `¬q` for `q : Bool` — sound, but a lost replay. -/
private def toProp (e : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType e)
  if ty.isProp then return e
  else if ty.isConstOf ``Bool then mkEq e (mkConst ``Bool.true)
  else return e

/-- Rebuild SMT's overloaded Boolean xor at either Lean's `Bool` or `Prop` level. -/
private def xor? (args : Array Expr) : MetaM (Option Expr) := do
  if args.isEmpty then return some (mkConst ``False)
  let argTypes ← args.mapM fun arg => do whnf (← inferType arg)
  if argTypes.all (·.isConstOf ``Bool) then
    let mut result := args[0]!
    for arg in args.extract 1 args.size do
      result ← mkAppM ``Bool.xor #[result, arg]
    return some result
  let props ← args.mapM toProp
  let mut result := props[0]!
  for prop in props.extract 1 props.size do
    result ← mkAppM ``Not #[← mkAppM ``Iff #[result, prop]]
  return some result

/-- Rebuild SMT's pairwise `distinct`. -/
private def distinct? (args : Array Expr) : MetaM (Option Expr) := do
  let mut inequalities := #[]
  for i in [:args.size] do
    for j in [i + 1:args.size] do
      let neq ← mkAppM ``Not #[← mkEq args[i]! args[j]!]
      inequalities := inequalities.push neq
  if inequalities.isEmpty then return some (mkConst ``True)
  let mut result := inequalities.back!
  for i in [1:inequalities.size] do
    result ← mkAppM ``And #[inequalities[inequalities.size - 1 - i]!, result]
  return some result

/-- Rebuild an SMT `ite`, lifting mixed Lean `Bool`/`Prop` branches to propositions. -/
private def ite? (condition thenBranch elseBranch : Expr) : MetaM (Option Expr) := do
  let condition ← toProp condition
  let thenType ← whnf (← inferType thenBranch)
  let elseType ← whnf (← inferType elseBranch)
  let (thenBranch, elseBranch) ←
    if thenType.isProp != elseType.isProp &&
        (thenType.isProp || thenType.isConstOf ``Bool) &&
        (elseType.isProp || elseType.isConstOf ``Bool) then
      pure (← toProp thenBranch, ← toProp elseBranch)
    else
      pure (thenBranch, elseBranch)
  mkAppChecked? ``ite #[condition, thenBranch, elseBranch]

/-- Rebuild a source-level bit-vector theory application. -/
private def bitVecApp? (head : String) (args : Array Expr) : MetaM (Option Expr) := do
  match head, args.size with
  | "bvadd", 2 => mkAppChecked? ``BitVec.add args
  | "bvsub", 2 => mkAppChecked? ``BitVec.sub args
  | "bvmul", 2 => mkAppChecked? ``BitVec.mul args
  | "bvand", 2 => mkAppChecked? ``BitVec.and args
  | "bvor", 2 => mkAppChecked? ``BitVec.or args
  | "bvxor", 2 => mkAppChecked? ``BitVec.xor args
  | "bvnot", 1 => mkAppChecked? ``BitVec.not args
  | "bvneg", 1 => mkAppChecked? ``BitVec.neg args
  | "bvudiv", 2 => mkAppChecked? ``BitVec.udiv args
  | "bvurem", 2 => mkAppChecked? ``BitVec.umod args
  | "bvsdiv", 2 => mkAppChecked? ``BitVec.sdiv args
  | "bvsrem", 2 => mkAppChecked? ``BitVec.srem args
  | "bvsmod", 2 => mkAppChecked? ``BitVec.smod args
  | "bvult", 2 => mkAppChecked? ``BitVec.ult args
  | "bvule", 2 => mkAppChecked? ``BitVec.ule args
  | "bvugt", 2 => mkAppChecked? ``BitVec.ult #[args[1]!, args[0]!]
  | "bvuge", 2 => mkAppChecked? ``BitVec.ule #[args[1]!, args[0]!]
  | "bvslt", 2 => mkAppChecked? ``BitVec.slt args
  | "bvsle", 2 => mkAppChecked? ``BitVec.sle args
  | "bvsgt", 2 => mkAppChecked? ``BitVec.slt #[args[1]!, args[0]!]
  | "bvsge", 2 => mkAppChecked? ``BitVec.sle #[args[1]!, args[0]!]
  | "bvshl", 2 =>
    let shift ← mkAppM ``BitVec.toNat #[args[1]!]
    mkAppChecked? ``BitVec.shiftLeft #[args[0]!, shift]
  | "bvlshr", 2 =>
    let shift ← mkAppM ``BitVec.toNat #[args[1]!]
    mkAppChecked? ``BitVec.ushiftRight #[args[0]!, shift]
  | "bvashr", 2 =>
    let shift ← mkAppM ``BitVec.toNat #[args[1]!]
    mkAppChecked? ``BitVec.sshiftRight #[args[0]!, shift]
  | "concat", 2 => mkAppChecked? ``BitVec.append args
  | "bv2nat", 1 | "ubv_to_int", 1 =>
    let value ← mkAppM ``BitVec.toNat args
    return some (mkApp (mkConst ``Int.ofNat) value)
  | "sbv_to_int", 1 => mkAppChecked? ``BitVec.toInt args
  | "rotate_left", 2 | "rotate_right", 2 =>
    let some amount ← indexValue? args[0]! | return none
    let operation :=
      if head == "rotate_left" then ``BitVec.rotateLeft else ``BitVec.rotateRight
    mkAppChecked? operation #[args[1]!, mkNatLit amount]
  | "extract", 3 =>
    let some high ← indexValue? args[0]! | return none
    let some low ← indexValue? args[1]! | return none
    mkAppChecked? ``BitVec.extractLsb #[mkNatLit high, mkNatLit low, args[2]!]
  | "zero_extend", 2 | "sign_extend", 2 =>
    let some amount ← indexValue? args[0]! | return none
    let some width ← bitVecWidth? args[1]! | return none
    let operation :=
      if head == "zero_extend" then ``BitVec.zeroExtend else ``BitVec.signExtend
    mkAppChecked? operation #[mkNatLit (width + amount), args[1]!]
  | "int2bv", 2 | "int_to_bv", 2 =>
    let some width ← indexValue? args[0]! | return none
    mkAppChecked? ``BitVec.ofInt #[mkNatLit width, args[1]!]
  | _, _ => return none

/-- Replace the concrete index in a cvc5 bit-blast expression by a marker. -/
private partial def normalizeBitPattern? (index : Nat) (term : Sexp) : Option Sexp := do
  let .list parts := term | failure
  if let some (Sexp.list ident) := parts[0]? then
    if ident.size == 3 && ident[0]? == some (.atom "_") &&
        ident[1]? == some (.atom "@bit_of") then
      let some (Sexp.atom actual) := ident[2]? | failure
      if actual.toNat? != some index || parts.size != 2 then failure
      return .list #[
        .list #[.atom "_", .atom "@bit_of", .atom "#"],
        parts[1]!]
  let some (Sexp.atom head) := parts[0]? | failure
  unless head == "xor" || head == "and" || head == "or" || head == "not" do
    failure
  let mut normalized := #[Sexp.atom head]
  for arg in parts.extract 1 parts.size do
    normalized := normalized.push (← normalizeBitPattern? index arg)
  return .list normalized

/-- Binary SMT-LIB theory operators, mapped to the Lean constant to apply. `=` and `=>` are
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

/-- The Lean type an SMT sort denotes, for a quantifier binder. Theory sorts are fixed; an
opaque sort (`declare-sort`) is looked up in the symbol map, where the translator recorded
the Lean type it came from. `none` declines the enclosing quantifier rather than guessing. -/
def sortToType? (ctx : TermCtx) : Sexp → MetaM (Option Expr)
  | .atom "Int"  => return some (mkConst ``Int)
  | .atom "Bool" => return some (mkConst ``Bool)
  | .atom "String" => return some (mkConst ``String)
  | .atom s => return ctx.symbols.get? s
  | .list parts => do
    if parts.size == 3 && parts[0]? == some (.atom "_") &&
        parts[1]? == some (.atom "BitVec") then
      match parts[2]? with
      | some (Sexp.atom width) => do
        let some width := width.toNat? | return none
        return some (mkApp (mkConst ``BitVec) (mkNatLit width))
      | _ => return none
    return none
  | .str _ => return none

/-- Translate an Alethe term to the Lean term it denotes, or `none` if any part of it
cannot be mapped. Operators are matched by their SMT-LIB names and rebuilt with the
standard instances, matching what the translator consumed on the way out. `fuel` bounds
recursion through `:named` indirection, which a malformed proof could otherwise cycle. -/
partial def toExpr? (ctx : TermCtx) (fuel : Nat) (s : Sexp) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  match s with
  | .str value => return some (Lean.toExpr value)
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
    else if let some e := ctx.symbols.get? a then return some (← symbolValue e)
    else if let some (width, value) := bitVecAtom? a then
      return some (mkBitVecLit width value)
    else if let some i := intLit? a then
      return some (Lean.toExpr i)
    else return none
  | .list xs =>
    if let some (Sexp.list ident) := xs[0]? then
      return ← indexedApp ident (xs.extract 1 xs.size)
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
    if head == "choice" then
      let some (Sexp.list binders) := args[0]? | return none
      let some body := args[1]? | return none
      let some (Sexp.list bind) := binders[0]? | return none
      if binders.size != 1 then return none
      let some (Sexp.atom vname) := bind[0]? | return none
      let some sortSexp := bind[1]? | return none
      let some ty ← sortToType? ctx sortSexp | return none
      return ← withLocalDeclD (Name.mkSimple vname) ty fun v => do
        let localCtx := { ctx with locals := ctx.locals.insert vname v }
        let some predicate ← toExpr? localCtx (fuel - 1) body | return none
        let predicate ← mkLambdaFVars #[v] (← toProp predicate)
        mkAppChecked? ``Classical.epsilon #[predicate]
    if head == "let" then
      let some (Sexp.list bindings) := args[0]? | return none
      let some body := args[1]? | return none
      let mut localCtx := ctx
      let mut values : Array (String × Expr) := #[]
      for binding in bindings do
        let Sexp.list pair := binding | return none
        let some (Sexp.atom name) := pair[0]? | return none
        let some value := pair[1]? | return none
        let some value ← toExpr? ctx (fuel - 1) value | return none
        values := values.push (name, value)
      for (name, value) in values do
        localCtx := { localCtx with locals := localCtx.locals.insert name value }
      return ← toExpr? localCtx (fuel - 1) body
    if head == "@bbterm" then
      return ← bitBlastTerm args
    if head == "@bv" && args.size == 2 then
      let some (Sexp.atom value) := args[0]? | return none
      let some (Sexp.atom width) := args[1]? | return none
      let some value := value.toNat? | return none
      let some width := width.toNat? | return none
      return some (mkBitVecLit width value)
    if head == "@bvsize" && args.size == 1 then
      let some value ← toExpr? ctx (fuel - 1) args[0]! | return none
      let some width ← bitVecWidth? value | return none
      return some (Lean.toExpr (Int.ofNat width))
    if head == "_" && args.size == 2 then
      let some (Sexp.atom valueName) := args[0]? | return none
      let some (Sexp.atom widthName) := args[1]? | return none
      unless valueName.startsWith "bv" do return none
      let some value := (valueName.drop 2).toString.toNat? | return none
      let some width := widthName.toNat? | return none
      return some (mkBitVecLit width value)
    -- Translate all arguments; any untranslatable argument fails the whole term.
    let mkArgs : MetaM (Option (Array Expr)) := do
      let mut out := #[]
      for a in args do
        let some e ← toExpr? ctx (fuel - 1) a | return none
        out := out.push e
      return some out
    let some as ← mkArgs | return none
    let as ← alignNatNumerals as
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
    | "-", _   =>
      if as.size < 2 then return none
      foldArithmetic? ``HSub.hSub as 0
    | "+", _ => foldArithmetic? ``HAdd.hAdd as 0
    | "*", _ => foldArithmetic? ``HMul.hMul as 1
    | "div", 2 => mkAppChecked? ``HDiv.hDiv as
    | "mod", 2 => mkAppChecked? ``HMod.hMod as
    | "abs", 1 => mkAppChecked? ``intAbs as
    | "int.pow2", 1 => do
      let some exponent ← getIntValue? as[0]! | return none
      if exponent < 0 then return none
      return some (Lean.toExpr (Int.ofNat (2 ^ exponent.toNat)))
    | "int.ispow2", 1 => do
      let some value ← getIntValue? as[0]! | return none
      if value ≤ 0 then return none
      let holds : Bool := decide value.toNat.isPowerOfTwo
      return some (mkConst (if holds then ``True else ``False))
    | "int.log2", 1 => do
      let some value ← getIntValue? as[0]! | return none
      if value ≤ 0 then return none
      return some (Lean.toExpr (Int.ofNat value.toNat.log2))
    | "xor", _ => xor? as
    | "distinct", _ => distinct? as
    | "ite", 3 => ite? as[0]! as[1]! as[2]!
    | "str.++", _ => stringAppend? as
    | "str.len", 1 => do
      let some length ← mkAppChecked? ``String.length as | return none
      return some (mkApp (mkConst ``Int.ofNat) length)
    | "str.prefixof", 2 => mkAppChecked? ``String.isPrefixOf as
    | "str.suffixof", 2 => mkAppChecked? ``String.endsWith #[as[1]!, as[0]!]
    | "str.contains", 2 => stringContains? as[0]! as[1]!
    | "str.substr", 3 => mkAppChecked? ``stringSubstr as
    | _, 2 =>
      match binOp? head with
      | some c => return some (← mkAppM c #[as[0]!, as[1]!])
      | none =>
        match ← bitVecApp? head as with
        | some result => return some result
        | none => extensionOrUninterp head #[] as
    | _, _ =>
      match ← bitVecApp? head as with
      | some result => return some result
      | none => extensionOrUninterp head #[] as
where
  /-- Translate indexed bit-vector operators used in cvc5 certificates. -/
  indexedApp (ident args : Array Sexp) : MetaM (Option Expr) := do
    unless ident[0]? == some (.atom "_") do return none
    let some (Sexp.atom head) := ident[1]? | return none
    let mut values := #[]
    for arg in args do
      let some value ← toExpr? ctx (fuel - 1) arg | return none
      values := values.push value
    let builtin ← match head, ident.size, values.size with
    | "@bit_of", 3, 1 =>
      let some (Sexp.atom index) := ident[2]? | return none
      let some index := index.toNat? | return none
      mkAppChecked? ``BitVec.getLsbD #[values[0]!, mkNatLit index]
    | "rotate_left", 3, 1 | "rotate_right", 3, 1 =>
      let some (Sexp.atom amount) := ident[2]? | return none
      let some amount := amount.toNat? | return none
      let operation :=
        if head == "rotate_left" then ``BitVec.rotateLeft else ``BitVec.rotateRight
      mkAppChecked? operation #[values[0]!, mkNatLit amount]
    | "extract", 4, 1 =>
      let some (Sexp.atom high) := ident[2]? | return none
      let some (Sexp.atom low) := ident[3]? | return none
      let some high := high.toNat? | return none
      let some low := low.toNat? | return none
      mkAppChecked? ``BitVec.extractLsb #[mkNatLit high, mkNatLit low, values[0]!]
    | "zero_extend", 3, 1 | "sign_extend", 3, 1 =>
      let some (Sexp.atom amount) := ident[2]? | return none
      let some amount := amount.toNat? | return none
      let some width ← bitVecWidth? values[0]! | return none
      let operation :=
        if head == "zero_extend" then ``BitVec.zeroExtend else ``BitVec.signExtend
      mkAppChecked? operation #[mkNatLit (width + amount), values[0]!]
    | "int2bv", 3, 1 | "int_to_bv", 3, 1 =>
      let some (Sexp.atom width) := ident[2]? | return none
      let some width := width.toNat? | return none
      mkAppChecked? ``BitVec.ofInt #[mkNatLit width, values[0]!]
    | _, _, _ => pure none
    if let some result := builtin then return some result
    runAletheDecoders ctx.decoders head (ident.extract 2 ident.size) values

  /-- Recover a bit-vector expression from cvc5's little-endian `@bbterm`. -/
  bitBlastTerm (args : Array Sexp) : MetaM (Option Expr) := do
    if args.isEmpty then return some (mkBitVecLit 0 0)
    let mut literal := 0
    let mut allLiteral := true
    for i in [:args.size] do
      match args[i]! with
      | .atom "true" => literal := literal + 2 ^ i
      | .atom "false" => pure ()
      | _ => allLiteral := false
    if allLiteral then return some (mkBitVecLit args.size literal)
    let patternResult ← (do
      let some first := expandNamed? ctx fuel args[0]! | return none
      let some pattern := normalizeBitPattern? 0 first | return none
      for i in [1:args.size] do
        let some arg := expandNamed? ctx fuel args[i]! | return none
        unless normalizeBitPattern? i arg == some pattern do return none
      let some result ← bitPatternExpr pattern | return none
      unless (← bitVecWidth? result) == some args.size do return none
      return some result)
    if let some result := patternResult then return some result
    let mut bits := #[]
    for arg in args do
      let some bit ← toExpr? ctx (fuel - 1) arg | return none
      let some bit ← boolArgument? bit | return none
      bits := bits.push bit
    let list ← mkListLit (mkConst ``Bool) bits.toList
    mkAppChecked? ``BitVec.ofBoolListLE #[list]

  /-- Translate a normalized bit pattern as a whole-vector operation. -/
  bitPatternExpr (pattern : Sexp) : MetaM (Option Expr) := do
    let .list parts := pattern | return none
    if let some (Sexp.list ident) := parts[0]? then
      if ident.size == 3 && ident[0]? == some (.atom "_") &&
          ident[1]? == some (.atom "@bit_of") && ident[2]? == some (.atom "#") &&
          parts.size == 2 then
        return ← toExpr? ctx (fuel - 1) parts[1]!
      return none
    let some (Sexp.atom head) := parts[0]? | return none
    let mut operands := #[]
    for arg in parts.extract 1 parts.size do
      let some operand ← bitPatternExpr arg | return none
      operands := operands.push operand
    let vectorHead :=
      match head with
      | "xor" => "bvxor"
      | "and" => "bvand"
      | "or" => "bvor"
      | "not" => "bvnot"
      | _ => head
    bitVecApp? vectorHead operands

  /-- An uninterpreted symbol applied to translated arguments: rebuild `head args…`.
  A mis-rebuilt (ill-typed) application is rejected rather than returned. -/
  uninterp (as : Array Expr) : MetaM (Option Expr) := do
    let .list xs := s | return none
    let some (Sexp.atom head) := xs[0]? | return none
    let some fn := ctx.symbols.get? head | return none
    try
      let some args ← alignFunctionArgs fn as | return none
      let e ← mkAppM' fn args
      let _ ← inferType e
      return some (← symbolValue e)
    catch _ => return none

  /-- Give user decoders first refusal over an otherwise unsupported operator,
  then try the emitted-symbol map used for ordinary uninterpreted functions. -/
  extensionOrUninterp (head : String) (indices : Array Sexp) (as : Array Expr) :
      MetaM (Option Expr) := do
    if let some result ← runAletheDecoders ctx.decoders head indices as then
      return some result
    uninterp as

/-- Decode the top-level literals of an Alethe clause without flattening Boolean `or`
terms that occur inside a literal. -/
def clauseLiteralsToExprs? (ctx : TermCtx) (fuel : Nat)
    (lits : Array Sexp) : MetaM (Option (Array Expr)) := do
  let mut out := #[]
  for l in lits do
    let some e ← toExpr? ctx fuel l | return none
    -- Clause literals are formulas; a `Bool`-sorted one must be lifted before it can be
    -- a disjunct (Lean's `Or` takes `Prop`s).
    out := out.push (← instantiateMVars (← toProp e))
  return some out

/-- A clause `(cl t₁ … tₙ)` as the Lean proposition it asserts: the disjunction of its
literals, and `False` for the empty clause. -/
def clauseToExpr? (ctx : TermCtx) (fuel : Nat) (lits : Array Sexp) : MetaM (Option Expr) := do
  let some out ← clauseLiteralsToExprs? ctx fuel lits | return none
  if out.isEmpty then return some (mkConst ``False)
  let mut e := out.back!
  for i in [1:out.size] do
    e ← mkAppM ``Or #[out[out.size - 1 - i]!, e]
  return some e

end Crush.Alethe
