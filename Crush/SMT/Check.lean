import Crush.SMT.Syntax
import Crush.SMT.Print

/-!
# SMT IR sort validation

A conservative sort checker for the SMT fragment emitted by `crush`.

`SMT.Term` is intentionally lightweight and does not carry a sort at every node.
That makes construction ergonomic, but previously let malformed applications reach
the backend, where they surfaced as solver-specific parser errors. This pass checks:

* every application of a declared function, constructor, or selector;
* the core Bool, Int, BitVec, String, and Array theory operators emitted by crush;
* binder, `let`, lambda, assertion, and definition result sorts.

The ordinary `checkScript` entry point leaves unknown undeclared symbols
unclassified. Translation extensions may target additional SMT theories, so treating
every symbol outside the core table as an error would make the public lowering API
artificially closed. `checkClosedScript` selects the stricter mode used by the
metatheory: every referenced symbol must instead be a known theory operator, a local
binder, or a preceding declaration.
-/

namespace Crush.SMT

/-- Solver-defined operators recognized by the shared SMT checker. An
identifier in this table cannot be redeclared as an uninterpreted function in
the closed metatheory fragment. -/
def isKnownTheoryOperator : Ident → Bool
  | .symb name =>
      #["true", "false", "=", "not", "=>", "and", "or", "xor",
        "distinct", "ite", "+", "*", "-", "div", "mod", "<", "<=",
        ">", ">=", "abs", "bvnot", "bvneg", "bvadd", "bvsub", "bvmul",
        "bvand", "bvor", "bvxor", "bvudiv", "bvurem", "bvsdiv",
        "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr", "bvult",
        "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt",
        "bvsge", "concat", "bv2nat", "sbv_to_int", "str.len", "str.++",
        "str.prefixof", "str.suffixof", "str.contains", "select", "store"]
        |>.contains name
  | .indexed name _ =>
      #["int2bv", "extract", "zero_extend", "sign_extend", "rotate_left",
        "rotate_right"] |>.contains name

/-- Theory operators whose denotation is present in `Metatheory.SMT.Semantics`.
Datatype constructors, selectors, and indexed testers are handled separately
by datatype declarations rather than this fixed table. -/
def isModeledTheoryOperator : Ident → Bool
  | .symb name =>
      #["=", "not", "=>", "and", "or", ">="] |>.contains name
  | .indexed _ _ => false

private structure CheckMode where
  rejectUnknown : Bool
  modeledTheoriesOnly : Bool

private structure FunSig where
  args : Array SSort
  res  : SSort

private structure CheckEnv where
  funs : Std.HashMap String FunSig := {}
  sorts : Std.HashMap String Nat := {}

/-- A malformed command found by `checkScript`. -/
structure SortError where
  commandIndex : Nat
  message      : String
  deriving DecidableEq, Inhabited, Repr

instance : ToString SortError where
  toString e := s!"command {e.commandIndex}: {e.message}"

private def arrowSig? : SSort → Option FunSig
  | .app (.symb "->") parts =>
    if parts.size < 2 then none
    else some { args := parts.extract 0 (parts.size - 1), res := parts.back! }
  | _ => none

private def bvWidth? : SSort → Option Nat
  | .app (.indexed "BitVec" #[.inr width]) #[] => some width
  | _ => none

private def requireArity (name : String) (actual expected : Nat) : Except String Unit :=
  if actual == expected then pure ()
  else throw s!"`{name}` expects {expected} argument(s), got {actual}"

private def builtinSortArity? : Ident → Option Nat
  | .symb "Bool" | .symb "Int" | .symb "String" => some 0
  | .symb "Array" => some 2
  | .symb "->" => none
  | .indexed "BitVec" #[.inr _] => some 0
  | _ => none

private partial def checkSort (mode : CheckMode) (env : CheckEnv)
    (sort : SSort) : Except String Unit := do
  match sort with
  | .bvar _ =>
      if mode.modeledTheoriesOnly then
        throw "sort variables are outside the modeled monomorphic SMT fragment"
  | .app identifier arguments =>
      for argument in arguments do
        checkSort mode env argument
      if identifier == .symb "->" then
        if mode.modeledTheoriesOnly then
          throw "function sorts are outside the modeled first-order SMT fragment"
        if arguments.size < 2 then
          throw "function sort expects at least one domain and one codomain"
        return
      if let some arity := builtinSortArity? identifier then
        requireArity s!"sort `{identifier}`" arguments.size arity
        return
      match identifier with
      | .symb name =>
          if let some arity := env.sorts.get? name then
            requireArity s!"sort `{name}`" arguments.size arity
          else if mode.rejectUnknown then
            throw s!"undeclared sort `{name}`"
      | .indexed _ _ =>
          if mode.rejectUnknown then
            throw s!"unknown indexed sort `{identifier}`"

private def insertSort (mode : CheckMode) (env : CheckEnv)
    (name : String) (arity : Nat) : Except String CheckEnv := do
  if (builtinSortArity? (.symb name)).isSome || name == "->" then
    throw s!"built-in sort `{name}` cannot be redeclared"
  if env.sorts.contains name then
    if mode.rejectUnknown then
      throw s!"sort `{name}` is declared more than once"
    else
      return env
  return { env with sorts := env.sorts.insert name arity }

private def lookupLocal (locals : List (String × SSort)) (name : String) : Option SSort :=
  (locals.find? fun entry => entry.1 == name).map (·.2)

private def requireSort (where_ : String) (actual : Option SSort) (expected : SSort) :
    Except String Unit :=
  match actual with
  | some actual =>
    if actual == expected then pure ()
    else throw s!"{where_} has sort `{actual}`, expected `{expected}`"
  | none => pure ()

private def requireSame (where_ : String) (a b : Option SSort) : Except String Unit :=
  match a, b with
  | some a, some b =>
    if a == b then pure ()
    else throw s!"{where_} combines incompatible sorts `{a}` and `{b}`"
  | _, _ => pure ()

private def requireBoolArgs (name : String) (args : Array (Option SSort)) :
    Except String Unit := do
  for i in [0:args.size] do
    requireSort s!"argument {i + 1} of `{name}`" args[i]! boolSort

private def requireIntArgs (name : String) (args : Array (Option SSort)) :
    Except String Unit := do
  for i in [0:args.size] do
    requireSort s!"argument {i + 1} of `{name}`" args[i]! intSort

private def requireBvArgs (name : String) (args : Array (Option SSort)) :
    Except String (Option Nat) := do
  let mut width : Option Nat := none
  for i in [0:args.size] do
    if let some sort := args[i]! then
      let some current := bvWidth? sort
        | throw s!"argument {i + 1} of `{name}` has non-bit-vector sort `{sort}`"
      match width with
      | none => width := some current
      | some expected =>
        unless current == expected do
          throw s!"`{name}` combines bit-vectors of widths {expected} and {current}"
  return width

private def validateStringLiteral (value : String) : Except String Unit := do
  for c in value.toList do
    if c.toNat > 0x2FFFF then
      throw s!"string literal contains Unicode codepoint U+{String.ofList
        (Nat.toDigits 16 c.toNat)} outside SMT-LIB 2.6's Unicode escape range"

private def checkSignature (name : String) (sig : FunSig)
    (args : Array (Option SSort)) : Except String Unit := do
  requireArity name args.size sig.args.size
  for i in [0:args.size] do
    requireSort s!"argument {i + 1} of `{name}`" args[i]! sig.args[i]!

private partial def inferTerm (mode : CheckMode) (env : CheckEnv)
    (locals : List (String × SSort))
    (bvars : List SSort) (term : Term) : Except String (Option SSort) := do
  match term with
  | .lit (.str value) =>
    if mode.modeledTheoriesOnly then
      throw "string literals are outside the modeled SMT fragment"
    validateStringLiteral value
    return some stringSort
  | .lit (.num _) => return some intSort
  | .lit (.bitvec width _) =>
    if mode.modeledTheoriesOnly then
      throw "bit-vector literals are outside the modeled SMT fragment"
    return some (.app (.indexed "BitVec" #[.inr width]) #[])
  | .lit (.bool _) => return some boolSort
  | .bvar index =>
    match bvars[index]? with
    | some sort => return some sort
    | none => throw s!"unbound SMT de Bruijn variable `{index}`"
  | .app ident args =>
    let argSorts ← args.mapM (inferTerm mode env locals bvars)
    inferApp mode env locals ident argSorts
  | .letE bindings body =>
    let mut bindingSorts : Array (String × SSort) := #[]
    for (name, value) in bindings do
      if let some sort ← inferTerm mode env locals bvars value then
        bindingSorts := bindingSorts.push (name, sort)
    inferTerm mode env (bindingSorts.toList.reverse ++ locals) bvars body
  | .forallE binders body =>
    for (_, sort) in binders do checkSort mode env sort
    let bodySort ← inferTerm mode env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    requireSort "body of `forall`" bodySort boolSort
    return some boolSort
  | .existsE binders body =>
    for (_, sort) in binders do checkSort mode env sort
    let bodySort ← inferTerm mode env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    requireSort "body of `exists`" bodySort boolSort
    return some boolSort
  | .lam binders body =>
    if mode.modeledTheoriesOnly then
      throw "lambda terms are outside the modeled first-order SMT fragment"
    for (_, sort) in binders do checkSort mode env sort
    let bodySort ← inferTerm mode env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    return bodySort.map fun result =>
      .app (.symb "->") (binders.map (·.2) |>.push result)
  | .annot body attrs =>
    let sort ← inferTerm mode env locals bvars body
    for attr in attrs do
      if let .pattern terms := attr then
        for pattern in terms do
          let _ ← inferTerm mode env locals bvars pattern
    return sort
where
  inferApp (mode : CheckMode) (env : CheckEnv)
      (locals : List (String × SSort)) (ident : Ident)
      (args : Array (Option SSort)) : Except String (Option SSort) := do
    match ident with
    | .indexed "is" #[.inl ctor] =>
      requireArity s!"(_ is {ctor})" args.size 1
      if let some sig := env.funs.get? ctor then
        requireSort s!"argument of tester for `{ctor}`" args[0]! sig.res
      else if mode.rejectUnknown then
        throw s!"tester references undeclared constructor `{ctor}`"
      return some boolSort
    | .indexed "int2bv" #[.inr width] =>
      requireArity "int2bv" args.size 1
      requireSort "argument of `int2bv`" args[0]! intSort
      return some (.app (.indexed "BitVec" #[.inr width]) #[])
    | .indexed "extract" #[.inr high, .inr low] =>
      requireArity "extract" args.size 1
      if high < low then throw s!"invalid bit-vector extraction [{high}:{low}]"
      let _ ← requireBvArgs "extract" args
      return some (.app (.indexed "BitVec" #[.inr (high - low + 1)]) #[])
    | .indexed op #[.inr amount] =>
      if op == "zero_extend" || op == "sign_extend" then
        requireArity op args.size 1
        return (← requireBvArgs op args).map fun width =>
          .app (.indexed "BitVec" #[.inr (width + amount)]) #[]
      if op == "rotate_left" || op == "rotate_right" then
        requireArity op args.size 1
        return (← requireBvArgs op args).map fun width =>
          .app (.indexed "BitVec" #[.inr width]) #[]
      if mode.modeledTheoriesOnly then
        throw s!"`{ident}` is outside the modeled SMT theory fragment"
      if mode.rejectUnknown then throw s!"unknown indexed symbol `{ident}`"
      return none
    | .indexed _ _ =>
      if mode.rejectUnknown then throw s!"unknown indexed symbol `{ident}`"
      return none
    | .symb name =>
      if mode.modeledTheoriesOnly && isKnownTheoryOperator ident &&
          !isModeledTheoryOperator ident then
        throw s!"`{name}` is outside the modeled SMT theory fragment"
      if let some localSort := lookupLocal locals name then
        if args.isEmpty then return some localSort
        let some sig := arrowSig? localSort
          | throw s!"local symbol `{name}` of sort `{localSort}` is not applicable"
        checkSignature name sig args
        return some sig.res
      if let some sig := env.funs.get? name then
        checkSignature name sig args
        return some sig.res
      match name with
      | "true" | "false" =>
        if mode.modeledTheoriesOnly then
          throw s!"`{name}` is outside the modeled SMT term fragment; use a Boolean literal"
        requireArity name args.size 0
        return some boolSort
      | "not" =>
        requireArity name args.size 1
        requireBoolArgs name args
        return some boolSort
      | "and" | "or" | "xor" =>
        if args.isEmpty then throw s!"`{name}` expects at least one argument, got none"
        requireBoolArgs name args
        return some boolSort
      | "=>" =>
        requireArity name args.size 2
        requireBoolArgs name args
        return some boolSort
      | "=" =>
        requireArity name args.size 2
        requireSame s!"arguments of `{name}`" args[0]! args[1]!
        return some boolSort
      | "distinct" =>
        if args.size < 2 then
          throw s!"`distinct` expects at least two arguments, got {args.size}"
        for i in [1:args.size] do
          requireSame "arguments of `distinct`" args[0]! args[i]!
        return some boolSort
      | "ite" =>
        requireArity name args.size 3
        requireSort "condition of `ite`" args[0]! boolSort
        requireSame "branches of `ite`" args[1]! args[2]!
        return match args[1]! with
          | some sort => some sort
          | none => args[2]!
      | "+" | "*" =>
        requireArity name args.size 2
        requireIntArgs name args
        return some intSort
      | "-" =>
        unless args.size == 1 || args.size == 2 do
          throw s!"`-` expects one or two arguments, got {args.size}"
        requireIntArgs name args
        return some intSort
      | "div" | "mod" =>
        requireArity name args.size 2
        requireIntArgs name args
        return some intSort
      | "<" | "<=" | ">" | ">=" =>
        requireArity name args.size 2
        requireIntArgs name args
        return some boolSort
      | "abs" =>
        requireArity name args.size 1
        requireIntArgs name args
        return some intSort
      | "bvnot" | "bvneg" =>
        requireArity name args.size 1
        return (← requireBvArgs name args).map fun width =>
          .app (.indexed "BitVec" #[.inr width]) #[]
      | "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor"
      | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod"
      | "bvshl" | "bvlshr" | "bvashr" =>
        requireArity name args.size 2
        return (← requireBvArgs name args).map fun width =>
          .app (.indexed "BitVec" #[.inr width]) #[]
      | "bvult" | "bvule" | "bvugt" | "bvuge"
      | "bvslt" | "bvsle" | "bvsgt" | "bvsge" =>
        requireArity name args.size 2
        let _ ← requireBvArgs name args
        return some boolSort
      | "concat" =>
        requireArity name args.size 2
        let left := args[0]!.bind bvWidth?
        let right := args[1]!.bind bvWidth?
        match left, right with
        | some left, some right =>
          return some (.app (.indexed "BitVec" #[.inr (left + right)]) #[])
        | some _, none | none, some _ =>
          throw "`concat` expects two bit-vector arguments"
        | none, none => return none
      | "bv2nat" | "sbv_to_int" =>
        requireArity name args.size 1
        let _ ← requireBvArgs name args
        return some intSort
      | "str.len" =>
        requireArity name args.size 1
        requireSort "argument of `str.len`" args[0]! stringSort
        return some intSort
      | "str.++" =>
        requireArity name args.size 2
        for arg in args do requireSort "argument of `str.++`" arg stringSort
        return some stringSort
      | "str.prefixof" | "str.suffixof" | "str.contains" =>
        requireArity name args.size 2
        for arg in args do requireSort s!"argument of `{name}`" arg stringSort
        return some boolSort
      | "select" =>
        requireArity name args.size 2
        match args[0]! with
        | some (.app (.symb "Array") #[key, value]) =>
          requireSort "index of `select`" args[1]! key
          return some value
        | some sort => throw s!"first argument of `select` has non-array sort `{sort}`"
        | none => return none
      | "store" =>
        requireArity name args.size 3
        match args[0]! with
        | some array@(.app (.symb "Array") #[key, value]) =>
          requireSort "index of `store`" args[1]! key
          requireSort "value of `store`" args[2]! value
          return some array
        | some sort => throw s!"first argument of `store` has non-array sort `{sort}`"
        | none => return none
      | _ =>
        if mode.rejectUnknown then throw s!"undeclared or unknown symbol `{name}`"
        return none

private def insertFun (mode : CheckMode) (env : CheckEnv) (name : String)
    (sig : FunSig) :
    Except String CheckEnv :=
  if mode.modeledTheoriesOnly && isKnownTheoryOperator (.symb name) then
    throw s!"theory operator `{name}` cannot be redeclared"
  else
  match env.funs.get? name with
  | none => pure { env with funs := env.funs.insert name sig }
  | some previous =>
    if mode.rejectUnknown then
      throw s!"symbol `{name}` is declared more than once"
    else if previous.args == sig.args && previous.res == sig.res then pure env
    else throw s!"symbol `{name}` is redeclared at incompatible signatures"

private def checkCommand (mode : CheckMode) (env : CheckEnv)
    (command : Command) : Except String CheckEnv := do
  match command with
  | .declSort name arity =>
    insertSort mode env name arity
  | .declFun name args res =>
    for sort in args do checkSort mode env sort
    checkSort mode env res
    insertFun mode env name { args, res }
  | .defFun definition =>
    for (_, sort) in definition.args do checkSort mode env sort
    checkSort mode env definition.resSort
    let bodySort ← inferTerm mode env definition.args.toList.reverse
      (definition.args.toList.reverse.map (·.2)) definition.body
    requireSort s!"body of definition `{definition.name}`" bodySort
      definition.resSort
    insertFun mode env definition.name {
      args := definition.args.map (·.2)
      res := definition.resSort }
  | .defFunsRec defs =>
    if mode.modeledTheoriesOnly && defs.isEmpty then
      throw "`define-funs-rec` requires at least one definition"
    let mut env := env
    for d in defs do
      for (_, sort) in d.args do checkSort mode env sort
      checkSort mode env d.resSort
      env ← insertFun mode env d.name { args := d.args.map (·.2), res := d.resSort }
    for d in defs do
      let bodySort ←
        inferTerm mode env d.args.toList.reverse
          (d.args.toList.reverse.map (·.2)) d.body
      requireSort s!"body of recursive definition `{d.name}`" bodySort d.resSort
    return env
  | .declDatatypes datatypes =>
    let mut env := env
    -- Mutually recursive datatype sorts enter scope together.
    for (sortName, arity, _) in datatypes do
      env ← insertSort mode env sortName arity
    -- Constructors must all be in scope before selectors of recursive datatypes
    -- are checked.
    for (sortName, _, datatype) in datatypes do
      let sort := SSort.app (.symb sortName) #[]
      for ctor in datatype.ctors do
        for (_, fieldSort) in ctor.selDecls do checkSort mode env fieldSort
        env ← insertFun mode env ctor.name { args := ctor.selDecls.map (·.2), res := sort }
    for (sortName, _, datatype) in datatypes do
      let sort := SSort.app (.symb sortName) #[]
      for ctor in datatype.ctors do
        for (selector, result) in ctor.selDecls do
          env ← insertFun mode env selector { args := #[sort], res := result }
    return env
  | .assert term =>
    let sort ← inferTerm mode env [] [] term
    requireSort "asserted term" sort boolSort
    return env
  | .echo value =>
    validateStringLiteral value
    return env
  | .setLogic _ | .setOption _ _
  | .checkSat | .getModel | .getProof | .getUnsatCore | .exit =>
    return env

/-- Validate declaration applications and core-theory sorts in an SMT command
sequence. The returned command index points into the supplied array. -/
private def checkScriptWith (mode : CheckMode)
    (commands : Array Command) : Except SortError Unit := do
  let mut env : CheckEnv := {}
  for i in [0:commands.size] do
    match checkCommand mode env commands[i]! with
    | .ok next => env := next
    | .error message => throw { commandIndex := i, message }

/-- Validate the open, extensible SMT IR used by the translator. Unknown theory
symbols remain unclassified so registered translation extensions can introduce
operators outside the built-in table. -/
def checkScript (commands : Array Command) : Except SortError Unit :=
  checkScriptWith { rejectUnknown := false, modeledTheoriesOnly := false } commands

/-- Validate a closed SMT script. Unlike `checkScript`, this rejects every
unknown or use-before-declaration symbol. The metatheory uses this judgment so
an invalid SMT script cannot establish unsatisfiability merely because its
untyped terms have incompatible sorts. -/
def checkClosedScript (commands : Array Command) : Except SortError Unit :=
  checkScriptWith { rejectUnknown := true, modeledTheoriesOnly := false } commands

/-- Computable success flag for `checkClosedScript`, used when a checked
translation must retain the validation result as proof data. -/
def closedScriptWellSorted (commands : Array Command) : Bool :=
  (checkClosedScript commands).isOk

/-- Type-check a closed command sequence in exactly the first-order theory
fragment whose denotation is mechanized by `Crush.Metatheory.SMT`. -/
def checkMetatheoryScript (commands : Array Command) : Except SortError Unit :=
  checkScriptWith { rejectUnknown := true, modeledTheoriesOnly := true } commands

/-- Computable success flag for `checkMetatheoryScript`. -/
def metatheoryScriptWellTyped (commands : Array Command) : Bool :=
  (checkMetatheoryScript commands).isOk

end Crush.SMT
