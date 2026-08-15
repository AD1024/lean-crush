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

Unknown undeclared symbols are left unclassified rather than rejected. Translation
extensions may target additional SMT theories, so treating every symbol outside the
core table as an error would make the public lowering API artificially closed.
-/

namespace Crush.SMT

private def boolSort : SSort := .app (.symb "Bool") #[]
private def intSort : SSort := .app (.symb "Int") #[]
private def stringSort : SSort := .app (.symb "String") #[]

private structure FunSig where
  args : Array SSort
  res  : SSort

private structure SortAlias where
  arity : Nat
  body  : SSort

private structure CheckEnv where
  funs : Std.HashMap String FunSig := {}
  /-- `define-sort` aliases, expanded before sorts are compared. -/
  sorts : Std.HashMap String SortAlias := {}

/-- A malformed command found by `checkScript`. -/
structure SortError where
  commandIndex : Nat
  message      : String
  deriving Inhabited, Repr

instance : ToString SortError where
  toString e := s!"command {e.commandIndex}: {e.message}"

/-- Expand `define-sort` aliases so a sort and its expansion compare equal.

`fuel` bounds the walk; a script that defines a cyclic alias stops rather than looping. -/
private partial def expandSort (env : CheckEnv) (fuel : Nat) : SSort → SSort
  | .app id args =>
    let args := args.map (expandSort env fuel)
    match fuel, id with
    | fuel + 1, .symb name =>
      match env.sorts.get? name with
      | some alias =>
        if args.size == alias.arity then
          expandSort env fuel (instantiateSort alias.body args)
        else
          .app id args
      | none => .app id args
    | _, _ => .app id args
  | s => s
where
  instantiateSort (body : SSort) (args : Array SSort) : SSort :=
    match body with
    | .bvar i => args[i]?.getD body
    | .app id nested => .app id (nested.map (instantiateSort · args))

/-- Alias-expanding entry point for the fixed alias depth the checker allows. -/
private def resolveSort (env : CheckEnv) (s : SSort) : SSort :=
  expandSort env 32 s

private def arrowSig? : SSort → Option FunSig
  | .app (.symb "->") parts =>
    if parts.size < 2 then none
    else some { args := parts.extract 0 (parts.size - 1), res := parts.back! }
  | _ => none

private def bvWidth? : SSort → Option Nat
  | .app (.indexed "BitVec" #[.inr width]) #[] => some width
  | _ => none

private def lookupLocal (locals : List (String × SSort)) (name : String) : Option SSort :=
  (locals.find? fun entry => entry.1 == name).map (·.2)

private def requireArity (name : String) (actual expected : Nat) : Except String Unit :=
  if actual == expected then pure ()
  else throw s!"`{name}` expects {expected} argument(s), got {actual}"

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

private partial def inferTerm (env : CheckEnv) (locals : List (String × SSort))
    (bvars : List SSort) (term : Term) : Except String (Option SSort) := do
  match term with
  | .lit (.str value) =>
    validateStringLiteral value
    return some stringSort
  | .lit (.num _) => return some intSort
  | .lit (.bitvec width _) => return some (.app (.indexed "BitVec" #[.inr width]) #[])
  | .lit (.bool _) => return some boolSort
  | .bvar index =>
    match bvars[index]? with
    | some sort => return some sort
    | none => throw s!"unbound SMT de Bruijn variable `{index}`"
  | .app ident args =>
    let argSorts ← args.mapM (inferTerm env locals bvars)
    inferApp env locals ident argSorts
  | .letE bindings body =>
    let mut bindingSorts : Array (String × SSort) := #[]
    for (name, value) in bindings do
      if let some sort ← inferTerm env locals bvars value then
        bindingSorts := bindingSorts.push (name, sort)
    inferTerm env (bindingSorts.toList.reverse ++ locals) bvars body
  | .forallE binders body =>
    let binders := binders.map fun (n, s) => (n, resolveSort env s)
    let bodySort ← inferTerm env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    requireSort "body of `forall`" bodySort boolSort
    return some boolSort
  | .existsE binders body =>
    let binders := binders.map fun (n, s) => (n, resolveSort env s)
    let bodySort ← inferTerm env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    requireSort "body of `exists`" bodySort boolSort
    return some boolSort
  | .lam binders body =>
    let binders := binders.map fun (n, s) => (n, resolveSort env s)
    let bodySort ← inferTerm env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    return bodySort.map fun result =>
      .app (.symb "->") (binders.map (·.2) |>.push result)
  | .annot body attrs =>
    let sort ← inferTerm env locals bvars body
    for attr in attrs do
      if let .pattern terms := attr then
        for pattern in terms do
          let _ ← inferTerm env locals bvars pattern
    return sort
where
  inferApp (env : CheckEnv) (locals : List (String × SSort)) (ident : Ident)
      (args : Array (Option SSort)) : Except String (Option SSort) := do
    match ident with
    | .indexed "is" #[.inl ctor] =>
      requireArity s!"(_ is {ctor})" args.size 1
      if let some sig := env.funs.get? ctor then
        requireSort s!"argument of tester for `{ctor}`" args[0]! sig.res
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
      return none
    | .indexed _ _ => return none
    | .symb name =>
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
      | "=" | "distinct" =>
        requireArity name args.size 2
        requireSame s!"arguments of `{name}`" args[0]! args[1]!
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
      | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" =>
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
      | _ => return none

private def insertFun (env : CheckEnv) (name : String) (sig : FunSig) :
    Except String CheckEnv :=
  let sig : FunSig := { args := sig.args.map (resolveSort env), res := resolveSort env sig.res }
  match env.funs.get? name with
  | none => pure { env with funs := env.funs.insert name sig }
  | some previous =>
    if previous.args == sig.args && previous.res == sig.res then pure env
    else throw s!"symbol `{name}` is redeclared at incompatible signatures"

private def checkCommand (env : CheckEnv) (command : Command) : Except String CheckEnv := do
  match command with
  | .declFun name args res =>
    insertFun env name { args, res }
  | .defFun recursive name args res body =>
    let env ← if recursive then insertFun env name { args := args.map (·.2), res } else pure env
    let args := args.map fun (n, s) => (n, resolveSort env s)
    let res := resolveSort env res
    let bodySort ← inferTerm env args.toList.reverse (args.toList.reverse.map (·.2)) body
    requireSort s!"body of definition `{name}`" bodySort res
    if recursive then pure env else insertFun env name { args := args.map (·.2), res }
  | .defFunsRec defs =>
    let mut env := env
    for d in defs do
      env ← insertFun env d.name { args := d.args.map (·.2), res := d.resSort }
    for d in defs do
      let bodySort ←
        inferTerm env d.args.toList.reverse (d.args.toList.reverse.map (·.2)) d.body
      requireSort s!"body of recursive definition `{d.name}`" bodySort d.resSort
    return env
  | .declDatatypes datatypes =>
    let mut env := env
    -- Constructors must all be in scope before selectors of recursive datatypes
    -- are checked.
    for (sortName, _, datatype) in datatypes do
      let sort := SSort.app (.symb sortName) #[]
      for ctor in datatype.ctors do
        env ← insertFun env ctor.name { args := ctor.selDecls.map (·.2), res := sort }
    for (sortName, _, datatype) in datatypes do
      let sort := SSort.app (.symb sortName) #[]
      for ctor in datatype.ctors do
        for (selector, result) in ctor.selDecls do
          env ← insertFun env selector { args := #[sort], res := result }
    return env
  | .assert term =>
    let sort ← inferTerm env [] [] term
    requireSort "asserted term" sort boolSort
    return env
  | .echo value =>
    validateStringLiteral value
    return env
  | .defSort name params body =>
    return { env with sorts := env.sorts.insert name { arity := params.size, body } }
  | .setLogic _ | .setOption _ _ | .declSort _ _
  | .checkSat | .getModel | .getProof | .getUnsatCore | .exit =>
    return env

/-- Validate declaration applications and core-theory sorts in an SMT command
sequence. The returned command index points into the supplied array. -/
def checkScript (commands : Array Command) : Except SortError Unit := do
  let mut env : CheckEnv := {}
  for i in [0:commands.size] do
    match checkCommand env commands[i]! with
    | .ok next => env := next
    | .error message => throw { commandIndex := i, message }

end Crush.SMT
