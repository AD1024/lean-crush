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

/- The metatheory retains successful checker runs as proof data. Recursive
sort and term checking is total, and the generated equation theorems let small
concrete successes be proved by kernel-checked simplification. -/

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

@[simp] private theorem builtinSortArity?_bool :
    Ident.builtinSortArity? (.symb "Bool") = some 0 := rfl

@[simp] private theorem builtinSortArity?_int :
    Ident.builtinSortArity? (.symb "Int") = some 0 := rfl

@[simp] private theorem builtinSortArity?_string :
    Ident.builtinSortArity? (.symb "String") = some 0 := rfl

private structure CheckMode where
  rejectUnknown : Bool
  modeledTheoriesOnly : Bool
  /-- Select the association-list mirror whose concrete evaluation can be
  checked by the kernel. Ordinary frontend checks use the hash-map fields. -/
  kernelReducible : Bool

private structure FunSig where
  args : Array SSort
  res  : SSort

/-- Kernel-reducible alternative to the frontend hash maps. The checker rejects
duplicate declarations before insertion, so association-list lookup has the
same result as hash-map lookup. The mode selects one representation, keeping
the frontend fast while allowing concrete metatheory certificates to reduce in
the kernel without evaluating opaque `String.hash`. -/
private abbrev NameMap (α : Type) := List (String × α)

@[simp]
private def NameMap.get? {α : Type} (entries : NameMap α) (name : String) : Option α :=
  (entries.find? fun entry => entry.1 == name).map (·.2)

@[simp]
private def NameMap.contains {α : Type} (entries : NameMap α) (name : String) : Bool :=
  (entries.get? name).isSome

@[simp]
private def NameMap.insert {α : Type} (entries : NameMap α) (name : String) (value : α) :
    NameMap α :=
  (name, value) :: entries

private structure CheckEnv where
  funs : Std.HashMap String FunSig := {}
  reducibleFuns : NameMap FunSig := []
  /-- Result sort of each datatype constructor introduced so far. Keeping this
  separate from `funs` prevents `(_ is f)` from treating an ordinary function
  as a datatype constructor. -/
  constructors : Std.HashMap String SSort := {}
  reducibleConstructors : NameMap SSort := []
  sorts : Std.HashMap String Nat := {}
  reducibleSorts : NameMap Nat := []

private def CheckEnv.fun? (mode : CheckMode) (env : CheckEnv)
    (name : String) : Option FunSig :=
  if mode.kernelReducible then env.reducibleFuns.get? name
  else env.funs.get? name

private def CheckEnv.constructor? (mode : CheckMode) (env : CheckEnv)
    (name : String) : Option SSort :=
  if mode.kernelReducible then env.reducibleConstructors.get? name
  else env.constructors.get? name

private def CheckEnv.sortArity? (mode : CheckMode) (env : CheckEnv)
    (name : String) : Option Nat :=
  if mode.kernelReducible then env.reducibleSorts.get? name
  else env.sorts.get? name

private def CheckEnv.containsSort (mode : CheckMode) (env : CheckEnv)
    (name : String) : Bool :=
  if mode.kernelReducible then env.reducibleSorts.contains name
  else env.sorts.contains name

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

mutual
  @[simp]
  private def checkSort (mode : CheckMode) (env : CheckEnv) :
      SSort → Except String Unit
    | .bvar _ => do
        if mode.modeledTheoriesOnly then
          throw "sort variables are outside the modeled monomorphic SMT fragment"
    | .app identifier arguments => do
        checkSortList mode env arguments.toList
        if identifier = .symb "->" then
          if mode.modeledTheoriesOnly then
            throw "function sorts are outside the modeled first-order SMT fragment"
          if arguments.size < 2 then
            throw "function sort expects at least one domain and one codomain"
          return
        if let some arity := identifier.builtinSortArity? then
          requireArity s!"sort `{identifier}`" arguments.size arity
          return
        match identifier with
        | .symb name =>
            if let some arity := env.sortArity? mode name then
              requireArity s!"sort `{name}`" arguments.size arity
            else if mode.rejectUnknown then
              throw s!"undeclared sort `{name}`"
        | .indexed _ _ =>
            if mode.rejectUnknown then
              throw s!"unknown indexed sort `{identifier}`"
  termination_by sort => sort.structuralSize
  decreasing_by all_goals simp [SSort.structuralSize] <;> omega

  @[simp]
  private def checkSortList (mode : CheckMode) (env : CheckEnv) :
      List SSort → Except String Unit
    | [] => pure ()
    | sort :: sorts => do
        checkSort mode env sort
        checkSortList mode env sorts
  termination_by sorts => SSort.listStructuralSize sorts
  decreasing_by all_goals simp [SSort.listStructuralSize] <;> omega
end

attribute [simp] checkSort.eq_1 checkSort.eq_2
  checkSortList.eq_1 checkSortList.eq_2

private def insertSort (mode : CheckMode) (env : CheckEnv)
    (name : String) (arity : Nat) : Except String CheckEnv := do
  if Ident.isBuiltinSort (.symb name) then
    throw s!"built-in sort `{name}` cannot be redeclared"
  if env.containsSort mode name then
    if mode.rejectUnknown then
      throw s!"sort `{name}` is declared more than once"
    else
      return env
  if mode.kernelReducible then
    return { env with reducibleSorts := env.reducibleSorts.insert name arity }
  else
    return { env with sorts := env.sorts.insert name arity }

private def lookupLocal (locals : List (String × SSort)) (name : String) : Option SSort :=
  (locals.find? fun entry => entry.1 == name).map (·.2)

@[reducible, simp]
private def requireSort (where_ : String) (actual : Option SSort) (expected : SSort) :
    Except String Unit :=
  match actual with
  | some actual =>
    if actual = expected then pure ()
    else throw s!"{where_} has sort `{actual}`, expected `{expected}`"
  | none => pure ()

private def requireSame (where_ : String) (a b : Option SSort) : Except String Unit :=
  match a, b with
  | some a, some b =>
    if a = b then pure ()
    else throw s!"{where_} combines incompatible sorts `{a}` and `{b}`"
  | _, _ => pure ()

@[simp]
private def requireArgsOfSort (name : String) (expected : SSort) :
    Nat → List (Option SSort) → Except String Unit
  | _, [] => pure ()
  | index, actual :: arguments => do
      requireSort s!"argument {index + 1} of `{name}`" actual expected
      requireArgsOfSort name expected (index + 1) arguments

private def requireBoolArgs (name : String) (args : Array (Option SSort)) :
    Except String Unit :=
  requireArgsOfSort name boolSort 0 args.toList

private def requireIntArgs (name : String) (args : Array (Option SSort)) :
    Except String Unit :=
  requireArgsOfSort name intSort 0 args.toList

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

mutual
  @[simp]
  private def inferTerm (mode : CheckMode) (env : CheckEnv)
      (locals : List (String × SSort)) (bvars : List SSort) :
      Term → Except String (Option SSort)
  | .lit (.str value) => do
    if mode.modeledTheoriesOnly then
      throw "string literals are outside the modeled SMT fragment"
    validateStringLiteral value
    return some stringSort
  | .lit (.num _) => do return some intSort
  | .lit (.bitvec width _) => do
    if mode.modeledTheoriesOnly then
      throw "bit-vector literals are outside the modeled SMT fragment"
    return some (.app (.indexed "BitVec" #[.inr width]) #[])
  | .lit (.bool _) => do return some boolSort
  | .bvar index => do
    match bvars[index]? with
    | some sort => return some sort
    | none => throw s!"unbound SMT de Bruijn variable `{index}`"
  | .app ident args => do
    let argSorts ← inferTermList mode env locals bvars args.toList
    inferApp mode env locals ident argSorts.toArray
  | .letE bindings body => do
    let bindingSorts ← inferBindingList mode env locals bvars bindings.toList
    inferTerm mode env (bindingSorts.reverse ++ locals) bvars body
  | .forallE binders body => do
    for (_, sort) in binders do checkSort mode env sort
    let bodySort ← inferTerm mode env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    requireSort "body of `forall`" bodySort boolSort
    return some boolSort
  | .existsE binders body => do
    for (_, sort) in binders do checkSort mode env sort
    let bodySort ← inferTerm mode env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    requireSort "body of `exists`" bodySort boolSort
    return some boolSort
  | .lam binders body => do
    if mode.modeledTheoriesOnly then
      throw "lambda terms are outside the modeled first-order SMT fragment"
    for (_, sort) in binders do checkSort mode env sort
    let bodySort ← inferTerm mode env (binders.toList.reverse ++ locals)
      (binders.toList.reverse.map (·.2) ++ bvars) body
    return bodySort.map fun result =>
      .app (.symb "->") (binders.map (·.2) |>.push result)
  | .annot body attrs => do
    let sort ← inferTerm mode env locals bvars body
    inferAttrList mode env locals bvars attrs.toList
    return sort
  termination_by term => Term.structuralSize term
  decreasing_by all_goals simp [Term.structuralSize] <;> omega
where
  inferApp (mode : CheckMode) (env : CheckEnv)
      (locals : List (String × SSort)) (ident : Ident)
      (args : Array (Option SSort)) : Except String (Option SSort) := do
    match ident with
    | .indexed "is" #[.inl ctor] =>
      requireArity s!"(_ is {ctor})" args.size 1
      if let some resultSort := env.constructor? mode ctor then
        requireSort s!"argument of tester for `{ctor}`" args[0]! resultSort
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
      if let some sig := env.fun? mode name then
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

  private def inferTermList (mode : CheckMode) (env : CheckEnv)
      (locals : List (String × SSort)) (bvars : List SSort) :
      List Term → Except String (List (Option SSort))
    | [] => pure []
    | term :: terms => do
        let sort ← inferTerm mode env locals bvars term
        let sorts ← inferTermList mode env locals bvars terms
        return sort :: sorts
  termination_by terms => Term.listStructuralSize terms
  decreasing_by all_goals simp [Term.listStructuralSize] <;> omega

  private def inferBindingList (mode : CheckMode) (env : CheckEnv)
      (locals : List (String × SSort)) (bvars : List SSort) :
      List (String × Term) → Except String (List (String × SSort))
    | [] => pure []
    | (name, value) :: bindings => do
        let sort ← inferTerm mode env locals bvars value
        let bindingSorts ← inferBindingList mode env locals bvars bindings
        return match sort with
          | some sort => (name, sort) :: bindingSorts
          | none => bindingSorts
  termination_by bindings => Term.bindingListStructuralSize bindings
  decreasing_by all_goals simp [Term.bindingListStructuralSize] <;> omega

  private def inferAttrList (mode : CheckMode) (env : CheckEnv)
      (locals : List (String × SSort)) (bvars : List SSort) :
      List Attr → Except String Unit
    | [] => pure ()
    | attr :: attrs => do
        match attr with
        | .pattern terms =>
            let _ ← inferTermList mode env locals bvars terms.toList
        | .named _ | .keyword _ _ => pure ()
        inferAttrList mode env locals bvars attrs
  termination_by attrs => Term.attrListStructuralSize attrs
  decreasing_by all_goals simp [Term.attrListStructuralSize,
    Term.attrStructuralSize] <;> omega
end

attribute [simp] inferTerm.eq_1 inferTerm.eq_2 inferTerm.eq_3 inferTerm.eq_4
  inferTerm.eq_5 inferTerm.eq_6 inferTerm.eq_7 inferTerm.eq_8 inferTerm.eq_9
  inferTerm.eq_10 inferTerm.eq_11 inferTermList.eq_1 inferTermList.eq_2
  inferBindingList.eq_1 inferBindingList.eq_2 inferAttrList.eq_1 inferAttrList.eq_2

private def insertFun (mode : CheckMode) (env : CheckEnv) (name : String)
    (sig : FunSig) :
    Except String CheckEnv :=
  if mode.modeledTheoriesOnly && isKnownTheoryOperator (.symb name) then
    throw s!"theory operator `{name}` cannot be redeclared"
  else
  match env.fun? mode name with
  | none =>
      if mode.kernelReducible then
        pure { env with reducibleFuns := env.reducibleFuns.insert name sig }
      else
        pure { env with funs := env.funs.insert name sig }
  | some previous =>
    if mode.rejectUnknown then
      throw s!"symbol `{name}` is declared more than once"
    else if previous.args = sig.args ∧ previous.res = sig.res then pure env
    else throw s!"symbol `{name}` is redeclared at incompatible signatures"

/-! ## Monomorphic datatype well-foundedness -/

/-- Nullary raw sort declared for one monomorphic datatype. -/
def datatypeSort (name : String) : SSort :=
  .app (.symb name) #[]

/-- Argument sorts of a raw datatype constructor. -/
def CtorDecl.argSorts (ctor : CtorDecl) : List SSort :=
  ctor.selDecls.toList.map (·.2)

/-- Constructor tester identifier generated by SMT-LIB. -/
def CtorDecl.tester (ctor : CtorDecl) : Ident :=
  .indexed "is" #[.inl ctor.name]

/-- Datatype sort/constructor pairs in command order. -/
def datatypeCtors
    (datatypes : Array (String × Nat × DatatypeDecl)) : List (SSort × CtorDecl) :=
  datatypes.toList.flatMap fun (name, _, datatype) =>
    datatype.ctors.toList.map fun ctor => (datatypeSort name, ctor)

/-- Sorts declared by one mutual datatype command. -/
def datatypeSorts
    (datatypes : Array (String × Nat × DatatypeDecl)) : List SSort :=
  datatypes.toList.map fun (name, _, _) => datatypeSort name

/-- Function identifiers declared by one datatype command. -/
def datatypeSymbols
    (datatypes : Array (String × Nat × DatatypeDecl)) : List Ident :=
  (datatypeCtors datatypes).flatMap fun (_, ctor) =>
    .symb ctor.name :: ctor.tester ::
      (ctor.selDecls.toList.map fun selector => .symb selector.1)

/-- Executable structural check for the modeled monomorphic datatype subset.
The semantic predicate below is defined by this exact Boolean result, so the
script validator and the UNSAT boundary cannot drift apart. -/
def datatypesStructurallyWellFormed
    (datatypes : Array (String × Nat × DatatypeDecl)) : Bool :=
  !datatypes.isEmpty &&
  decide (datatypes.toList.map (fun (name, _, _) => name)).Nodup &&
  decide (datatypeSymbols datatypes).Nodup &&
  datatypes.all fun (_, arity, datatype) =>
    arity == 0 && datatype.params.isEmpty && !datatype.ctors.isEmpty

/-- Names of the sorts introduced together by one `declare-datatypes`
command. -/
@[reducible]
def declaredDatatypeNames
    (datatypes : Array (String × Nat × DatatypeDecl)) : Array String :=
  datatypes.map (·.1)

/-- Recognize a direct reference to one of the nullary datatype sorts declared
by the current mutual block. -/
@[reducible]
def directDatatypeReference?
    (names : Array String) : SSort → Option String
  | .app (.symb name) arguments =>
      if arguments.isEmpty && names.contains name then some name else none
  | _ => none

/- Whether a sort contains a datatype sort declared by the current mutual
block. The list helper makes recursion through compound sort arguments
structurally explicit. -/
mutual
  @[reducible] def sortContainsDeclaredDatatype
      (names : Array String) : SSort → Bool
    | .bvar _ => false
    | .app (.symb name) arguments =>
        names.contains name ||
          sortListContainsDeclaredDatatype names arguments.toList
    | .app (.indexed _ _) arguments =>
        sortListContainsDeclaredDatatype names arguments.toList
  termination_by sort => sort.structuralSize
  decreasing_by
    all_goals simp [SSort.structuralSize] <;> omega

  @[reducible] def sortListContainsDeclaredDatatype
      (names : Array String) : List SSort → Bool
    | [] => false
    | sort :: sorts =>
        sortContainsDeclaredDatatype names sort ||
          sortListContainsDeclaredDatatype names sorts
  termination_by sorts => SSort.listStructuralSize sorts
  decreasing_by
    all_goals simp [SSort.listStructuralSize] <;> omega
end

/-- An external datatype field may use any complete sort that does not contain
one of the sorts declared by the same mutual block. Sort variables are rejected
by the surrounding monomorphic sort checker. -/
@[reducible]
def admissibleExternalDatatypeFieldSort (names : Array String) : SSort → Bool
  | .bvar _ => false
  | sort => !sortContainsDeclaredDatatype names sort

/-- Search, with a height bound, for one finite constructor tree of the named
datatype. External fields need no recursive witness because every SMT sort is
nonempty. Direct references to the current block recurse with smaller fuel.
Occurrences nested under another sort constructor are rejected explicitly. -/
@[reducible]
def datatypeHasFiniteValue
    (datatypes : Array (String × Nat × DatatypeDecl)) :
    Nat → String → Bool
  | 0, _ => false
  | fuel + 1, name =>
      match datatypes.find? fun entry => entry.1 == name with
      | none => false
      | some (_, _, datatype) =>
          let names := declaredDatatypeNames datatypes
          datatype.ctors.any fun ctor =>
            ctor.selDecls.all fun (_, fieldSort) =>
              match directDatatypeReference? names fieldSort with
              | some child => datatypeHasFiniteValue datatypes fuel child
              | none => admissibleExternalDatatypeFieldSort names fieldSort

/-- Executable SMT-LIB well-foundedness check for a monomorphic mutual
datatype declaration. Every declared sort must have a finite constructor tree.
For a block of `n` sorts, a shortest acyclic dependency witness has height at
most `n`, so the block size is sufficient fuel. -/
@[reducible]
def datatypesProductive
    (datatypes : Array (String × Nat × DatatypeDecl)) : Bool :=
  datatypes.all fun (name, _, _) =>
    datatypeHasFiniteValue datatypes datatypes.size name

@[reducible, simp]
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
    if mode.modeledTheoriesOnly && !datatypesStructurallyWellFormed datatypes then
      throw "datatype block is outside the modeled monomorphic structural fragment"
    if mode.modeledTheoriesOnly && !datatypesProductive datatypes then
      throw "datatype block has no finite constructor value for one or more sorts"
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
        env := if mode.kernelReducible then
          { env with reducibleConstructors :=
              env.reducibleConstructors.insert ctor.name sort }
        else
          { env with constructors := env.constructors.insert ctor.name sort }
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

/-- Structurally validate commands in order while retaining their array index
for diagnostics. This recursor is exact: unlike a fuel-bounded evaluator, it
visits every command once and cannot reject a large script because a bound was
chosen too small. -/
@[simp]
private def checkCommandList (mode : CheckMode) (index : Nat) (env : CheckEnv) :
    List Command → Except SortError Unit
  | [] => pure ()
  | command :: commands =>
      match checkCommand mode env command with
      | .ok next => checkCommandList mode (index + 1) next commands
      | .error message => throw { commandIndex := index, message }

/-- Validate declaration applications and core-theory sorts in an SMT command
sequence. The returned command index points into the supplied array. -/
private def checkScriptWith (mode : CheckMode)
    (commands : Array Command) : Except SortError Unit :=
  checkCommandList mode 0 {} commands.toList

/-- Validate the open, extensible SMT IR used by the translator. Unknown theory
symbols remain unclassified so registered translation extensions can introduce
operators outside the built-in table. -/
def checkScript (commands : Array Command) : Except SortError Unit :=
  checkScriptWith ⟨false, false, false⟩ commands

/-- Validate a closed SMT script. Unlike `checkScript`, this rejects every
unknown or use-before-declaration symbol. The metatheory uses this judgment so
an invalid SMT script cannot establish unsatisfiability merely because its
untyped terms have incompatible sorts. -/
def checkClosedScript (commands : Array Command) : Except SortError Unit :=
  checkScriptWith ⟨true, false, false⟩ commands

/-- Computable success flag for `checkClosedScript`, used when a checked
translation must retain the validation result as proof data. -/
def closedScriptWellSorted (commands : Array Command) : Bool :=
  (checkClosedScript commands).isOk

/-- Type-check a closed command sequence in exactly the first-order theory
fragment whose denotation is mechanized by `Crush.Metatheory.SMT`. -/
def checkMetatheoryScript (commands : Array Command) : Except SortError Unit :=
  checkScriptWith ⟨true, true, true⟩ commands

/-- Computable success flag for `checkMetatheoryScript`. -/
def metatheoryScriptWellTyped (commands : Array Command) : Bool :=
  (checkMetatheoryScript commands).isOk

/-- Normalize a concrete modeled-fragment checker run into a kernel-checked
equality proof. The tactic unfolds the total structural recursors above; it
does not invoke compiled evaluation or add a native-decision axiom. -/
macro "prove_metatheory_script_well_typed" : tactic =>
  `(tactic| simp [metatheoryScriptWellTyped, checkMetatheoryScript,
      checkScriptWith, checkCommand, checkSort, checkSortList,
      checkCommandList, NameMap.get?, NameMap.contains, NameMap.insert,
      CheckEnv.fun?, CheckEnv.constructor?, CheckEnv.sortArity?,
      CheckEnv.containsSort,
      inferTerm, inferTermList, inferBindingList, inferAttrList,
      inferTerm.eq_1, inferTerm.eq_2, inferTerm.eq_3, inferTerm.eq_4,
      inferTerm.eq_5, inferTerm.eq_6, inferTerm.eq_7, inferTerm.eq_8,
      inferTerm.eq_9, inferTerm.eq_10, inferTerm.eq_11,
      inferTermList.eq_1, inferTermList.eq_2,
      inferBindingList.eq_1, inferBindingList.eq_2,
      inferAttrList.eq_1, inferAttrList.eq_2,
      inferTerm.inferApp, insertSort, insertFun, requireSort, requireSame,
      requireArgsOfSort, requireBoolArgs, requireIntArgs, requireBvArgs, checkSignature,
      arrowSig?, requireArity, lookupLocal,
      validateStringLiteral, isKnownTheoryOperator, isModeledTheoryOperator,
      boolSort, intSort, stringSort, bitvecSort,
      Pure.pure, Bind.bind, Functor.map, Except.pure, Except.bind, Except.map,
      Term.symbApp] <;> rfl)

/-- Kernel-checked regression for the smallest unsatisfiable script. -/
theorem metatheoryScriptWellTyped_assertFalse :
    metatheoryScriptWellTyped #[.assert (.lit (.bool false))] = true := by
  prove_metatheory_script_well_typed

/-- Kernel-checked regression for a well-typed integer equality. -/
theorem metatheoryScriptWellTyped_distinctNumerals : metatheoryScriptWellTyped
    #[.assert (.symbApp "=" #[.lit (.num 0), .lit (.num 1)])] = true := by
  prove_metatheory_script_well_typed

/-- Kernel-checked regression that exercises declaration insertion and a
subsequent lookup in nonempty checker state. -/
theorem metatheoryScriptWellTyped_declaredBooleanConstant :
    metatheoryScriptWellTyped #[
      .declFun "p" #[] boolSort,
      .assert (.symbApp "p" #[])] = true := by
  prove_metatheory_script_well_typed

end Crush.SMT
