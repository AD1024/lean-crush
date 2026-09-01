import Crush.SMT.Print

/-!
# SMT theory signatures

This module describes the syntax contributed by an SMT theory independently
of the command checker and the semantic metatheory. A signature records sort
constructors, literals, and ranked operator typing. Compatible signatures can
be combined without assigning different types to shared syntax.
-/

namespace Crush.SMT.Theory

/-- Result of checking one application of an operator present in a signature.
`none` as the successful result means that incomplete argument information did
not determine a result sort. -/
abbrev AppResult := Except String (Option SSort)

namespace AppResult

/-- Two application checks give the same typing judgment. Diagnostic text is
not part of the judgment, so two failures agree regardless of their messages. -/
def Agrees : AppResult → AppResult → Prop
  | .ok left, .ok right => left = right
  | .error _, .error _ => True
  | .ok _, .error _ | .error _, .ok _ => False

theorem agrees_refl (result : AppResult) : result.Agrees result := by
  cases result <;> trivial

theorem agrees_symm {left right : AppResult} :
    left.Agrees right → right.Agrees left := by
  cases left <;> cases right <;> simp_all [Agrees]

theorem agrees_trans {left middle right : AppResult} :
    left.Agrees middle → middle.Agrees right → left.Agrees right := by
  cases left <;> cases middle <;> cases right <;> simp_all [Agrees]

end AppResult

/-- Syntax and typing supplied by one SMT theory. `inferApp?` returns `none`
exactly when the identifier is absent; a present identifier returns either a
typing result or a diagnostic. -/
structure Sig where
  sortArity? : Ident → Option Nat
  containsIdent : Ident → Bool
  literalSort? : Literal → Option SSort
  inferApp? : Ident → Array (Option SSort) → Option AppResult
  inferApp_present : ∀ identifier arguments,
    (inferApp? identifier arguments).isSome = true →
      containsIdent identifier = true

namespace Sig

/-- Empty SMT signature. -/
def empty : Sig where
  sortArity? := fun _ => none
  containsIdent := fun _ => false
  literalSort? := fun _ => none
  inferApp? := fun _ _ => none
  inferApp_present := by simp

/-- Build a signature from arity-independent identifier membership and its
typing function. The wrapper makes `inferApp_present` hold by construction. -/
def ofClassifiers
    (sortArity? : Ident → Option Nat)
    (containsIdent : Ident → Bool)
    (literalSort? : Literal → Option SSort)
    (infer : Ident → Array (Option SSort) → AppResult) : Sig where
  sortArity?
  containsIdent
  literalSort?
  inferApp? := fun identifier arguments =>
    if containsIdent identifier then some (infer identifier arguments) else none
  inferApp_present := by
    intro identifier arguments present
    dsimp at present ⊢
    split at present
    · assumption
    · contradiction

/-- Whether a signature contains a literal. -/
def containsLiteral (sig : Sig) (literal : Literal) : Bool :=
  (sig.literalSort? literal).isSome

/-- Whether a signature contains a sort constructor. -/
def containsSortCtor (sig : Sig) (identifier : Ident) : Bool :=
  (sig.sortArity? identifier).isSome

mutual
  /-- Whether a complete sort is formed from constructors in the signature.
Bound sort variables belong to a surrounding declaration, not to a closed
signature. -/
  def containsSort (sig : Sig) : SSort → Bool
    | .bvar _ => false
    | .app identifier arguments =>
        match sig.sortArity? identifier with
        | some arity =>
            arguments.size == arity && sig.containsSortList arguments.toList
        | none => false
  termination_by sort => sort.structuralSize
  decreasing_by all_goals simp [SSort.structuralSize] <;> omega

  /-- Pointwise signature membership for a list of sorts. -/
  def containsSortList (sig : Sig) : List SSort → Bool
    | [] => true
    | sort :: sorts => sig.containsSort sort && sig.containsSortList sorts
  termination_by sorts => SSort.listStructuralSize sorts
  decreasing_by all_goals simp [SSort.listStructuralSize] <;> omega
end

@[simp] theorem containsSortList_nil (sig : Sig) :
    sig.containsSortList [] = true := by
  rw [containsSortList.eq_def]

@[simp] theorem containsSortList_cons (sig : Sig) (sort : SSort)
    (sorts : List SSort) :
    sig.containsSortList (sort :: sorts) =
      (sig.containsSort sort && sig.containsSortList sorts) := by
  rw [containsSortList.eq_def]

@[simp] theorem empty_containsSort (sort : SSort) :
    empty.containsSort sort = false := by
  cases sort <;> simp [empty, containsSort]

/-- Inclusion of one signature in another, preserving every shared typing
judgment. -/
structure Sub (small large : Sig) : Prop where
  sort : ∀ identifier arity,
    small.sortArity? identifier = some arity →
      large.sortArity? identifier = some arity
  ident : ∀ identifier,
    small.containsIdent identifier = true →
      large.containsIdent identifier = true
  literal : ∀ value sort,
    small.literalSort? value = some sort →
      large.literalSort? value = some sort
  app : ∀ identifier arguments result,
    small.inferApp? identifier arguments = some result →
      ∃ larger, large.inferApp? identifier arguments = some larger ∧
        result.Agrees larger

mutual
  /-- Signature inclusion preserves recursively formed sorts. -/
  theorem containsSort_mono {small large : Sig} (sub : small.Sub large) :
      ∀ sort, small.containsSort sort = true →
        large.containsSort sort = true
    | .bvar _ => by simp [containsSort]
    | .app identifier arguments => by
        intro present
        simp only [containsSort] at present ⊢
        split at present
        next arity smallArity =>
          have parts : (arguments.size == arity) = true ∧
              small.containsSortList arguments.toList = true := by
            simpa only [Bool.and_eq_true] using present
          rw [sub.sort identifier arity smallArity]
          simpa only [Bool.and_eq_true] using
            And.intro parts.1
              (containsSortList_mono sub arguments.toList parts.2)
        next absent => contradiction
  termination_by sort => sort.structuralSize
  decreasing_by all_goals simp [SSort.structuralSize] <;> omega

  /-- Signature inclusion preserves lists of recursively formed sorts. -/
  theorem containsSortList_mono {small large : Sig} (sub : small.Sub large) :
      ∀ sorts, small.containsSortList sorts = true →
        large.containsSortList sorts = true
    | [] => by
        intro present
        exact containsSortList_nil large
    | sort :: sorts => by
        intro present
        simp only [containsSortList] at present ⊢
        have parts : small.containsSort sort = true ∧
            small.containsSortList sorts = true := by
          simpa only [Bool.and_eq_true] using present
        simpa only [Bool.and_eq_true] using
          And.intro (containsSort_mono sub sort parts.1)
            (containsSortList_mono sub sorts parts.2)
  termination_by sorts => SSort.listStructuralSize sorts
  decreasing_by all_goals simp [SSort.listStructuralSize] <;> omega
end

/-- Two signatures agree wherever both contain the same syntax. -/
structure Compatible (left right : Sig) : Prop where
  sort : ∀ identifier leftArity rightArity,
    left.sortArity? identifier = some leftArity →
    right.sortArity? identifier = some rightArity →
      leftArity = rightArity
  literal : ∀ value leftSort rightSort,
    left.literalSort? value = some leftSort →
    right.literalSort? value = some rightSort →
      leftSort = rightSort
  app : ∀ identifier arguments leftResult rightResult,
    left.inferApp? identifier arguments = some leftResult →
    right.inferApp? identifier arguments = some rightResult →
      leftResult.Agrees rightResult

/-- Signature compatibility is symmetric. -/
theorem Compatible.symm {left right : Sig} (compatible : left.Compatible right) :
    right.Compatible left where
  sort := by
    intro identifier rightArity leftArity rightPresent leftPresent
    exact (compatible.sort identifier leftArity rightArity
      leftPresent rightPresent).symm
  literal := by
    intro value rightSort leftSort rightPresent leftPresent
    exact (compatible.literal value leftSort rightSort
      leftPresent rightPresent).symm
  app := by
    intro identifier arguments rightResult leftResult rightPresent leftPresent
    exact AppResult.agrees_symm
      (compatible.app identifier arguments leftResult rightResult
        leftPresent rightPresent)

/-- Least signature containing two compatible signatures. The compatibility
proof justifies the left choice on shared syntax. -/
def sum (left right : Sig) (_compatible : left.Compatible right) : Sig where
  sortArity? := fun identifier =>
    match left.sortArity? identifier with
    | some arity => some arity
    | none => right.sortArity? identifier
  containsIdent := fun identifier =>
    left.containsIdent identifier || right.containsIdent identifier
  literalSort? := fun literal =>
    match left.literalSort? literal with
    | some sort => some sort
    | none => right.literalSort? literal
  inferApp? := fun identifier arguments =>
    match left.inferApp? identifier arguments with
    | some result => some result
    | none => right.inferApp? identifier arguments
  inferApp_present := by
    intro identifier arguments present
    dsimp at present ⊢
    split at present
    next leftPresent =>
      have modeled := left.inferApp_present identifier arguments (by
        rw [leftPresent]
        rfl)
      simp [modeled]
    next leftAbsent =>
      have modeled := right.inferApp_present identifier arguments present
      simp [modeled]

/-- Every signature includes itself. -/
theorem sub_refl (sig : Sig) : sig.Sub sig where
  sort := by intros; assumption
  ident := by intros; assumption
  literal := by intros; assumption
  app := by
    intro identifier arguments result present
    exact ⟨result, present, AppResult.agrees_refl result⟩

/-- Signature inclusion is transitive. -/
theorem Sub.trans {small middle large : Sig}
    (lower : small.Sub middle) (upper : middle.Sub large) :
    small.Sub large where
  sort := by
    intro identifier arity present
    exact upper.sort identifier arity (lower.sort identifier arity present)
  ident := by
    intro identifier present
    exact upper.ident identifier (lower.ident identifier present)
  literal := by
    intro value sort present
    exact upper.literal value sort (lower.literal value sort present)
  app := by
    intro identifier arguments result present
    rcases lower.app identifier arguments result present with
      ⟨middleResult, middlePresent, lowerAgree⟩
    rcases upper.app identifier arguments middleResult middlePresent with
      ⟨largeResult, largePresent, upperAgree⟩
    exact ⟨largeResult, largePresent,
      AppResult.agrees_trans lowerAgree upperAgree⟩

/-- The left signature is included in a compatible signature sum. -/
theorem sub_sum_left (left right : Sig) (compatible : left.Compatible right) :
    left.Sub (left.sum right compatible) where
  sort := by
    intro identifier arity present
    simp [sum, present]
  ident := by
    intro identifier present
    simp [sum, present]
  literal := by
    intro value sort present
    simp [sum, present]
  app := by
    intro identifier arguments result present
    exact ⟨result, by simp [sum, present], AppResult.agrees_refl result⟩

/-- The right signature is included in a compatible signature sum. -/
theorem sub_sum_right (left right : Sig) (compatible : left.Compatible right) :
    right.Sub (left.sum right compatible) where
  sort := by
    intro identifier rightArity rightPresent
    simp only [sum]
    split
    next leftArity leftPresent =>
      have equal := compatible.sort identifier leftArity rightArity
        leftPresent rightPresent
      subst rightArity
      rfl
    next leftAbsent => exact rightPresent
  ident := by
    intro identifier present
    simp [sum, present]
  literal := by
    intro value rightSort rightPresent
    simp only [sum]
    split
    next leftSort leftPresent =>
      have equal := compatible.literal value leftSort rightSort
        leftPresent rightPresent
      subst rightSort
      rfl
    next leftAbsent => exact rightPresent
  app := by
    intro identifier arguments rightResult rightPresent
    simp only [sum]
    split
    next leftResult leftPresent =>
      exact ⟨leftResult, rfl,
        AppResult.agrees_symm
          (compatible.app identifier arguments leftResult rightResult
            leftPresent rightPresent)⟩
    next leftAbsent =>
      exact ⟨rightResult, rightPresent, AppResult.agrees_refl rightResult⟩

/-- Every signature is compatible with itself. -/
theorem compatible_refl (sig : Sig) : sig.Compatible sig where
  sort := by
    intro identifier left right leftPresent rightPresent
    exact Option.some.inj (leftPresent.symm.trans rightPresent)
  literal := by
    intro value left right leftPresent rightPresent
    exact Option.some.inj (leftPresent.symm.trans rightPresent)
  app := by
    intro identifier arguments left right leftPresent rightPresent
    have equal := Option.some.inj (leftPresent.symm.trans rightPresent)
    subst right
    cases left <;> trivial

end Sig

/-! ## Current checker signatures -/

def requireArity (name : String) (actual expected : Nat) :
    Except String Unit :=
  if actual == expected then pure ()
  else throw s!"`{name}` expects {expected} argument(s), got {actual}"

def requireSort (where_ : String) (actual : Option SSort)
    (expected : SSort) : Except String Unit :=
  match actual with
  | some actual =>
    if actual = expected then pure ()
    else throw s!"{where_} has sort `{actual}`, expected `{expected}`"
  | none => pure ()

def requireSame (where_ : String) (left right : Option SSort) :
    Except String Unit :=
  match left, right with
  | some left, some right =>
    if left = right then pure ()
    else throw s!"{where_} combines incompatible sorts `{left}` and `{right}`"
  | _, _ => pure ()

def requireArgsOfSort (name : String) (expected : SSort) :
    Nat → List (Option SSort) → Except String Unit
  | _, [] => pure ()
  | index, actual :: arguments => do
    requireSort s!"argument {index + 1} of `{name}`" actual expected
    requireArgsOfSort name expected (index + 1) arguments

def requireBoolArgs (name : String) (arguments : Array (Option SSort)) :
    Except String Unit :=
  requireArgsOfSort name boolSort 0 arguments.toList

def requireIntArgs (name : String) (arguments : Array (Option SSort)) :
    Except String Unit :=
  requireArgsOfSort name intSort 0 arguments.toList

def bvWidth? : SSort → Option Nat
  | .app (.indexed "BitVec" #[.inr width]) #[] => some width
  | _ => none

def requireBvArgs (name : String) (arguments : Array (Option SSort)) :
    Except String (Option Nat) := do
  let mut width : Option Nat := none
  for index in [0:arguments.size] do
    if let some sort := arguments[index]! then
      let some current := bvWidth? sort
        | throw s!"argument {index + 1} of `{name}` has non-bit-vector sort `{sort}`"
      match width with
      | none => width := some current
      | some expected =>
        unless current == expected do
          throw s!"`{name}` combines bit-vectors of widths {expected} and {current}"
  return width

/-- Core logical identifiers interpreted directly by term evaluation. -/
def coreContainsIdent : Ident → Bool
  | .symb name => #["=", "not", "=>", "and", "or"].contains name
  | .indexed _ _ => false

/-- Identifiers in the currently modeled integer fragment. -/
def intContainsIdent (identifier : Ident) : Bool :=
  decide (identifier = .symb ">=")

/-- All theory identifiers whose typing is known to the shared checker. -/
def knownContainsIdent : Ident → Bool
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

/-- Known identifiers whose semantics is outside the current metatheory. -/
def syntaxContainsIdent (identifier : Ident) : Bool :=
  knownContainsIdent identifier &&
    !(coreContainsIdent identifier || intContainsIdent identifier)

def inferCoreApp (identifier : Ident)
    (arguments : Array (Option SSort)) : AppResult := do
  let .symb name := identifier
    | throw s!"unknown core identifier `{identifier}`"
  match name with
  | "not" =>
    requireArity name arguments.size 1
    requireBoolArgs name arguments
    return some boolSort
  | "and" | "or" =>
    if arguments.isEmpty then
      throw s!"`{name}` expects at least one argument, got none"
    requireBoolArgs name arguments
    return some boolSort
  | "=>" =>
    requireArity name arguments.size 2
    requireBoolArgs name arguments
    return some boolSort
  | "=" =>
    requireArity name arguments.size 2
    requireSame s!"arguments of `{name}`" arguments[0]! arguments[1]!
    return some boolSort
  | _ => throw s!"unknown core identifier `{identifier}`"

def inferIntApp (identifier : Ident)
    (arguments : Array (Option SSort)) : AppResult := do
  let .symb name := identifier
    | throw s!"unknown integer identifier `{identifier}`"
  requireArity name arguments.size 2
  requireIntArgs name arguments
  return some boolSort

def inferSyntaxApp (identifier : Ident)
    (arguments : Array (Option SSort)) : AppResult := do
  match identifier with
  | .indexed "int2bv" #[.inr width] =>
    requireArity "int2bv" arguments.size 1
    requireSort "argument of `int2bv`" arguments[0]! intSort
    return some (.app (.indexed "BitVec" #[.inr width]) #[])
  | .indexed "extract" #[.inr high, .inr low] =>
    requireArity "extract" arguments.size 1
    if high < low then throw s!"invalid bit-vector extraction [{high}:{low}]"
    let _ ← requireBvArgs "extract" arguments
    return some (.app (.indexed "BitVec" #[.inr (high - low + 1)]) #[])
  | .indexed name #[.inr amount] =>
    if name == "zero_extend" || name == "sign_extend" then
      requireArity name arguments.size 1
      return (← requireBvArgs name arguments).map fun width =>
        .app (.indexed "BitVec" #[.inr (width + amount)]) #[]
    if name == "rotate_left" || name == "rotate_right" then
      requireArity name arguments.size 1
      return (← requireBvArgs name arguments).map fun width =>
        .app (.indexed "BitVec" #[.inr width]) #[]
    throw s!"unknown indexed theory identifier `{identifier}`"
  | .indexed _ _ =>
    throw s!"unknown indexed theory identifier `{identifier}`"
  | .symb name =>
    match name with
    | "true" | "false" =>
      requireArity name arguments.size 0
      return some boolSort
    | "xor" =>
      if arguments.isEmpty then
        throw s!"`{name}` expects at least one argument, got none"
      requireBoolArgs name arguments
      return some boolSort
    | "distinct" =>
      if arguments.size < 2 then
        throw s!"`distinct` expects at least two arguments, got {arguments.size}"
      for index in [1:arguments.size] do
        requireSame "arguments of `distinct`" arguments[0]! arguments[index]!
      return some boolSort
    | "ite" =>
      requireArity name arguments.size 3
      requireSort "condition of `ite`" arguments[0]! boolSort
      requireSame "branches of `ite`" arguments[1]! arguments[2]!
      return match arguments[1]! with
        | some sort => some sort
        | none => arguments[2]!
    | "+" | "*" =>
      requireArity name arguments.size 2
      requireIntArgs name arguments
      return some intSort
    | "-" =>
      unless arguments.size == 1 || arguments.size == 2 do
        throw s!"`-` expects one or two arguments, got {arguments.size}"
      requireIntArgs name arguments
      return some intSort
    | "div" | "mod" =>
      requireArity name arguments.size 2
      requireIntArgs name arguments
      return some intSort
    | "<" | "<=" | ">" =>
      requireArity name arguments.size 2
      requireIntArgs name arguments
      return some boolSort
    | "abs" =>
      requireArity name arguments.size 1
      requireIntArgs name arguments
      return some intSort
    | "bvnot" | "bvneg" =>
      requireArity name arguments.size 1
      return (← requireBvArgs name arguments).map fun width =>
        .app (.indexed "BitVec" #[.inr width]) #[]
    | "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor"
    | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod"
    | "bvshl" | "bvlshr" | "bvashr" =>
      requireArity name arguments.size 2
      return (← requireBvArgs name arguments).map fun width =>
        .app (.indexed "BitVec" #[.inr width]) #[]
    | "bvult" | "bvule" | "bvugt" | "bvuge"
    | "bvslt" | "bvsle" | "bvsgt" | "bvsge" =>
      requireArity name arguments.size 2
      let _ ← requireBvArgs name arguments
      return some boolSort
    | "concat" =>
      requireArity name arguments.size 2
      let left := arguments[0]!.bind bvWidth?
      let right := arguments[1]!.bind bvWidth?
      match left, right with
      | some left, some right =>
        return some (.app (.indexed "BitVec" #[.inr (left + right)]) #[])
      | some _, none | none, some _ =>
        throw "`concat` expects two bit-vector arguments"
      | none, none => return none
    | "bv2nat" | "sbv_to_int" =>
      requireArity name arguments.size 1
      let _ ← requireBvArgs name arguments
      return some intSort
    | "str.len" =>
      requireArity name arguments.size 1
      requireSort "argument of `str.len`" arguments[0]! stringSort
      return some intSort
    | "str.++" =>
      requireArity name arguments.size 2
      for argument in arguments do
        requireSort "argument of `str.++`" argument stringSort
      return some stringSort
    | "str.prefixof" | "str.suffixof" | "str.contains" =>
      requireArity name arguments.size 2
      for argument in arguments do
        requireSort s!"argument of `{name}`" argument stringSort
      return some boolSort
    | "select" =>
      requireArity name arguments.size 2
      match arguments[0]! with
      | some (.app (.symb "Array") #[key, value]) =>
        requireSort "index of `select`" arguments[1]! key
        return some value
      | some sort =>
        throw s!"first argument of `select` has non-array sort `{sort}`"
      | none => return none
    | "store" =>
      requireArity name arguments.size 3
      match arguments[0]! with
      | some array@(.app (.symb "Array") #[key, value]) =>
        requireSort "index of `store`" arguments[1]! key
        requireSort "value of `store`" arguments[2]! value
        return some array
      | some sort =>
        throw s!"first argument of `store` has non-array sort `{sort}`"
      | none => return none
    | _ => throw s!"unknown theory identifier `{identifier}`"

def coreSortArity? : Ident → Option Nat
  | .symb "Bool" => some 0
  | _ => none

def intSortArity? : Ident → Option Nat
  | identifier =>
    match coreSortArity? identifier with
    | some arity => some arity
    | none => if identifier = .symb "Int" then some 0 else none

def syntaxSortArity? : Ident → Option Nat
  | .symb "Bool" | .symb "Int" | .symb "String" => some 0
  | .symb "Array" => some 2
  | .indexed "BitVec" #[.inr _] => some 0
  | _ => none

/-- Signature of logical syntax interpreted directly by `Eval`. -/
def coreSig : Sig := Sig.ofClassifiers coreSortArity? coreContainsIdent
  (fun literal => match literal with
    | .bool _ => some boolSort
    | _ => none)
  inferCoreApp

/-- Signature of the integer fragment currently covered by the metatheory. -/
def intSig : Sig := Sig.ofClassifiers intSortArity? intContainsIdent
  (fun literal => match literal with
    | .num _ => some intSort
    | _ => none)
  inferIntApp

@[simp] theorem intSig_containsSort_bool :
    intSig.containsSort boolSort = true := by
  simp [intSig, intSortArity?, coreSortArity?, Sig.ofClassifiers,
    Sig.containsSort, boolSort]

@[simp] theorem intSig_containsSort_int :
    intSig.containsSort intSort = true := by
  simp [intSig, intSortArity?, coreSortArity?, Sig.ofClassifiers,
    Sig.containsSort, intSort]

@[simp] theorem intSig_containsLiteral_num (value : Nat) :
    intSig.containsLiteral (.num value) = true := rfl

/-- Signature used only to type known solver syntax whose semantics has not
yet been added to the metatheory. -/
def syntaxSig : Sig := Sig.ofClassifiers syntaxSortArity? syntaxContainsIdent
  (fun literal => match literal with
    | .str _ => some stringSort
    | .bitvec width _ => some (bitvecSort width)
    | _ => none)
  inferSyntaxApp

/-- One named interpreted-theory entry and its semantic dependencies. -/
structure Entry where
  key : Lean.Name
  deps : List Lean.Name
  sig : Sig

/-- Registry component selected to provide a checker typing rule. Provider
uniqueness is operational; compatible semantic signatures may overlap. -/
inductive Provider (modeledCount syntaxCount : Nat) where
  | core
  | modeled : Fin modeledCount → Provider modeledCount syntaxCount
  | syntaxOnly : Fin syntaxCount → Provider modeledCount syntaxCount
  deriving DecidableEq

/-- Finite syntax registry consumed by the checker. Semantic theory
declarations are attached to the modeled entries in the metatheory layer. -/
structure SigEnv where
  core : Sig
  modeled : List Entry
  syntaxOnly : List Sig
  sortProvider : Ident → Option (Provider modeled.length syntaxOnly.length)
  identProvider : Ident → Option (Provider modeled.length syntaxOnly.length)
  literalProvider : Literal → Option (Provider modeled.length syntaxOnly.length)
  depIds : (index : Fin modeled.length) → List (Fin modeled.length)

namespace SigEnv

/-- Signature selected by one checker provider. -/
def providerSig (env : SigEnv) :
    Provider env.modeled.length env.syntaxOnly.length → Sig
  | .core => env.core
  | .modeled index => (env.modeled.get index).sig
  | .syntaxOnly index => env.syntaxOnly.get index

/-- Whether a provider belongs to the semantically modeled fragment. -/
def providerIsModeled {modeledCount syntaxCount : Nat} :
    Provider modeledCount syntaxCount → Bool
  | .core | .modeled _ => true
  | .syntaxOnly _ => false

/-- Well-formed registry dispatch and dependency information. These laws make
provider selection a checked implementation of signature membership rather
than a second, potentially drifting classification. -/
structure WF (env : SigEnv) : Prop where
  sort_provider : ∀ identifier provider,
    env.sortProvider identifier = some provider →
      (env.providerSig provider).containsSortCtor identifier = true
  ident_provider : ∀ identifier provider,
    env.identProvider identifier = some provider →
      (env.providerSig provider).containsIdent identifier = true
  literal_provider : ∀ literal provider,
    env.literalProvider literal = some provider →
      (env.providerSig provider).containsLiteral literal = true
  core_compatible : ∀ index,
    env.core.Compatible (env.modeled.get index).sig
  modeled_compatible : ∀ left right,
    (env.modeled.get left).sig.Compatible (env.modeled.get right).sig
  deps_resolve : ∀ index dependency,
    dependency ∈ env.depIds index →
      (env.modeled.get dependency).key ∈ (env.modeled.get index).deps
  deps_before : ∀ index dependency,
    dependency ∈ env.depIds index → dependency.val < index.val

/-- Whether an identifier has a typing rule in the modeled fragment. -/
def isModeledIdent (env : SigEnv) (identifier : Ident) : Bool :=
  match env.identProvider identifier with
  | some (.core) | some (.modeled _) => true
  | _ => false

/-- Whether an identifier has any registered typing rule. -/
def isKnownIdent (env : SigEnv) (identifier : Ident) : Bool :=
  (env.identProvider identifier).isSome

/-- Whether a sort constructor is registered. -/
def isKnownSortCtor (env : SigEnv) (identifier : Ident) : Bool :=
  (env.sortProvider identifier).isSome

/-- Whether a sort constructor belongs to the modeled fragment. -/
def isModeledSortCtor (env : SigEnv) (identifier : Ident) : Bool :=
  match env.sortProvider identifier with
  | some provider => providerIsModeled provider
  | none => false

/-- Whether a literal belongs to the modeled fragment. -/
def isModeledLiteral (env : SigEnv) (literal : Literal) : Bool :=
  match env.literalProvider literal with
  | some provider => providerIsModeled provider
  | none => false

/-- Application typing supplied by the selected provider. -/
def inferApp? (env : SigEnv) (identifier : Ident)
    (arguments : Array (Option SSort)) : Option AppResult := do
  let provider ← env.identProvider identifier
  (env.providerSig provider).inferApp? identifier arguments

/-- Literal typing supplied by the selected provider. -/
def literalSort? (env : SigEnv) (literal : Literal) : Option SSort := do
  let provider ← env.literalProvider literal
  (env.providerSig provider).literalSort? literal

/-- Fixed sort-constructor arity supplied by the selected provider. -/
def sortArity? (env : SigEnv) (identifier : Ident) : Option Nat := do
  let provider ← env.sortProvider identifier
  (env.providerSig provider).sortArity? identifier

end SigEnv

/-! ## Registry for the currently checked fragment -/

private def intEntry : Entry where
  key := `Int
  deps := []
  sig := intSig

private def currentSortProvider (identifier : Ident) : Option (Provider 1 1) :=
  if coreSig.containsSortCtor identifier then some .core
  else if intSig.containsSortCtor identifier then some (.modeled ⟨0, by omega⟩)
  else if syntaxSig.containsSortCtor identifier then
    some (.syntaxOnly ⟨0, by omega⟩)
  else none

private def currentIdentProvider (identifier : Ident) : Option (Provider 1 1) :=
  if coreContainsIdent identifier then some .core
  else if intContainsIdent identifier then some (.modeled ⟨0, by omega⟩)
  else if syntaxContainsIdent identifier then some (.syntaxOnly ⟨0, by omega⟩)
  else none

private def currentLiteralProvider : Literal → Option (Provider 1 1)
  | .bool _ => some .core
  | .num _ => some (.modeled ⟨0, by omega⟩)
  | .str _ | .bitvec _ _ => some (.syntaxOnly ⟨0, by omega⟩)

/-- Theory registry matching the checker fragment before this refactor. The
logical core is mandatory, integer semantics is modeled, and the remaining
known solver syntax is available only to the open/closed syntax checker. -/
def currentEnv : SigEnv where
  core := coreSig
  modeled := [intEntry]
  syntaxOnly := [syntaxSig]
  sortProvider := currentSortProvider
  identProvider := currentIdentProvider
  literalProvider := currentLiteralProvider
  depIds := fun _ => []

/-- Integer entry of the current one-theory modeled registry. -/
def intId : Fin currentEnv.modeled.length := ⟨0, by decide⟩

private theorem core_not_int {identifier : Ident}
    (core : coreContainsIdent identifier = true) :
    intContainsIdent identifier = false := by
  cases integer : intContainsIdent identifier with
  | false => rfl
  | true =>
      have equal : identifier = .symb ">=" := of_decide_eq_true integer
      subst identifier
      simp [coreContainsIdent] at core

/-- A modeled identifier provider in the current registry is exactly the
integer comparison provider. -/
theorem current_identProvider_modeled_iff (identifier : Ident)
    (index : Fin currentEnv.modeled.length) :
    currentEnv.identProvider identifier = some (.modeled index) ↔
      intContainsIdent identifier = true := by
  change currentIdentProvider identifier = some (.modeled index) ↔ _
  unfold currentIdentProvider
  split
  next core => simp [core_not_int core]
  next notCore =>
    split
    next integer =>
      constructor
      · intro; exact integer
      · intro
        have indexEq : (⟨0, by omega⟩ : Fin 1) = index :=
          Subsingleton.elim _ _
        cases indexEq
        rfl
    next notInteger => simp [notInteger]

/-- A modeled sort provider in the current registry supplies exactly `Int`. -/
theorem current_sortProvider_modeled_iff (identifier : Ident)
    (index : Fin currentEnv.modeled.length) :
    currentEnv.sortProvider identifier = some (.modeled index) ↔
      identifier = .symb "Int" := by
  change currentSortProvider identifier = some (.modeled index) ↔ _
  unfold currentSortProvider
  split
  next core =>
    have notInt : identifier ≠ .symb "Int" := by
      intro equal
      subst identifier
      simp [coreSig, Sig.containsSortCtor, Sig.ofClassifiers,
        coreSortArity?] at core
    simp [notInt]
  next notCore =>
    split
    next integer =>
      have isInt : identifier = .symb "Int" := by
        have notCoreEq : coreSig.containsSortCtor identifier = false := by
          cases found : coreSig.containsSortCtor identifier
          · rfl
          · exact False.elim (notCore found)
        have coreAbsent : coreSortArity? identifier = none := by
          change (coreSortArity? identifier).isSome = false at notCoreEq
          cases found : coreSortArity? identifier <;>
            simp [found] at notCoreEq ⊢
        change (intSortArity? identifier).isSome = true at integer
        simp [intSortArity?, coreAbsent] at integer
        exact integer
      subst identifier
      constructor
      · intro; rfl
      · intro
        have indexEq : (⟨0, by omega⟩ : Fin 1) = index :=
          Subsingleton.elim _ _
        cases indexEq
        rfl
    next notInteger =>
      have notInt : identifier ≠ .symb "Int" := by
        intro equal
        subst identifier
        simp [intSig, Sig.containsSortCtor, Sig.ofClassifiers,
          intSortArity?, coreSortArity?] at notInteger
      simp [notInt]

/-- A modeled literal provider in the current registry supplies exactly
natural-number literals. -/
theorem current_literalProvider_modeled_iff (literal : Literal)
    (index : Fin currentEnv.modeled.length) :
    currentEnv.literalProvider literal = some (.modeled index) ↔
      ∃ value, literal = .num value := by
  cases literal with
  | num value =>
      constructor
      · intro; exact ⟨value, rfl⟩
      · intro
        have indexEq : (⟨0, by omega⟩ : Fin 1) = index :=
          Subsingleton.elim _ _
        change some (Provider.modeled (⟨0, by omega⟩ : Fin 1)) =
          some (Provider.modeled index)
        exact congrArg some (congrArg Provider.modeled indexEq)
  | str value | bitvec width value | bool value =>
      simp [currentEnv, currentLiteralProvider]

/-- Application typing in the current registry is the ordered dispatch to the
core, integer, and syntax-only signatures. -/
@[simp] theorem current_inferApp? (identifier : Ident)
    (arguments : Array (Option SSort)) :
    currentEnv.inferApp? identifier arguments =
      if coreContainsIdent identifier then
        some (inferCoreApp identifier arguments)
      else if intContainsIdent identifier then
        some (inferIntApp identifier arguments)
      else if syntaxContainsIdent identifier then
        some (inferSyntaxApp identifier arguments)
      else none := by
  cases core : coreContainsIdent identifier <;>
    cases integer : intContainsIdent identifier <;>
    cases knownSyntax : syntaxContainsIdent identifier <;>
    simp [SigEnv.inferApp?, currentEnv, currentIdentProvider,
      SigEnv.providerSig, coreSig, intSig, syntaxSig, intEntry,
      Sig.ofClassifiers, core, integer, knownSyntax]

/-- A sort constructor is registered exactly when one of the ordered
component signatures contains it. -/
@[simp] theorem current_isKnownSortCtor (identifier : Ident) :
    currentEnv.isKnownSortCtor identifier =
      (coreSig.containsSortCtor identifier ||
        intSig.containsSortCtor identifier ||
          syntaxSig.containsSortCtor identifier) := by
  cases core : coreSig.containsSortCtor identifier <;>
    cases integer : intSig.containsSortCtor identifier <;>
    cases knownSyntax : syntaxSig.containsSortCtor identifier <;>
    simp [SigEnv.isKnownSortCtor, currentEnv, currentSortProvider,
      core, integer, knownSyntax]

/-- Only core and integer sort constructors are admitted by the modeled
checker. -/
@[simp] theorem current_isModeledSortCtor (identifier : Ident) :
    currentEnv.isModeledSortCtor identifier =
      (coreSig.containsSortCtor identifier ||
        intSig.containsSortCtor identifier) := by
  cases core : coreSig.containsSortCtor identifier <;>
    cases integer : intSig.containsSortCtor identifier <;>
    cases knownSyntax : syntaxSig.containsSortCtor identifier <;>
    simp [SigEnv.isModeledSortCtor, SigEnv.providerIsModeled,
      currentEnv, currentSortProvider, core, integer, knownSyntax]

@[simp] theorem current_sortArity_bool :
    currentEnv.sortArity? (.symb "Bool") = some 0 := rfl

@[simp] theorem current_sortArity_int :
    currentEnv.sortArity? (.symb "Int") = some 0 := rfl

@[simp] theorem current_sortArity_string :
    currentEnv.sortArity? (.symb "String") = some 0 := rfl

@[simp] theorem current_sortArity_array :
    currentEnv.sortArity? (.symb "Array") = some 2 := rfl

@[simp] theorem current_sortArity_bitvec (width : Nat) :
    currentEnv.sortArity? (.indexed "BitVec" #[.inr width]) = some 0 := rfl

/-- Every literal class in the current SMT syntax has one registered sort. -/
@[simp] theorem current_literalSort? (literal : Literal) :
    currentEnv.literalSort? literal = some literal.sort := by
  cases literal <;> rfl

/-- Boolean and numeral literals are modeled; string and bit-vector literals
remain in the syntax-only tier. -/
@[simp] theorem current_isModeledLiteral : ∀ literal : Literal,
    currentEnv.isModeledLiteral literal =
      match literal with
      | .bool _ | .num _ => true
      | .str _ | .bitvec _ _ => false
  | .bool _ | .num _ | .str _ | .bitvec _ _ => by
      simp [SigEnv.isModeledLiteral, SigEnv.providerIsModeled,
        currentEnv, currentLiteralProvider]

private theorem core_int_compatible : coreSig.Compatible intSig where
  sort := by
    intro identifier left right leftPresent rightPresent
    change coreSortArity? identifier = some left at leftPresent
    change intSortArity? identifier = some right at rightPresent
    have equal : some left = some right := by
      simpa [intSortArity?, leftPresent] using rightPresent
    exact Option.some.inj equal
  literal := by
    intro value left right leftPresent rightPresent
    cases value <;>
      simp [coreSig, intSig, Sig.ofClassifiers] at leftPresent rightPresent
  app := by
    intro identifier arguments left right leftPresent rightPresent
    have corePresent := coreSig.inferApp_present identifier arguments (by
      rw [leftPresent]
      rfl)
    have intPresent := intSig.inferApp_present identifier arguments (by
      rw [rightPresent]
      rfl)
    have identifierEq : identifier = .symb ">=" :=
      of_decide_eq_true intPresent
    subst identifier
    simp [coreSig, Sig.ofClassifiers, coreContainsIdent] at corePresent

/-- The current registry has coherent providers, compatible modeled
signatures, and an empty integer dependency list. -/
theorem currentEnv_wf : currentEnv.WF where
  sort_provider := by
    intro identifier provider present
    simp only [currentEnv, currentSortProvider] at present
    split at present
    next core =>
      cases present
      exact core
    next notCore =>
      split at present
      next integer =>
        cases present
        exact integer
      next notInteger =>
        split at present
        next knownSyntax =>
          cases present
          exact knownSyntax
        next absent => contradiction
  ident_provider := by
    intro identifier provider present
    simp only [currentEnv, currentIdentProvider] at present
    split at present
    next core =>
      cases present
      exact core
    next notCore =>
      split at present
      next integer =>
        cases present
        exact integer
      next notInteger =>
        split at present
        next knownSyntax =>
          cases present
          exact knownSyntax
        next absent => contradiction
  literal_provider := by
    intro literal provider present
    cases literal <;> cases present <;> rfl
  core_compatible := by
    rintro ⟨index, bound⟩
    change index < 1 at bound
    have indexEq : index = 0 := by omega
    subst index
    exact core_int_compatible
  modeled_compatible := by
    rintro ⟨left, leftBound⟩ ⟨right, rightBound⟩
    change left < 1 at leftBound
    change right < 1 at rightBound
    have leftEq : left = 0 := by omega
    have rightEq : right = 0 := by omega
    subst left
    subst right
    exact Sig.compatible_refl intSig
  deps_resolve := by
    intro index dependency member
    change dependency ∈ [] at member
    contradiction
  deps_before := by
    intro index dependency member
    change dependency ∈ [] at member
    contradiction

/-- The registry's known-identifier classifier is the existing finite table. -/
private theorem core_known {identifier : Ident}
    (present : coreContainsIdent identifier = true) :
    knownContainsIdent identifier = true := by
  cases identifier with
  | indexed name indices => simp [coreContainsIdent] at present
  | symb name =>
      simp [coreContainsIdent, knownContainsIdent] at present ⊢
      grind

private theorem int_known {identifier : Ident}
    (present : intContainsIdent identifier = true) :
    knownContainsIdent identifier = true := by
  have equal : identifier = .symb ">=" := of_decide_eq_true present
  subst identifier
  simp [knownContainsIdent]

@[simp] theorem current_known_ident (identifier : Ident) :
    currentEnv.isKnownIdent identifier = knownContainsIdent identifier := by
  cases core : coreContainsIdent identifier <;>
    cases integer : intContainsIdent identifier <;>
    cases known : knownContainsIdent identifier <;>
    simp [SigEnv.isKnownIdent, currentEnv, currentIdentProvider,
      syntaxContainsIdent, core, integer, known] <;>
    grind [core_known, int_known]

/-- The modeled registry entries reproduce the current core-plus-`>=` table. -/
@[simp] theorem current_modeled_ident (identifier : Ident) :
    currentEnv.isModeledIdent identifier =
      (coreContainsIdent identifier || intContainsIdent identifier) := by
  cases core : coreContainsIdent identifier <;>
    cases integer : intContainsIdent identifier <;>
    cases knownSyntax : syntaxContainsIdent identifier <;>
    simp [SigEnv.isModeledIdent, currentEnv, currentIdentProvider,
      core, integer, knownSyntax]

end Crush.SMT.Theory
