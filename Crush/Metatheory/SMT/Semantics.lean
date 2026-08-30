import Crush.SMT.Syntax

/-!
# Semantics of the verified SMT fragment

The production SMT syntax is intentionally untyped.  Its semantics is therefore
relational: a model supplies one universe of values, sort membership, literal
interpretations, and a graph for user symbols.  The evaluation relation gives
the built-in Boolean connectives, equality, quantifiers, and simultaneous lets
their standard meaning.

Only the command forms needed by the proved representation path are classified
as supported. Native datatypes have their free-algebra semantics, and
`define-funs-rec` has a simultaneous typed graph-equation semantics for the
production datatype guards. Nonrecursive definitions and lambdas remain outside
the command fragment instead of receiving a vacuous semantics.
-/

namespace Crush.SMT

/-- Sort assigned to a literal by the supported fragment. -/
def Literal.sort : Literal → SSort
  | .bool _ => boolSort
  | .num _ => intSort
  | .str _ => stringSort
  | .bitvec width _ => bitvecSort width

/-- A relational first-order SMT model.  `apply` is the graph of user symbols;
the evaluation relation below interprets logical built-ins directly. -/
structure Model where
  Value : Type
  inSort : SSort → Value → Prop
  sortNonempty : ∀ sort, ∃ value, inSort sort value
  bool : Bool → Value
  boolTyped : ∀ value, inSort boolSort (bool value)
  boolInjective : Function.Injective bool
  literal : Literal → Value
  literalTyped : ∀ lit, inSort (Literal.sort lit) (literal lit)
  apply : Ident → List Value → Value → Prop

/-- A list of semantic values has the listed SMT sorts in the same order. -/
inductive ValuesTyped (model : Model) : List SSort → List model.Value → Prop where
  | nil : ValuesTyped model [] []
  | cons {sort : SSort} {sorts : List SSort} {value : model.Value}
      {values : List model.Value} :
      model.inSort sort value → ValuesTyped model sorts values →
        ValuesTyped model (sort :: sorts) (value :: values)

namespace ValuesTyped

/-- An empty sort telescope types only the empty value list. -/
theorem eq_nil {model : Model} {values : List model.Value}
    (typed : ValuesTyped model [] values) : values = [] := by
  cases typed
  rfl

/-- Invert one typed value-list constructor. -/
theorem exists_cons {model : Model} {sort : SSort} {sorts : List SSort}
    {values : List model.Value}
    (typed : ValuesTyped model (sort :: sorts) values) :
    ∃ value rest, values = value :: rest ∧ model.inSort sort value ∧
      ValuesTyped model sorts rest := by
  cases typed
  exact ⟨_, _, rfl, by assumption, by assumption⟩

end ValuesTyped

/-- Values selected for a binder telescope, in binder declaration order. -/
abbrev Bindings := ValuesTyped

/-- A user symbol graph is total, single-valued, and sort-correct at one
declaration. -/
def SymbolHasType (model : Model) (symbol : Ident)
    (arguments : List SSort) (result : SSort) : Prop :=
  ∀ values, ValuesTyped model arguments values →
    ∃ output, model.inSort result output ∧
      model.apply symbol values output ∧
      ∀ other, model.apply symbol values other → other = output

/-- Every application graph at a fixed identifier and argument list has at
most one output. The induced models below satisfy this globally, including
their fresh derived-symbol extensions. -/
def ApplyUnique (model : Model) : Prop :=
  ∀ symbol values left right,
    model.apply symbol values left → model.apply symbol values right →
      left = right

/-- Semantic values are the images of the listed Boolean values. -/
inductive BoolValues (model : Model) : List model.Value → List Bool → Prop where
  | nil : BoolValues model [] []
  | cons {value : Bool} {values : List model.Value} {booleans : List Bool} :
      BoolValues model values booleans →
        BoolValues model (model.bool value :: values) (value :: booleans)

theorem BoolValues.eq_map {model : Model} {values : List model.Value}
    {booleans : List Bool} (typed : BoolValues model values booleans) :
    values = booleans.map model.bool := by
  induction typed with
  | nil => rfl
  | cons tail ih => simp [ih]

private theorem map_inj {alpha beta : Type} {image : alpha → beta}
    (injective : Function.Injective image) : ∀ {left right : List alpha},
      left.map image = right.map image → left = right := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons head tail => simp at equal
  | cons head tail ih =>
      intro right equal
      cases right with
      | nil => simp at equal
      | cons other rest =>
        simp only [List.map_cons, List.cons.injEq] at equal
        have headEq := injective equal.1
        subst other
        exact congrArg (head :: ·) (ih equal.2)

/-- Boolean-value evidence determines its Boolean list uniquely. -/
theorem BoolValues.unique {model : Model} {values : List model.Value}
    {left right : List Bool} (leftValues : BoolValues model values left)
    (rightValues : BoolValues model values right) : left = right := by
  apply map_inj model.boolInjective
  exact leftValues.eq_map.symm.trans rightValues.eq_map

@[simp] theorem Model.bool_eq_iff (model : Model) (left right : Bool) :
    model.bool left = model.bool right ↔ left = right :=
  ⟨fun equal => model.boolInjective equal, congrArg model.bool⟩

/-- Logical built-ins are interpreted by dedicated `Eval` constructors rather
than the arbitrary user-symbol graph. -/
inductive NotBuiltin : Ident → Prop where
  | indexed (name : String) (indices : Array (String ⊕ Nat)) :
      NotBuiltin (.indexed name indices)
  | symb (name : String) :
      name ≠ "=" → name ≠ "not" → name ≠ "=>" →
      name ≠ "and" → name ≠ "or" → NotBuiltin (.symb name)

instance (identifier : Ident) : Decidable (NotBuiltin identifier) :=
  match identifier with
  | .indexed name indices => isTrue (.indexed name indices)
  | .symb name =>
      decidable_of_iff
        (name ≠ "=" ∧ name ≠ "not" ∧ name ≠ "=>" ∧
          name ≠ "and" ∧ name ≠ "or")
        ⟨fun properties =>
            .symb name properties.1 properties.2.1 properties.2.2.1
              properties.2.2.2.1 properties.2.2.2.2,
          fun fresh => by
            cases fresh with
            | symb _ equal not implication conjunction disjunction =>
                exact ⟨equal, not, implication, conjunction, disjunction⟩⟩

private theorem NotBuiltin.ne_eq {symbol : Ident} (fresh : NotBuiltin symbol) :
    symbol ≠ .symb "=" := by
  intro equal
  subst symbol
  cases fresh with
  | symb _ different _ _ _ _ => exact different rfl

private theorem NotBuiltin.ne_not {symbol : Ident} (fresh : NotBuiltin symbol) :
    symbol ≠ .symb "not" := by
  intro equal
  subst symbol
  cases fresh with
  | symb _ _ different _ _ _ => exact different rfl

private theorem NotBuiltin.ne_imp {symbol : Ident} (fresh : NotBuiltin symbol) :
    symbol ≠ .symb "=>" := by
  intro equal
  subst symbol
  cases fresh with
  | symb _ _ _ different _ _ => exact different rfl

private theorem NotBuiltin.ne_and {symbol : Ident} (fresh : NotBuiltin symbol) :
    symbol ≠ .symb "and" := by
  intro equal
  subst symbol
  cases fresh with
  | symb _ _ _ _ different _ => exact different rfl

private theorem NotBuiltin.ne_or {symbol : Ident} (fresh : NotBuiltin symbol) :
    symbol ≠ .symb "or" := by
  intro equal
  subst symbol
  cases fresh with
  | symb _ _ _ _ _ different => exact different rfl

mutual
  /-- Relational evaluation of a concrete SMT term under a de Bruijn
  environment, with the nearest binder at list position zero. -/
  inductive Eval (model : Model) : List model.Value → Term → model.Value → Prop where
    | boolLit {environment : List model.Value} (value : Bool) :
        Eval model environment (.lit (.bool value)) (model.bool value)
    | literal {environment : List model.Value} (literal : Literal)
        (notBool : ∀ value, literal ≠ .bool value) :
        Eval model environment (.lit literal) (model.literal literal)
    | bvar {environment : List model.Value} {index : Nat} {value : model.Value} :
        environment[index]? = some value → Eval model environment (.bvar index) value
    | symbol {environment : List model.Value} {symbol : Ident}
        {arguments : Array Term} {values : List model.Value} {value : model.Value} :
        NotBuiltin symbol → EvalList model environment arguments.toList values →
        model.apply symbol values value → Eval model environment (.app symbol arguments) value
    | eqTrue {environment : List model.Value} {left right : Term}
        {leftValue rightValue : model.Value} :
        Eval model environment left leftValue → Eval model environment right rightValue →
        leftValue = rightValue →
          Eval model environment (.symbApp "=" #[left, right]) (model.bool true)
    | eqFalse {environment : List model.Value} {left right : Term}
        {leftValue rightValue : model.Value} :
        Eval model environment left leftValue → Eval model environment right rightValue →
        leftValue ≠ rightValue →
          Eval model environment (.symbApp "=" #[left, right]) (model.bool false)
    | not {environment : List model.Value} {body : Term} {value : Bool} :
        Eval model environment body (model.bool value) →
          Eval model environment (.symbApp "not" #[body]) (model.bool (!value))
    | imp {environment : List model.Value} {left right : Term}
        {leftValue rightValue : Bool} :
        Eval model environment left (model.bool leftValue) →
        Eval model environment right (model.bool rightValue) →
          Eval model environment (.symbApp "=>" #[left, right])
            (model.bool (!leftValue || rightValue))
    | and {environment : List model.Value} {arguments : Array Term}
        {values : List model.Value} {booleans : List Bool} :
        EvalList model environment arguments.toList values →
        BoolValues model values booleans →
          Eval model environment (.symbApp "and" arguments)
            (model.bool (booleans.all id))
    | or {environment : List model.Value} {arguments : Array Term}
        {values : List model.Value} {booleans : List Bool} :
        EvalList model environment arguments.toList values →
        BoolValues model values booleans →
          Eval model environment (.symbApp "or" arguments)
            (model.bool (booleans.any id))
    | letE {environment : List model.Value}
        {bindings : Array (String × Term)} {body : Term}
        {values : List model.Value} {value : model.Value} :
        EvalList model environment (bindings.toList.map (·.2)) values →
        Eval model (values.reverse ++ environment) body value →
          Eval model environment (.letE bindings body) value
    | forallTrue {environment : List model.Value}
        {binders : Array (String × SSort)} {body : Term} :
        (∀ values, Bindings model (binders.toList.map (·.2)) values →
          Eval model (values.reverse ++ environment) body (model.bool true)) →
        Eval model environment (.forallE binders body) (model.bool true)
    | forallFalse {environment : List model.Value}
        {binders : Array (String × SSort)} {body : Term}
        {values : List model.Value} :
        Bindings model (binders.toList.map (·.2)) values →
        Eval model (values.reverse ++ environment) body (model.bool false) →
          Eval model environment (.forallE binders body) (model.bool false)
    | existsTrue {environment : List model.Value}
        {binders : Array (String × SSort)} {body : Term}
        {values : List model.Value} :
        Bindings model (binders.toList.map (·.2)) values →
        Eval model (values.reverse ++ environment) body (model.bool true) →
          Eval model environment (.existsE binders body) (model.bool true)
    | existsFalse {environment : List model.Value}
        {binders : Array (String × SSort)} {body : Term} :
        (∀ values, Bindings model (binders.toList.map (·.2)) values →
          Eval model (values.reverse ++ environment) body (model.bool false)) →
        Eval model environment (.existsE binders body) (model.bool false)
    | annot {environment : List model.Value} {term : Term}
        {attributes : Array Attr} {value : model.Value} :
        Eval model environment term value → Eval model environment (.annot term attributes) value

  /-- Pointwise evaluation of a list of argument terms. -/
  inductive EvalList (model : Model) :
      List model.Value → List Term → List model.Value → Prop where
    | nil {environment : List model.Value} : EvalList model environment [] []
    | cons {environment : List model.Value} {term : Term} {terms : List Term} {value : model.Value}
        {values : List model.Value} :
        Eval model environment term value → EvalList model environment terms values →
          EvalList model environment (term :: terms) (value :: values)
end

/-- Raw evaluation is deterministic whenever the model's user-symbol graph is
single-valued. The proof covers the complete supported term semantics,
including Boolean connectives, lets, and quantifiers. -/
theorem Eval.unique {model : Model} (functional : ApplyUnique model)
    {environment : List model.Value} {term : Term} {left right : model.Value}
    (leftEval : Eval model environment term left)
    (rightEval : Eval model environment term right) : left = right := by
  have boolInj : Function.Injective model.bool := model.boolInjective
  exact Eval.rec
    (motive_1 := fun environment term value _ =>
      ∀ other, Eval model environment term other → value = other)
    (motive_2 := fun environment terms values _ =>
      ∀ others, EvalList model environment terms others → values = others)
    (boolLit := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (literal := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (bvar := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (symbol := by
      intros
      rename_i environment symbol arguments values value fresh argsEval applied
        argsIH other evaluated
      generalize termEq : Term.app symbol arguments = candidate at evaluated
      cases evaluated <;>
        simp_all [Term.symbApp, ApplyUnique] <;>
        grind [NotBuiltin.ne_eq, NotBuiltin.ne_not, NotBuiltin.ne_imp,
          NotBuiltin.ne_and, NotBuiltin.ne_or])
    (eqTrue := by
      intros
      rename_i environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval equal leftIH rightIH other evaluated
      generalize termEq : Term.symbApp "=" #[leftTerm, rightTerm] = candidate
        at evaluated
      cases evaluated <;> simp_all [Term.symbApp] <;>
        try { rename_i fresh; cases fresh <;> contradiction } <;>
        grind [BoolValues.unique, NotBuiltin.ne_eq])
    (eqFalse := by
      intros
      rename_i environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval unequal leftIH rightIH other evaluated
      generalize termEq : Term.symbApp "=" #[leftTerm, rightTerm] = candidate
        at evaluated
      cases evaluated <;> simp_all [Term.symbApp] <;>
        try { rename_i fresh; cases fresh <;> contradiction } <;>
        grind [BoolValues.unique, NotBuiltin.ne_eq])
    (not := by
      intros
      rename_i environment body value bodyEval bodyIH other evaluated
      generalize termEq : Term.symbApp "not" #[body] = candidate at evaluated
      cases evaluated <;> simp_all [Term.symbApp] <;>
        try { rename_i fresh; cases fresh <;> contradiction } <;>
        grind [BoolValues.unique, NotBuiltin.ne_not])
    (imp := by
      intros
      rename_i environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval leftIH rightIH other evaluated
      generalize termEq : Term.symbApp "=>" #[leftTerm, rightTerm] = candidate
        at evaluated
      cases evaluated <;> simp_all [Term.symbApp] <;>
        try { rename_i fresh; cases fresh <;> contradiction } <;>
        grind [BoolValues.unique, NotBuiltin.ne_imp])
    (and := by
      intros
      rename_i environment arguments values booleans argsEval boolValues argsIH
        other evaluated
      generalize termEq : Term.symbApp "and" arguments = candidate at evaluated
      cases evaluated <;> simp_all [Term.symbApp] <;>
        try { rename_i fresh; cases fresh <;> contradiction } <;>
        grind [BoolValues.unique, NotBuiltin.ne_and])
    (or := by
      intros
      rename_i environment arguments values booleans argsEval boolValues argsIH
        other evaluated
      generalize termEq : Term.symbApp "or" arguments = candidate at evaluated
      cases evaluated <;> simp_all [Term.symbApp] <;>
        try { rename_i fresh; cases fresh <;> contradiction } <;>
        grind [BoolValues.unique, NotBuiltin.ne_or])
    (letE := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (forallTrue := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (forallFalse := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (existsTrue := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (existsFalse := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (annot := by intros; rename_i other evaluated; cases evaluated <;> grind)
    (nil := by intros; rename_i other evaluated; cases evaluated; rfl)
    (cons := by intros; rename_i other evaluated; cases evaluated <;> grind)
    leftEval right rightEval

/-- A known evaluation characterizes every possible output in a functional
model. -/
theorem Eval.iff_eq {model : Model} (functional : ApplyUnique model)
    {environment : List model.Value} {term : Term} {value output : model.Value}
    (evaluated : Eval model environment term value) :
    Eval model environment term output ↔ output = value := by
  constructor
  · intro other
    exact (evaluated.unique functional other).symm
  · intro equal
    subst output
    exact evaluated

/-- A formula holds when it evaluates to semantic Boolean true. -/
def Holds (model : Model) (environment : List model.Value) (term : Term) : Prop :=
  Eval model environment term (model.bool true)

/-! ## Native monomorphic datatype commands -/

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

/-- Sorts owned by one mutual datatype command. -/
def datatypeSorts
    (datatypes : Array (String × Nat × DatatypeDecl)) : List SSort :=
  datatypes.toList.map fun (name, _, _) => datatypeSort name

/-- Function identifiers owned by one datatype command. -/
def datatypeSymbols
    (datatypes : Array (String × Nat × DatatypeDecl)) : List Ident :=
  (datatypeCtors datatypes).flatMap fun (_, ctor) =>
    .symb ctor.name :: ctor.tester ::
      (ctor.selDecls.toList.map fun selector => .symb selector.1)

/-- Syntactic conditions for the verified monomorphic datatype fragment. -/
def DatatypesSupported
    (datatypes : Array (String × Nat × DatatypeDecl)) : Prop :=
  datatypes.toList ≠ [] ∧
  (datatypes.toList.map fun (name, _, _) => name).Nodup ∧
  (datatypeSymbols datatypes).Nodup ∧
  ∀ name arity datatype, (name, arity, datatype) ∈ datatypes.toList →
    arity = 0 ∧ datatype.params.isEmpty = true ∧ datatype.ctors.toList ≠ []

/-- Typed constructor application in a raw model. -/
def CtorApplies (model : Model) (ctor : CtorDecl)
    (arguments : List model.Value) (result : model.Value) : Prop :=
  ValuesTyped model ctor.argSorts arguments ∧
  model.apply (.symb ctor.name) arguments result

/-- One constructor is total, sort-correct, and injective. -/
def ConstructorHolds (model : Model) (dataSort : SSort)
    (ctor : CtorDecl) : Prop :=
  SymbolHasType model (.symb ctor.name) ctor.argSorts dataSort ∧
  ∀ leftArgs rightArgs leftResult rightResult,
    CtorApplies model ctor leftArgs leftResult →
    CtorApplies model ctor rightArgs rightResult →
    leftResult = rightResult → leftArgs = rightArgs

/-- Selectors are total at their declared types and recover the corresponding
argument on their own constructor. No equation is imposed on other
constructors. -/
def SelectorsHold (model : Model) (dataSort : SSort)
    (ctor : CtorDecl) : Prop :=
  ∀ (index : Nat) name resultSort, ctor.selDecls[index]? = some (name, resultSort) →
    SymbolHasType model (.symb name) [dataSort] resultSort ∧
    ∀ arguments result selected,
      CtorApplies model ctor arguments result →
      arguments[index]? = some selected →
      model.apply (.symb name) [result] selected

/-- The implicit tester for a constructor is total and returns true on that
constructor. Rejection of other constructors is stated block-wide below. -/
def TesterHolds (model : Model) (dataSort : SSort)
    (ctor : CtorDecl) : Prop :=
  SymbolHasType model ctor.tester [dataSort] boolSort ∧
  ∀ arguments result, CtorApplies model ctor arguments result →
    model.apply ctor.tester [result] (model.bool true)

/-- Semantic condition of one native monomorphic datatype block.

`rank` rules out cyclic or infinite constructor values: every recursive field in
this declaration block has strictly smaller rank than its constructor result. -/
def DatatypesHold (model : Model)
    (datatypes : Array (String × Nat × DatatypeDecl)) : Prop :=
  DatatypesSupported datatypes ∧
  (∀ dataSort ctor, (dataSort, ctor) ∈ datatypeCtors datatypes →
    ConstructorHolds model dataSort ctor ∧
    SelectorsHold model dataSort ctor ∧
    TesterHolds model dataSort ctor) ∧
  (∀ leftSort leftCtor rightSort rightCtor,
    (leftSort, leftCtor) ∈ datatypeCtors datatypes →
    (rightSort, rightCtor) ∈ datatypeCtors datatypes →
    leftCtor.name ≠ rightCtor.name →
    ∀ leftArgs leftResult rightArgs rightResult,
      CtorApplies model leftCtor leftArgs leftResult →
      CtorApplies model rightCtor rightArgs rightResult →
      leftResult ≠ rightResult) ∧
  (∀ name arity datatype, (name, arity, datatype) ∈ datatypes.toList →
    ∀ value, model.inSort (datatypeSort name) value →
      ∃ ctor, ctor ∈ datatype.ctors.toList ∧
        ∃ arguments, CtorApplies model ctor arguments value) ∧
  (∀ dataSort leftCtor rightCtor,
    (dataSort, leftCtor) ∈ datatypeCtors datatypes →
    (dataSort, rightCtor) ∈ datatypeCtors datatypes →
    leftCtor.name ≠ rightCtor.name →
    ∀ arguments result, CtorApplies model rightCtor arguments result →
      model.apply leftCtor.tester [result] (model.bool false)) ∧
  ∃ rank : model.Value → Nat,
    ∀ dataSort ctor, (dataSort, ctor) ∈ datatypeCtors datatypes →
    ∀ arguments result, CtorApplies model ctor arguments result →
    ∀ (index : Nat) fieldSort fieldValue,
      ctor.argSorts[index]? = some fieldSort →
      arguments[index]? = some fieldValue →
      fieldSort ∈ datatypeSorts datatypes →
      rank fieldValue < rank result

/-! ## Recursive function definitions -/

/-- Syntactic boundary for the recursive definitions used by the verified
fragment. Definitions must form a nonempty, duplicate-free set of ordinary
user symbols. Body typing is retained by the component-specific certificate
that constructs the exact command. -/
def FunsRecSupported (definitions : Array FunDef) : Prop :=
  definitions.toList ≠ [] ∧
  (definitions.toList.map fun definition => definition.name).Nodup ∧
  ∀ definition ∈ definitions.toList,
    NotBuiltin (.symb definition.name)

/-- A raw recursive definition denotes a total typed graph satisfying its body
equation. Arguments enter `Eval` nearest binder first, hence the reversal of
their declaration-order values. Mutual recursion is interpreted through the
same global `model.apply` graph used while evaluating every body. -/
def FunDef.Holds (model : Model) (definition : FunDef) : Prop :=
  SymbolHasType model (.symb definition.name)
    (definition.args.toList.map (·.2)) definition.resSort ∧
  ∀ values, ValuesTyped model (definition.args.toList.map (·.2)) values →
    ∀ output, model.apply (.symb definition.name) values output ↔
      Eval model values.reverse definition.body output

/-- Every member of one simultaneous recursive-definition command satisfies
its equation in the shared model. -/
def FunsRecHold (model : Model) (definitions : Array FunDef) : Prop :=
  ∀ definition ∈ definitions.toList, definition.Holds model

/-- Commands admitted by the verified SMT fragment. -/
def Command.Supported : Command → Prop
  | .setLogic _ | .setOption _ _ | .declSort _ _ | .declFun _ _ _ |
      .assert _ | .checkSat | .getModel | .getProof | .getUnsatCore |
      .echo _ | .exit => True
  | .defSort _ _ _ | .defFun _ _ _ _ _ => False
  | .defFunsRec definitions => FunsRecSupported definitions
  | .declDatatypes datatypes => DatatypesSupported datatypes

/-- Semantic condition imposed by one supported command.  Administrative and
solver-query commands do not constrain a model. -/
def Model.SatisfiesCommand (model : Model) : Command → Prop
  | command@(.declFun name arguments result) =>
      command.Supported ∧ SymbolHasType model (.symb name) arguments.toList result
  | command@(.assert formula) => command.Supported ∧ Holds model [] formula
  | command@(.declDatatypes datatypes) =>
      command.Supported ∧ DatatypesHold model datatypes
  | command@(.defFunsRec definitions) =>
      command.Supported ∧ FunsRecHold model definitions
  | command => command.Supported

/-- Satisfaction of an ordered command sequence by one global SMT model. -/
def Model.SatisfiesCommands (model : Model) (commands : Array Command) : Prop :=
  ∀ command ∈ commands.toList, model.SatisfiesCommand command

set_option quotPrecheck false

/-- A concrete SMT formula holds in a model with no free variables. -/
scoped notation:50 model:51 " ⊨ₛ " formula:51 => Holds model [] formula

/-- A concrete SMT model satisfies an ordered command sequence. -/
scoped notation:50 model:51 " ⊨ₛᶜ " commands:51 =>
  Model.SatisfiesCommands model commands

/-- Semantic unsatisfiability of the concrete command sequence. -/
def CommandsUnsatisfiable (commands : Array Command) : Prop :=
  ∀ model : Model, ¬model.SatisfiesCommands commands

theorem Model.satisfiesCommands_empty (model : Model) :
    model.SatisfiesCommands #[] := by
  intro command membership
  contradiction

theorem Model.satisfiesCommands_append (model : Model)
    (left right : Array Command) :
    model.SatisfiesCommands (left ++ right) ↔
      model.SatisfiesCommands left ∧ model.SatisfiesCommands right := by
  unfold Model.SatisfiesCommands
  simp only [Array.toList_append, List.mem_append]
  grind

/-- A model of an extended command sequence is a model of its prefix. -/
theorem Model.satisfiesCommands_weaken (model : Model)
    {pre suf : Array Command}
    (valid : model.SatisfiesCommands (pre ++ suf)) :
    model.SatisfiesCommands pre :=
  (model.satisfiesCommands_append pre suf).1 valid |>.1

/-- Extend a satisfied command sequence by one satisfied command. -/
theorem Model.satisfiesCommands_push (model : Model)
    {commands : Array Command} {command : Command}
    (commandsValid : model.SatisfiesCommands commands)
    (commandValid : model.SatisfiesCommand command) :
    model.SatisfiesCommands (commands.push command) := by
  unfold Model.SatisfiesCommands at commandsValid
  intro candidate membership
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at membership
  grind

end Crush.SMT
