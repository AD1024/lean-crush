import Crush.SMT.Syntax

/-!
# Semantics of the verified SMT fragment

The production SMT syntax is intentionally untyped.  Its semantics is therefore
relational: a model supplies one universe of values, sort membership, literal
interpretations, and a graph for user symbols.  The evaluation relation gives
the built-in Boolean connectives, equality, quantifiers, and simultaneous lets
their standard meaning.

Only the command forms needed by the proved representation path are classified
as supported.  Definitions, recursive definitions, lambdas, and datatype
commands remain outside this fragment instead of receiving a vacuous semantics.
-/

namespace Crush.SMT

/-- Standard nullary SMT Boolean sort. -/
def boolSort : SSort := .app (.symb "Bool") #[]

/-- Standard nullary SMT integer sort. -/
def intSort : SSort := .app (.symb "Int") #[]

/-- Standard nullary SMT string sort. -/
def stringSort : SSort := .app (.symb "String") #[]

/-- SMT bit-vector sort of a fixed width. -/
def bitvecSort (width : Nat) : SSort :=
  .app (.indexed "BitVec" #[.inr width]) #[]

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

/-- Semantic values are the images of the listed Boolean values. -/
inductive BoolValues (model : Model) : List model.Value → List Bool → Prop where
  | nil : BoolValues model [] []
  | cons {value : Bool} {values : List model.Value} {booleans : List Bool} :
      BoolValues model values booleans →
        BoolValues model (model.bool value :: values) (value :: booleans)

/-- Logical built-ins are interpreted by dedicated `Eval` constructors rather
than the arbitrary user-symbol graph. -/
inductive NotBuiltin : Ident → Prop where
  | indexed (name : String) (indices : Array (String ⊕ Nat)) :
      NotBuiltin (.indexed name indices)
  | symb (name : String) :
      name ≠ "=" → name ≠ "not" → name ≠ "=>" →
      name ≠ "and" → name ≠ "or" → NotBuiltin (.symb name)

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

/-- A formula holds when it evaluates to semantic Boolean true. -/
def Holds (model : Model) (environment : List model.Value) (term : Term) : Prop :=
  Eval model environment term (model.bool true)

/-- Commands admitted by the verified SMT fragment. -/
def Command.Supported : Command → Prop
  | .setLogic _ | .setOption _ _ | .declSort _ _ | .declFun _ _ _ |
      .assert _ | .checkSat | .getModel | .getProof | .getUnsatCore |
      .echo _ | .exit => True
  | .defSort _ _ _ | .defFun _ _ _ _ _ | .defFunsRec _ |
      .declDatatypes _ => False

/-- Semantic condition imposed by one supported command.  Administrative and
solver-query commands do not constrain a model. -/
def Model.SatisfiesCommand (model : Model) : Command → Prop
  | command@(.declFun name arguments result) =>
      command.Supported ∧ SymbolHasType model (.symb name) arguments.toList result
  | command@(.assert formula) => command.Supported ∧ Holds model [] formula
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
