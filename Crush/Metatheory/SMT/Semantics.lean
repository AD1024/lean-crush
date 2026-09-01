import Crush.SMT.Check

/-!
# Semantics of the verified SMT fragment

The emitted SMT syntax is intentionally untyped. Its semantics is therefore
relational: a model supplies one universe of values, sort membership, literal
interpretations, and a graph for user symbols.  The evaluation relation gives
the built-in Boolean connectives, equality, quantifiers, and simultaneous lets
their standard meaning.

Only the command forms needed by the proved representation path are classified
as supported. Native datatypes have their free-algebra semantics, and both
singleton and mutually recursive function definitions use typed graph
equations. Lambda terms remain outside this first-order semantic fragment.
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

/-- The standard interpretations needed by the modeled SMT fragment.

The raw `Model` structure is intentionally useful for intermediate
countermodel constructions, but by itself it is not an SMT-LIB model: its
Boolean carrier may contain extra values, numerals may collapse, and `>=` may
be an arbitrary graph. `Standard` closes exactly those degrees of freedom used
by the SMT subset covered by the soundness theorem. Other SMT theories remain outside
`Command.Supported` until an analogous interpretation is added here. -/
structure Model.IntegerInterpretation (model : Model) where
  int : Int → model.Value
  int_typed : ∀ value, model.inSort intSort (int value)
  int_injective : Function.Injective int
  int_exhaustive : ∀ value, model.inSort intSort value →
    ∃ integer, value = int integer
  numeral : ∀ value : Nat, model.literal (.num value) = int value
  ge : ∀ left right output,
    model.apply (.symb ">=") [int left, int right] output ↔
      (right ≤ left ∧ output = model.bool true) ∨
        (¬right ≤ left ∧ output = model.bool false)

/-- A raw model is standard for the currently modeled SMT theories when its
Boolean carrier is exactly two-valued, it carries a standard integer
interpretation, and every identifier graph is single-valued. `Nonempty` keeps
this predicate proof-valued while retaining the integer embedding needed to
state the laws. The integer clause is unconditional even for a command array
that does not mention integers; `standardModel_exists` below proves that this
global model class is inhabited. An induced model built from an FO model uses
the separate, model-dependent `SMT.IntView` premise to establish this clause. -/
structure Model.Standard (model : Model) : Prop where
  bool_exhaustive : ∀ value, model.inSort boolSort value →
    ∃ boolean, value = model.bool boolean
  integer : Nonempty model.IntegerInterpretation
  apply_unique : ∀ symbol values left right,
    model.apply symbol values left → model.apply symbol values right →
      left = right

/-! ## Command-indexed interpreted-theory requirements -/

mutual
  /-- Whether a concrete SMT sort contains the built-in integer sort. Compound
  sorts are traversed because an integer carrier can occur beneath another sort
  constructor, for example as an array index or datatype field. -/
  @[reducible] def SSort.requiresIntegerSemantics : SSort → Bool
    | .bvar _ => false
    | .app (.symb "Int") arguments =>
        true || SSort.listRequiresIntegerSemantics arguments.toList
    | .app _ arguments =>
        SSort.listRequiresIntegerSemantics arguments.toList
  termination_by sort => sort.structuralSize
  decreasing_by all_goals simp [SSort.structuralSize] <;> omega

  @[reducible] def SSort.listRequiresIntegerSemantics : List SSort → Bool
    | [] => false
    | sort :: sorts =>
        sort.requiresIntegerSemantics ||
          SSort.listRequiresIntegerSemantics sorts
  termination_by sorts => SSort.listStructuralSize sorts
  decreasing_by all_goals simp [SSort.listStructuralSize] <;> omega
end

@[simp] theorem SSort.requiresIntegerSemantics_boolSort :
    boolSort.requiresIntegerSemantics = false := by
  rw [SSort.requiresIntegerSemantics.eq_def]
  simp [boolSort, SSort.listRequiresIntegerSemantics.eq_def]

@[simp] theorem SSort.listRequiresIntegerSemantics_nil :
    SSort.listRequiresIntegerSemantics [] = false := by
  rw [SSort.listRequiresIntegerSemantics.eq_def]

@[simp] theorem SSort.listRequiresIntegerSemantics_cons
    (sort : SSort) (sorts : List SSort) :
    SSort.listRequiresIntegerSemantics (sort :: sorts) =
      (sort.requiresIntegerSemantics ||
        SSort.listRequiresIntegerSemantics sorts) := by
  rw [SSort.listRequiresIntegerSemantics.eq_def]

mutual
  /-- Whether a concrete term uses syntax whose SMT-LIB meaning depends on the
  standard integer carrier. Explicit sorts are inspected at binders; numerals
  and the currently modeled integer comparison are inspected at term nodes. -/
  @[reducible] def Term.requiresIntegerSemantics : Term → Bool
    | .lit (.num _) => true
    | .lit _ | .bvar _ => false
    | .app (.symb ">=") arguments =>
        true || Term.listRequiresIntegerSemantics arguments.toList
    | .app _ arguments =>
        Term.listRequiresIntegerSemantics arguments.toList
    | .letE bindings body =>
        Term.bindingListRequiresIntegerSemantics bindings.toList ||
          body.requiresIntegerSemantics
    | .forallE binders body | .existsE binders body | .lam binders body =>
        SSort.listRequiresIntegerSemantics (binders.toList.map (·.2)) ||
          body.requiresIntegerSemantics
    | .annot body _ => body.requiresIntegerSemantics
  termination_by term => term.structuralSize
  decreasing_by all_goals simp [Term.structuralSize] <;> omega

  @[reducible] def Term.listRequiresIntegerSemantics : List Term → Bool
    | [] => false
    | term :: terms =>
        term.requiresIntegerSemantics ||
          Term.listRequiresIntegerSemantics terms
  termination_by terms => Term.listStructuralSize terms
  decreasing_by all_goals simp [Term.listStructuralSize] <;> omega

  @[reducible] def Term.bindingListRequiresIntegerSemantics :
      List (String × Term) → Bool
    | [] => false
    | (_, term) :: bindings =>
        term.requiresIntegerSemantics ||
          Term.bindingListRequiresIntegerSemantics bindings
  termination_by bindings => Term.bindingListStructuralSize bindings
  decreasing_by all_goals simp [Term.bindingListStructuralSize] <;> omega

end

@[simp] theorem Term.requiresIntegerSemantics_bvar (index : Nat) :
    (Term.bvar index).requiresIntegerSemantics = false := by
  rw [Term.requiresIntegerSemantics.eq_def]

@[simp] theorem Term.requiresIntegerSemantics_app_integerComparison
    (arguments : Array Term) :
    (Term.app (.symb ">=") arguments).requiresIntegerSemantics = true := by
  rw [Term.requiresIntegerSemantics.eq_def]
  simp

@[simp] theorem Term.requiresIntegerSemantics_app_of_ne
    (identifier : Ident) (arguments : Array Term)
    (notIntegerComparison : identifier ≠ .symb ">=") :
    (Term.app identifier arguments).requiresIntegerSemantics =
      Term.listRequiresIntegerSemantics arguments.toList := by
  simp only [Term.requiresIntegerSemantics.eq_def]

@[simp] theorem Term.requiresIntegerSemantics_forallE
    (binders : Array (String × SSort)) (body : Term) :
    (Term.forallE binders body).requiresIntegerSemantics =
      (SSort.listRequiresIntegerSemantics (binders.toList.map (·.2)) ||
        body.requiresIntegerSemantics) := by
  rw [Term.requiresIntegerSemantics.eq_def]

@[simp] theorem Term.requiresIntegerSemantics_existsE
    (binders : Array (String × SSort)) (body : Term) :
    (Term.existsE binders body).requiresIntegerSemantics =
      (SSort.listRequiresIntegerSemantics (binders.toList.map (·.2)) ||
        body.requiresIntegerSemantics) := by
  rw [Term.requiresIntegerSemantics.eq_def]

@[simp] theorem Term.listRequiresIntegerSemantics_nil :
    Term.listRequiresIntegerSemantics [] = false := by
  rw [Term.listRequiresIntegerSemantics.eq_def]

@[simp] theorem Term.listRequiresIntegerSemantics_cons
    (term : Term) (terms : List Term) :
    Term.listRequiresIntegerSemantics (term :: terms) =
      (term.requiresIntegerSemantics ||
        Term.listRequiresIntegerSemantics terms) := by
  rw [Term.listRequiresIntegerSemantics.eq_def]

@[simp] theorem Term.requiresIntegerSemantics_annot
    (body : Term) (attributes : Array Attr) :
    (Term.annot body attributes).requiresIntegerSemantics =
      body.requiresIntegerSemantics := by
  rw [Term.requiresIntegerSemantics.eq_def]

@[reducible] def FunDef.requiresIntegerSemantics (definition : FunDef) : Bool :=
  SSort.listRequiresIntegerSemantics (definition.args.toList.map (·.2)) ||
    definition.resSort.requiresIntegerSemantics ||
      definition.body.requiresIntegerSemantics

@[reducible] def CtorDecl.requiresIntegerSemantics (constructor : CtorDecl) : Bool :=
  SSort.listRequiresIntegerSemantics (constructor.selDecls.toList.map (·.2))

@[reducible] def DatatypeDecl.requiresIntegerSemantics
    (datatype : DatatypeDecl) : Bool :=
  datatype.ctors.toList.any CtorDecl.requiresIntegerSemantics

/-- Whether one command requires the standard integer carrier. The test is
conservative on malformed syntax; `CommandsWellTyped` separately establishes
that accepted commands use only the modeled integer operations. -/
@[reducible] def Command.requiresIntegerSemantics : Command → Bool
  | .declFun _ arguments result =>
      SSort.listRequiresIntegerSemantics arguments.toList ||
        result.requiresIntegerSemantics
  | .defFun definition => definition.requiresIntegerSemantics
  | .defFunsRec definitions =>
      definitions.toList.any FunDef.requiresIntegerSemantics
  | .declDatatypes datatypes =>
      datatypes.toList.any fun (_, _, datatype) =>
        datatype.requiresIntegerSemantics
  | .assert term => term.requiresIntegerSemantics
  | .setLogic _ | .setOption _ _ | .declSort _ _ | .checkSat |
      .getModel | .getProof | .getUnsatCore | .echo _ | .exit => false

/-- Whether any command requires standard integer semantics. -/
@[reducible] def CommandsRequireIntegerSemantics
    (commands : Array Command) : Bool :=
  commands.toList.any Command.requiresIntegerSemantics

/-- The standard laws needed for one concrete command array. Boolean
two-valuedness and functional application are always required. The integer
carrier is required exactly when integer syntax or an explicit `Int` sort
occurs in that array. -/
structure Model.StandardFor (model : Model) (commands : Array Command) : Prop where
  bool_exhaustive : ∀ value, model.inSort boolSort value →
    ∃ boolean, value = model.bool boolean
  integer : CommandsRequireIntegerSemantics commands = true →
    Nonempty model.IntegerInterpretation
  apply_unique : ∀ symbol values left right,
    model.apply symbol values left → model.apply symbol values right →
      left = right

/-- A globally standard model is standard for every concrete command array. -/
theorem Model.Standard.forCommands {model : Model} (standard : model.Standard)
    (commands : Array Command) : model.StandardFor commands where
  bool_exhaustive := standard.bool_exhaustive
  integer := fun _ => standard.integer
  apply_unique := standard.apply_unique

/-- Transfer command-indexed standardness when two arrays require the same
interpreted theories. -/
theorem Model.StandardFor.of_requirements_eq {model : Model}
    {left right : Array Command} (standard : model.StandardFor left)
    (equal : CommandsRequireIntegerSemantics left =
      CommandsRequireIntegerSemantics right) : model.StandardFor right where
  bool_exhaustive := standard.bool_exhaustive
  integer := by
    intro required
    apply standard.integer
    rw [equal]
    exact required
  apply_unique := standard.apply_unique

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

/-- A standard SMT model interprets each function symbol as a function. -/
theorem Model.Standard.applyUnique {model : Model} (standard : model.Standard) :
    ApplyUnique model := standard.apply_unique

/-- Command-indexed standard models retain globally functional application. -/
theorem Model.StandardFor.applyUnique {model : Model} {commands : Array Command}
    (standard : model.StandardFor commands) : ApplyUnique model :=
  standard.apply_unique

/-! ## A concrete standard-model witness -/

/-- Values used only to show that the standard-model class is inhabited.
Uninterpreted sorts receive one sort-indexed value. -/
private inductive StandardWitnessValue where
  | boolean : Bool → StandardWitnessValue
  | integer : Int → StandardWitnessValue
  | uninterpreted : SSort → StandardWitnessValue

private def StandardWitnessValue.InSort (sort : SSort) :
    StandardWitnessValue → Prop
  | .boolean _ => sort = boolSort
  | .integer _ => sort = intSort
  | .uninterpreted declared =>
      sort = declared ∧ sort ≠ boolSort ∧ sort ≠ intSort

private def standardWitnessLiteral : Literal → StandardWitnessValue
  | .bool value => .boolean value
  | .num value => .integer value
  | .str _ => .uninterpreted stringSort
  | .bitvec width _ => .uninterpreted (bitvecSort width)

private def standardWitnessApply (identifier : Ident)
    (arguments : List StandardWitnessValue) (output : StandardWitnessValue) : Prop :=
  ∃ left right : Int,
    identifier = .symb ">=" ∧
    arguments = [.integer left, .integer right] ∧
    output = .boolean (decide (right ≤ left))

/-- A concrete model of the standard Boolean and integer laws. Its only
interpreted application symbol is integer `>=`: logical connectives and
equality are handled directly by `Eval`, while arithmetic operators such as
`+` and bit-vector operators are outside the SMT subset currently covered by
the soundness theorem.
Declarations add their own typed graphs in the model constructions used by the
lowering proof. -/
private def standardWitnessModel : Model where
  Value := StandardWitnessValue
  inSort := StandardWitnessValue.InSort
  sortNonempty := by
    intro sort
    by_cases boolEq : sort = boolSort
    · exact ⟨.boolean false, boolEq⟩
    by_cases intEq : sort = intSort
    · exact ⟨.integer 0, intEq⟩
    · exact ⟨.uninterpreted sort, rfl, boolEq, intEq⟩
  bool := .boolean
  boolTyped := by intro value; rfl
  boolInjective := by intro left right equal; injection equal
  literal := standardWitnessLiteral
  literalTyped := by
    intro literal
    cases literal <;>
      simp [standardWitnessLiteral, StandardWitnessValue.InSort,
        Literal.sort, stringSort, boolSort, intSort, bitvecSort]
  apply := standardWitnessApply

private theorem boolSort_ne_intSort : boolSort ≠ intSort := by
  intro equal
  change SSort.app (.symb "Bool") #[] =
    SSort.app (.symb "Int") #[] at equal
  injection equal with identifiersEqual
  injection identifiersEqual with namesEqual
  exact (by decide : ("Bool" : String) ≠ "Int") namesEqual

/-- Standard SMT models exist independently of any command sequence. This
rules out vacuity caused by an empty model class. -/
theorem standardModel_exists : ∃ model : Model, model.Standard := by
  refine ⟨standardWitnessModel, ?_⟩
  refine {
    bool_exhaustive := ?_
    integer := ?_
    apply_unique := ?_ }
  · intro value typed
    cases value with
    | boolean value => exact ⟨value, rfl⟩
    | integer value => exact False.elim (boolSort_ne_intSort typed)
    | uninterpreted sort => simp [standardWitnessModel,
        StandardWitnessValue.InSort] at typed
  · refine ⟨{
      int := .integer
      int_typed := by intro value; rfl
      int_injective := by intro left right equal; injection equal
      int_exhaustive := ?_
      numeral := by intro value; rfl
      ge := ?_ }⟩
    · intro value typed
      cases value with
      | boolean value => exact False.elim (boolSort_ne_intSort typed.symm)
      | integer value => exact ⟨value, rfl⟩
      | uninterpreted sort => simp [standardWitnessModel,
          StandardWitnessValue.InSort] at typed
    · intro left right output
      constructor
      · intro applied
        change standardWitnessApply (.symb ">=")
          [.integer left, .integer right] output at applied
        rcases applied with
          ⟨actualLeft, actualRight, identifierEq, argumentsEq, outputEq⟩
        injection argumentsEq with leftEq restEq
        injection restEq with rightEq tailEq
        injection leftEq with leftIntEq
        injection rightEq with rightIntEq
        subst actualLeft
        subst actualRight
        by_cases ordered : right ≤ left
        · exact Or.inl ⟨ordered,
            by simpa [standardWitnessModel, ordered] using outputEq⟩
        · exact Or.inr ⟨ordered,
            by simpa [standardWitnessModel, ordered] using outputEq⟩
      · intro standardOutput
        change standardWitnessApply (.symb ">=")
          [.integer left, .integer right] output
        refine ⟨left, right, rfl, rfl, ?_⟩
        rcases standardOutput with ⟨ordered, rfl⟩ | ⟨notOrdered, rfl⟩
        · simp [standardWitnessModel, ordered]
        · simp [standardWitnessModel, notOrdered]
  · intro identifier arguments left right leftApplied rightApplied
    rcases leftApplied with
      ⟨leftArg, rightArg, identifierEq, argumentsEq, leftEq⟩
    rcases rightApplied with
      ⟨otherLeft, otherRight, otherIdentifierEq, otherArgumentsEq, rightEq⟩
    rw [argumentsEq] at otherArgumentsEq
    injection otherArgumentsEq with leftArgEq restEq
    injection restEq with rightArgEq tailEq
    injection leftArgEq with leftIntEq
    injection rightArgEq with rightIntEq
    subst otherLeft
    subst otherRight
    exact leftEq.trans rightEq.symm

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

/-- An identifier available to encoded source symbols: it is neither a
logical built-in handled by dedicated evaluation rules nor the interpreted
integer comparison constrained by `IntegerInterpretation`. -/
structure NotInterpreted (identifier : Ident) : Prop where
  notLogicalBuiltin : NotBuiltin identifier
  ne_integerComparison : identifier ≠ .symb ">="

instance (identifier : Ident) : Decidable (NotInterpreted identifier) :=
  decidable_of_iff
    (NotBuiltin identifier ∧ identifier ≠ .symb ">=")
    ⟨fun properties => ⟨properties.1, properties.2⟩,
      fun available => ⟨available.notLogicalBuiltin,
        available.ne_integerComparison⟩⟩

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

/-- Term attributes do not change evaluation. -/
theorem Eval.annot_iff {model : Model} {environment : List model.Value}
    {term : Term} {attributes : Array Attr} {value : model.Value} :
    Eval model environment (.annot term attributes) value ↔
      Eval model environment term value := by
  constructor
  · intro evaluated
    exact match evaluated with
      | .annot bodyEval => bodyEval
  · exact Eval.annot

/-- Evaluation of a Boolean literal has its unique distinguished value without
requiring any assumption about the user-symbol graph. -/
theorem Eval.boolLit_iff {model : Model} {environment : List model.Value}
    {boolean : Bool} {value : model.Value} :
    Eval model environment (.lit (.bool boolean)) value ↔
      value = model.bool boolean := by
  constructor
  · intro evaluated
    exact match evaluated with
      | .boolLit _ => rfl
      | .literal _ notBool => False.elim (notBool boolean rfl)
  · intro equal
    subst value
    exact Eval.boolLit boolean

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

/-- Structural conditions for the modeled monomorphic datatype fragment:
the block is nonempty, sort and symbol names are distinct, and every member is
a nonempty nullary declaration without type parameters. -/
def DatatypesStructurallyWellFormed
    (datatypes : Array (String × Nat × DatatypeDecl)) : Prop :=
  datatypesStructurallyWellFormed datatypes = true

/-- Complete datatype admission condition. Structural validity is paired with
the same executable finite-constructor check used by
`checkMetatheoryScript`. -/
def DatatypesWellFormed
    (datatypes : Array (String × Nat × DatatypeDecl)) : Prop :=
  DatatypesStructurallyWellFormed datatypes ∧
  datatypesProductive datatypes = true

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
  DatatypesWellFormed datatypes ∧
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

/-! ## Function definitions -/

/-- A raw function definition denotes a total typed graph satisfying its body
equation. Arguments enter `Eval` nearest binder first, hence the reversal of
their declaration-order values. Recursive definitions are interpreted through
the same global `model.apply` graph used while evaluating every body. -/
def FunDef.Holds (model : Model) (definition : FunDef) : Prop :=
  SymbolHasType model (.symb definition.name)
    (definition.args.toList.map (·.2)) definition.resSort ∧
  ∀ values, ValuesTyped model (definition.args.toList.map (·.2)) values →
    ∀ output, model.apply (.symb definition.name) values output ↔
      Eval model values.reverse definition.body output

/-- Every member of a function-definition group satisfies its equation in the
shared model. A nonrecursive `define-fun` uses the singleton specialization. -/
def FunctionDefinitionsHold (model : Model) (definitions : Array FunDef) : Prop :=
  ∀ definition ∈ definitions.toList, definition.Holds model

/-- Semantic side conditions not expressible as ordinary SMT typing. The
declaration-aware type checker handles terms, scopes, symbol signatures, and
the distinction between recursive and nonrecursive definitions. Native
datatypes additionally require the free-algebra side conditions below. -/
def Command.Supported : Command → Prop
  | .declDatatypes datatypes => DatatypesWellFormed datatypes
  | _ => True

/-- Semantic condition imposed by one command. Static membership in the modeled
fragment is tracked separately by `Command.Supported`; it is a required field of
`CommandsUnsatisfiable`, not a way to make command satisfaction false. -/
def Model.SatisfiesCommand (model : Model) : Command → Prop
  | .declFun name arguments result =>
      SymbolHasType model (.symb name) arguments.toList result
  | .assert formula => Holds model [] formula
  | .declDatatypes datatypes => DatatypesHold model datatypes
  | .defFun definition => definition.Holds model
  | .defFunsRec definitions => FunctionDefinitionsHold model definitions
  | _ => True

/-- Satisfaction of every command in an array by one global SMT model. The raw
semantics is deliberately insensitive to order and repeated occurrences. -/
def Model.SatisfiesCommands (model : Model) (commands : Array Command) : Prop :=
  ∀ command ∈ commands.toList, model.SatisfiesCommand command

/-- Every command belongs to the explicitly modeled SMT fragment. Keeping this
condition separate from model satisfaction prevents an unmodeled command from
making a script appear unsatisfiable merely because its satisfaction predicate
is false. -/
def CommandsSupported (commands : Array Command) : Prop :=
  ∀ command ∈ commands.toList, command.Supported

/-- The concrete command sequence is accepted by the declaration-aware type
checker for the modeled first-order SMT fragment. This judgment is
order-sensitive, unlike `SameCommandSet`: it rejects unknown symbols,
use-before-declaration, out-of-scope variables, ill-sorted terms, unsupported
theory operators, and lambda syntax. -/
def CommandsWellTyped (commands : Array Command) : Prop :=
  Crush.SMT.metatheoryScriptWellTyped commands = true

/-- Two arrays impose exactly the same semantic command obligations. Command
order and duplicate occurrences are intentionally irrelevant here; concrete
SMT-LIB scope/order is checked separately by the script validator. -/
def SameCommandSet (left right : Array Command) : Prop :=
  (∀ command ∈ left.toList, command ∈ right.toList) ∧
  (∀ command ∈ right.toList, command ∈ left.toList)

namespace SameCommandSet

theorem refl (commands : Array Command) : SameCommandSet commands commands := by
  exact ⟨fun _ member => member, fun _ member => member⟩

theorem symm {left right : Array Command}
    (same : SameCommandSet left right) : SameCommandSet right left :=
  ⟨same.2, same.1⟩

theorem of_eq {left right : Array Command} (equal : left = right) :
    SameCommandSet left right := by
  subst right
  exact refl left

end SameCommandSet

set_option quotPrecheck false

/-- A concrete SMT formula holds in a model with no free variables. -/
scoped notation:50 model:51 " ⊨ₛ " formula:51 => Holds model [] formula

/-- A concrete SMT model satisfies every command obligation in an array. -/
scoped notation:50 model:51 " ⊨ₛᶜ " commands:51 =>
  Model.SatisfiesCommands model commands

/-- A well-typed command sequence with no model in the unconstrained relational
semantics. This internal notion is useful for component-level countermodel
lemmas, but it is deliberately not identified with SMT-LIB unsatisfiability:
`Model` alone does not fix interpreted theories. Requiring the same static
checks as the external notion prevents an ill-formed script from establishing
this stronger no-raw-model premise vacuously. -/
structure AbstractCommandsUnsatisfiable (commands : Array Command) : Prop where
  supported : CommandsSupported commands
  wellTyped : CommandsWellTyped commands
  noModel : ∀ model : Model, ¬model.SatisfiesCommands commands

/-- A well-typed command sequence with no standard model.

Both static fields are logically important. `supported` records the additional
free-datatype conditions; `wellTyped` rejects malformed or semantically
unmodeled syntax. `noModel` quantifies only over models satisfying the standard
laws for the theories used by this command array. In particular, integer laws
are mandatory for arrays containing integer syntax, but not for Boolean-only
arrays. -/
structure CommandsUnsatisfiable (commands : Array Command) : Prop where
  supported : CommandsSupported commands
  wellTyped : CommandsWellTyped commands
  noModel : ∀ model : Model, model.StandardFor commands →
    ¬model.SatisfiesCommands commands

theorem Model.satisfiesCommands_empty (model : Model) :
    model.SatisfiesCommands #[] := by
  intro command membership
  contradiction

theorem commandsSupported_empty : CommandsSupported #[] := by
  intro command membership
  contradiction

theorem Model.satisfiesCommands_append (model : Model)
    (left right : Array Command) :
    model.SatisfiesCommands (left ++ right) ↔
      model.SatisfiesCommands left ∧ model.SatisfiesCommands right := by
  unfold Model.SatisfiesCommands
  simp only [Array.toList_append, List.mem_append]
  grind

theorem commandsSupported_append (left right : Array Command) :
    CommandsSupported (left ++ right) ↔
      CommandsSupported left ∧ CommandsSupported right := by
  unfold CommandsSupported
  simp only [Array.toList_append, List.mem_append]
  grind

/-- Raw command satisfaction depends only on the command set. -/
theorem Model.satisfiesCommands_congr (model : Model)
    {left right : Array Command} (same : SameCommandSet left right) :
    model.SatisfiesCommands left ↔ model.SatisfiesCommands right := by
  constructor
  · intro valid command member
    exact valid command (same.2 command member)
  · intro valid command member
    exact valid command (same.1 command member)

/-- Fragment membership, like satisfaction, depends only on the command set. -/
theorem commandsSupported_congr {left right : Array Command}
    (same : SameCommandSet left right) :
    CommandsSupported left ↔ CommandsSupported right := by
  constructor
  · intro supported command member
    exact supported command (same.2 command member)
  · intro supported command member
    exact supported command (same.1 command member)

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
