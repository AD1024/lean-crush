import Crush.SMT.Theory

/-!
# Theory requirements of SMT syntax

These definitions traverse SMT syntax once per modeled registry entry. A
requirement is selected by the provider of a sort constructor, literal, or
application identifier. Sort arguments are visited recursively, so nested
combinations such as `Array Int String` select every represented component.
-/

namespace Crush.SMT.Theory

namespace SigEnv

/-- Whether a provider selects one modeled theory entry. -/
def selects {env : SigEnv} (theory : Fin env.modeled.length) :
    Provider env.modeled.length env.syntaxOnly.length → Bool
  | .modeled candidate => decide (candidate = theory)
  | .core | .syntaxOnly _ => false

/-- Whether a sort constructor is provided by one modeled theory entry. -/
def usesSortCtor (env : SigEnv) (theory : Fin env.modeled.length)
    (identifier : Ident) : Bool :=
  match env.sortProvider identifier with
  | some provider => selects theory provider
  | none => false

/-- Whether a literal is provided by one modeled theory entry. -/
def usesLiteral (env : SigEnv) (theory : Fin env.modeled.length)
    (literal : Literal) : Bool :=
  match env.literalProvider literal with
  | some provider => selects theory provider
  | none => false

/-- Whether an application identifier is provided by one modeled theory
entry. -/
def usesIdent (env : SigEnv) (theory : Fin env.modeled.length)
    (identifier : Ident) : Bool :=
  match env.identProvider identifier with
  | some provider => selects theory provider
  | none => false

mutual
  /-- Whether a complete SMT sort uses one modeled theory. -/
  @[reducible] def usesSort (env : SigEnv) (theory : Fin env.modeled.length) :
      SSort → Bool
    | .bvar _ => false
    | .app identifier arguments =>
        env.usesSortCtor theory identifier ||
          env.usesSortList theory arguments.toList
  termination_by sort => sort.structuralSize
  decreasing_by all_goals simp [SSort.structuralSize] <;> omega

  /-- Whether a list of SMT sorts uses one modeled theory. -/
  @[reducible] def usesSortList (env : SigEnv) (theory : Fin env.modeled.length) :
      List SSort → Bool
    | [] => false
    | sort :: sorts =>
        env.usesSort theory sort || env.usesSortList theory sorts
  termination_by sorts => SSort.listStructuralSize sorts
  decreasing_by all_goals simp [SSort.listStructuralSize] <;> omega
end

@[simp] theorem usesSort_bvar (env : SigEnv) (theory) (index : Nat) :
    env.usesSort theory (.bvar index) = false := by
  rw [usesSort.eq_1]

@[simp] theorem usesSort_app (env : SigEnv) (theory) (identifier : Ident)
    (arguments : Array SSort) :
    env.usesSort theory (.app identifier arguments) =
      (env.usesSortCtor theory identifier ||
        env.usesSortList theory arguments.toList) := by
  rw [usesSort.eq_2]

@[simp] theorem usesSortList_nil (env : SigEnv) (theory) :
    env.usesSortList theory [] = false := by
  rw [usesSortList.eq_1]

@[simp] theorem usesSortList_cons (env : SigEnv) (theory) (sort : SSort)
    (sorts : List SSort) :
    env.usesSortList theory (sort :: sorts) =
      (env.usesSort theory sort || env.usesSortList theory sorts) := by
  rw [usesSortList.eq_2]

mutual
  /-- Whether a term's semantic syntax uses one modeled theory. Attribute
patterns are solver guidance and do not contribute semantic obligations. -/
  @[reducible] def usesTerm (env : SigEnv) (theory : Fin env.modeled.length) :
      Term → Bool
    | .lit literal => env.usesLiteral theory literal
    | .bvar _ => false
    | .app identifier arguments =>
        env.usesIdent theory identifier ||
          env.usesTermList theory arguments.toList
    | .letE bindings body =>
        env.usesBindingList theory bindings.toList ||
          env.usesTerm theory body
    | .forallE binders body | .existsE binders body | .lam binders body =>
        env.usesSortList theory (binders.toList.map (fun binder => binder.2)) ||
          env.usesTerm theory body
    | .annot body _ => env.usesTerm theory body
  termination_by term => term.structuralSize
  decreasing_by all_goals simp [Term.structuralSize] <;> omega

  /-- Whether a list of terms uses one modeled theory. -/
  @[reducible] def usesTermList (env : SigEnv) (theory : Fin env.modeled.length) :
      List Term → Bool
    | [] => false
    | term :: terms =>
        env.usesTerm theory term || env.usesTermList theory terms
  termination_by terms => Term.listStructuralSize terms
  decreasing_by all_goals simp [Term.listStructuralSize] <;> omega

  /-- Whether simultaneous `let` bindings use one modeled theory. -/
  @[reducible] def usesBindingList (env : SigEnv) (theory : Fin env.modeled.length) :
      List (String × Term) → Bool
    | [] => false
    | (_, term) :: bindings =>
        env.usesTerm theory term || env.usesBindingList theory bindings
  termination_by bindings => Term.bindingListStructuralSize bindings
  decreasing_by all_goals simp [Term.bindingListStructuralSize] <;> omega
end

@[simp] theorem usesTerm_lit (env : SigEnv) (theory) (literal : Literal) :
    env.usesTerm theory (.lit literal) = env.usesLiteral theory literal := by
  rw [usesTerm.eq_1]

@[simp] theorem usesTerm_bvar (env : SigEnv) (theory) (index : Nat) :
    env.usesTerm theory (.bvar index) = false := by
  rw [usesTerm.eq_2]

@[simp] theorem usesTerm_app (env : SigEnv) (theory) (identifier : Ident)
    (arguments : Array Term) :
    env.usesTerm theory (.app identifier arguments) =
      (env.usesIdent theory identifier ||
        env.usesTermList theory arguments.toList) := by
  rw [usesTerm.eq_3]

@[simp] theorem usesTerm_let (env : SigEnv) (theory)
    (bindings : Array (String × Term)) (body : Term) :
    env.usesTerm theory (.letE bindings body) =
      (env.usesBindingList theory bindings.toList || env.usesTerm theory body) := by
  rw [usesTerm.eq_4]

@[simp] theorem usesTerm_forall (env : SigEnv) (theory)
    (binders : Array (String × SSort)) (body : Term) :
    env.usesTerm theory (.forallE binders body) =
      (env.usesSortList theory (binders.toList.map (fun binder => binder.2)) ||
        env.usesTerm theory body) := by
  rw [usesTerm.eq_5]

@[simp] theorem usesTerm_exists (env : SigEnv) (theory)
    (binders : Array (String × SSort)) (body : Term) :
    env.usesTerm theory (.existsE binders body) =
      (env.usesSortList theory (binders.toList.map (fun binder => binder.2)) ||
        env.usesTerm theory body) := by
  rw [usesTerm.eq_6]

@[simp] theorem usesTerm_lam (env : SigEnv) (theory)
    (binders : Array (String × SSort)) (body : Term) :
    env.usesTerm theory (.lam binders body) =
      (env.usesSortList theory (binders.toList.map (fun binder => binder.2)) ||
        env.usesTerm theory body) := by
  rw [usesTerm.eq_7]

@[simp] theorem usesTerm_annot (env : SigEnv) (theory) (body : Term)
    (attributes : Array Attr) :
    env.usesTerm theory (.annot body attributes) = env.usesTerm theory body := by
  rw [usesTerm.eq_8]

@[simp] theorem usesTermList_nil (env : SigEnv) (theory) :
    env.usesTermList theory [] = false := by
  rw [usesTermList.eq_1]

@[simp] theorem usesTermList_cons (env : SigEnv) (theory) (term : Term)
    (terms : List Term) :
    env.usesTermList theory (term :: terms) =
      (env.usesTerm theory term || env.usesTermList theory terms) := by
  rw [usesTermList.eq_2]

@[simp] theorem usesBindingList_nil (env : SigEnv) (theory) :
    env.usesBindingList theory [] = false := by
  rw [usesBindingList.eq_1]

@[simp] theorem usesBindingList_cons (env : SigEnv) (theory) (name : String)
    (term : Term) (bindings : List (String × Term)) :
    env.usesBindingList theory ((name, term) :: bindings) =
      (env.usesTerm theory term || env.usesBindingList theory bindings) := by
  rw [usesBindingList.eq_2]

/-- Whether a function definition uses one modeled theory. -/
@[reducible] def usesFunDef (env : SigEnv) (theory : Fin env.modeled.length)
    (definition : FunDef) : Bool :=
  env.usesSortList theory (definition.args.toList.map (fun argument => argument.2)) ||
    env.usesSort theory definition.resSort ||
      env.usesTerm theory definition.body

/-- Whether a datatype constructor's selector sorts use one modeled theory. -/
@[reducible] def usesCtor (env : SigEnv) (theory : Fin env.modeled.length)
    (constructor : CtorDecl) : Bool :=
  env.usesSortList theory
    (constructor.selDecls.toList.map (fun selector => selector.2))

/-- Whether a datatype declaration uses one modeled theory. -/
@[reducible] def usesDatatype (env : SigEnv) (theory : Fin env.modeled.length)
    (datatype : DatatypeDecl) : Bool :=
  datatype.ctors.toList.any (env.usesCtor theory)

/-- Whether one command uses one modeled theory. Malformed commands may
conservatively select extra theories; the modeled checker independently proves
that every accepted theory symbol has semantics. -/
@[reducible] def usesCommand (env : SigEnv) (theory : Fin env.modeled.length) :
    Command → Bool
  | .declFun _ arguments result =>
      env.usesSortList theory arguments.toList || env.usesSort theory result
  | .defFun definition => env.usesFunDef theory definition
  | .defFunsRec definitions =>
      definitions.toList.any (env.usesFunDef theory)
  | .declDatatypes datatypes =>
      datatypes.toList.any fun declaration =>
        env.usesDatatype theory declaration.2.2
  | .assert term => env.usesTerm theory term
  | .setLogic _ | .setOption _ _ | .declSort _ _ | .checkSat |
      .getModel | .getProof | .getUnsatCore | .echo _ | .exit => false

/-- Whether a command array uses one modeled theory. -/
@[reducible] def usesCommands (env : SigEnv) (commands : Array Command)
    (theory : Fin env.modeled.length) : Bool :=
  commands.toList.any (env.usesCommand theory)

@[simp] theorem usesCommands_append (env : SigEnv)
    (left right : Array Command) (theory : Fin env.modeled.length) :
    env.usesCommands (left ++ right) theory =
      (env.usesCommands left theory || env.usesCommands right theory) := by
  simp [usesCommands]

@[simp] theorem default_usesIdent_int (identifier : Ident) :
    defaultSigEnv.usesIdent intId identifier = intContainsIdent identifier := by
  cases integer : intContainsIdent identifier
  · unfold usesIdent
    cases found : defaultSigEnv.identProvider identifier with
    | none => rfl
    | some provider =>
        cases provider with
        | core | syntaxOnly index => rfl
        | modeled index =>
            have present :=
              (default_identProvider_modeled_iff identifier index).mp found
            simp [integer] at present
  · have found :=
      (default_identProvider_modeled_iff identifier intId).mpr integer
    simp [usesIdent, found, selects]

@[simp] theorem default_usesSortCtor_int (identifier : Ident) :
    defaultSigEnv.usesSortCtor intId identifier =
      decide (identifier = .symb "Int") := by
  cases isInt : decide (identifier = .symb "Int")
  · unfold usesSortCtor
    cases found : defaultSigEnv.sortProvider identifier with
    | none => rfl
    | some provider =>
        cases provider with
        | core | syntaxOnly index => rfl
        | modeled index =>
            have equal :=
              (default_sortProvider_modeled_iff identifier index).mp found
            have : decide (identifier = .symb "Int") = true := by
              simp [equal]
            simp [isInt] at this
  · have equal : identifier = .symb "Int" := of_decide_eq_true isInt
    subst identifier
    have found :=
      (default_sortProvider_modeled_iff (.symb "Int") intId).mpr rfl
    simp [usesSortCtor, found, selects]

@[simp] theorem default_usesLiteral_int (literal : Literal) :
    defaultSigEnv.usesLiteral intId literal =
      match literal with
      | .num _ => true
      | _ => false := by
  cases literal with
  | num value =>
      have found :=
        (default_literalProvider_modeled_iff (.num value) intId).mpr
          ⟨value, rfl⟩
      simp [usesLiteral, found, selects]
  | str value | bitvec width value | bool value =>
      unfold usesLiteral
      cases found : defaultSigEnv.literalProvider _ with
      | none => rfl
      | some provider =>
          cases provider with
          | core | syntaxOnly index => rfl
          | modeled index =>
              have witness :=
                (default_literalProvider_modeled_iff _ index).mp found
              rcases witness with ⟨value, equal⟩
              contradiction

end SigEnv

end Crush.SMT.Theory
