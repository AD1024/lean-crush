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

@[simp] theorem current_usesIdent_int (identifier : Ident) :
    currentEnv.usesIdent intId identifier = intContainsIdent identifier := by
  cases integer : intContainsIdent identifier
  · unfold usesIdent
    cases found : currentEnv.identProvider identifier with
    | none => rfl
    | some provider =>
        cases provider with
        | core | syntaxOnly index => rfl
        | modeled index =>
            have present :=
              (current_identProvider_modeled_iff identifier index).mp found
            simp [integer] at present
  · have found :=
      (current_identProvider_modeled_iff identifier intId).mpr integer
    simp [usesIdent, found, selects]

@[simp] theorem current_usesSortCtor_int (identifier : Ident) :
    currentEnv.usesSortCtor intId identifier =
      decide (identifier = .symb "Int") := by
  cases isInt : decide (identifier = .symb "Int")
  · unfold usesSortCtor
    cases found : currentEnv.sortProvider identifier with
    | none => rfl
    | some provider =>
        cases provider with
        | core | syntaxOnly index => rfl
        | modeled index =>
            have equal :=
              (current_sortProvider_modeled_iff identifier index).mp found
            have : decide (identifier = .symb "Int") = true := by
              simp [equal]
            simp [isInt] at this
  · have equal : identifier = .symb "Int" := of_decide_eq_true isInt
    subst identifier
    have found :=
      (current_sortProvider_modeled_iff (.symb "Int") intId).mpr rfl
    simp [usesSortCtor, found, selects]

@[simp] theorem current_usesLiteral_int (literal : Literal) :
    currentEnv.usesLiteral intId literal =
      match literal with
      | .num _ => true
      | _ => false := by
  cases literal with
  | num value =>
      have found :=
        (current_literalProvider_modeled_iff (.num value) intId).mpr
          ⟨value, rfl⟩
      simp [usesLiteral, found, selects]
  | str value | bitvec width value | bool value =>
      unfold usesLiteral
      cases found : currentEnv.literalProvider _ with
      | none => rfl
      | some provider =>
          cases provider with
          | core | syntaxOnly index => rfl
          | modeled index =>
              have witness :=
                (current_literalProvider_modeled_iff _ index).mp found
              rcases witness with ⟨value, equal⟩
              contradiction

end SigEnv

end Crush.SMT.Theory
