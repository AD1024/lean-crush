import Crush.Metatheory.SMT.Model
import Crush.Metatheory.SMT.Theory

/-!
# Model extension by derived-symbol graphs

An `ExtraGraph` is disjoint from every encoded source identifier. Consequently
all evaluations already established in the ordinary induced model remain valid
after native derived symbols, such as datatype well-formedness predicates, are
installed.
-/

namespace Crush.Metatheory.SMT

open Defunctionalization.Flattened

variable {symbols : FO.SymbolFamily}

/-! ## Fixed-carrier model-extension laws -/

namespace ModelExt

@[ext] theorem ext {Value : Type} {left right : ModelExt Value}
    (literal : ∀ value, left.literal? value = right.literal? value)
    (apply : ∀ identifier values output,
      left.apply identifier values output ↔
        right.apply identifier values output) : left = right := by
  cases left with
  | mk leftLiteral leftApply =>
    cases right with
    | mk rightLiteral rightApply =>
      have literalEq : leftLiteral = rightLiteral := funext literal
      subst rightLiteral
      have applyEq : leftApply = rightApply := by
        funext identifier values output
        exact propext (apply identifier values output)
      subst rightApply
      rfl

/-- Two extensions contribute disjoint literal and application syntax. -/
structure Disjoint {Value : Type} (left right : ModelExt Value) : Prop where
  literal : ∀ literal leftValue rightValue,
    left.literal? literal = some leftValue →
    right.literal? literal = some rightValue → False
  apply : ∀ identifier values leftOutput rightOutput,
    left.apply identifier values leftOutput →
    right.apply identifier values rightOutput → False

/-- Functionality conditions needed for an extension to preserve a
well-formed model. `base_agree` permits overlap only when both graphs return
the same value. -/
structure WF (base : Crush.SMT.Model)
    (ext : ModelExt base.Value) : Prop extends LiteralWF base ext where
  apply_unique : ∀ identifier values left right,
    ext.apply identifier values left →
    ext.apply identifier values right → left = right
  base_agree : ∀ identifier values baseOutput extraOutput,
    base.apply identifier values baseOutput →
    ext.apply identifier values extraOutput →
      baseOutput = extraOutput

/-- An extension does not interpret any literal or application identifier in
one theory signature. -/
structure InactiveOn {Value : Type} (ext : ModelExt Value)
    (sig : Crush.SMT.Theory.Sig) : Prop where
  literal : ∀ value, sig.containsLiteral value = true →
    ext.literal? value = none
  apply : ∀ identifier, sig.containsIdent identifier = true →
    ∀ values output, ¬ext.apply identifier values output

theorem Disjoint.symm {Value : Type} {left right : ModelExt Value}
    (disjoint : left.Disjoint right) : right.Disjoint left where
  literal := by
    intro literal rightValue leftValue rightPresent leftPresent
    exact disjoint.literal literal leftValue rightValue
      leftPresent rightPresent
  apply := by
    intro identifier values rightOutput leftOutput rightApplied leftApplied
    exact disjoint.apply identifier values leftOutput rightOutput
      leftApplied rightApplied

/-- Empty extension is disjoint from every extension. -/
theorem empty_disjoint {Value : Type} (ext : ModelExt Value) :
    (empty Value).Disjoint ext where
  literal := by simp [empty]
  apply := by simp [empty]

/-- The empty extension satisfies the extension laws for every base model. -/
theorem empty_wf (base : Crush.SMT.Model) : WF base (empty base.Value) where
  literal_typed := by simp [empty]
  apply_unique := by simp [empty]
  base_agree := by simp [empty]

@[simp] theorem empty_union {Value : Type} (ext : ModelExt Value) :
    (empty Value).union ext = ext := by
  apply ModelExt.ext
  · intro literal
    simp [empty, union]
  · intro identifier values output
    simp [empty, union]

@[simp] theorem union_empty {Value : Type} (ext : ModelExt Value) :
    ext.union (empty Value) = ext := by
  apply ModelExt.ext
  · intro literal
    rw [union_literal]
    cases ext.literal? literal <;> rfl
  · intro identifier values output
    simp [empty, union]

theorem union_assoc {Value : Type} (first second third : ModelExt Value) :
    (first.union second).union third = first.union (second.union third) := by
  apply ModelExt.ext
  · intro observation
    simp only [union_literal]
    cases first.literal? observation <;>
      cases second.literal? observation <;> rfl
  · intro identifier values output
    simp only [union_apply]
    constructor
    · rintro ((firstApplied | secondApplied) | thirdApplied)
      · exact Or.inl firstApplied
      · exact Or.inr (Or.inl secondApplied)
      · exact Or.inr (Or.inr thirdApplied)
    · rintro (firstApplied | secondApplied | thirdApplied)
      · exact Or.inl (Or.inl firstApplied)
      · exact Or.inl (Or.inr secondApplied)
      · exact Or.inr thirdApplied

/-- Disjoint extension union is commutative. Without disjointness, literal
union intentionally retains the left interpretation. -/
theorem union_comm {Value : Type} {left right : ModelExt Value}
    (disjoint : left.Disjoint right) : left.union right = right.union left := by
  apply ModelExt.ext
  · intro observation
    rw [union_literal, union_literal]
    cases leftPresent : left.literal? observation with
    | none =>
        cases right.literal? observation <;> rfl
    | some leftValue =>
        have rightAbsent : right.literal? observation = none := by
          cases rightPresent : right.literal? observation with
          | none => rfl
          | some rightValue =>
              exact False.elim (disjoint.literal observation leftValue
                rightValue leftPresent rightPresent)
        rw [rightAbsent]
  · intro identifier values output
    simp only [union_apply]
    exact or_comm

/-- Disjoint well-formed extensions combine without duplicating typing or
functionality proofs. -/
theorem WF.union {base : Crush.SMT.Model}
    {left right : ModelExt base.Value}
    (leftWF : left.WF base) (rightWF : right.WF base)
    (disjoint : left.Disjoint right) : (left.union right).WF base where
  literal_typed := by
    intro literal value present
    rw [union_literal] at present
    split at present
    next leftValue leftPresent =>
      have equal := Option.some.inj present
      subst value
      exact leftWF.literal_typed literal leftValue leftPresent
    next leftAbsent =>
      exact rightWF.literal_typed literal value present
  apply_unique := by
    intro identifier values first second firstApplied secondApplied
    rcases firstApplied with firstLeft | firstRight
    · rcases secondApplied with secondLeft | secondRight
      · exact leftWF.apply_unique identifier values first second
          firstLeft secondLeft
      · exact False.elim
          (disjoint.apply identifier values first second firstLeft secondRight)
    · rcases secondApplied with secondLeft | secondRight
      · exact False.elim
          (disjoint.apply identifier values second first secondLeft firstRight)
      · exact rightWF.apply_unique identifier values first second
          firstRight secondRight
  base_agree := by
    intro identifier values baseOutput extraOutput baseApplied extraApplied
    rcases extraApplied with leftApplied | rightApplied
    · exact leftWF.base_agree identifier values baseOutput extraOutput
        baseApplied leftApplied
    · exact rightWF.base_agree identifier values baseOutput extraOutput
        baseApplied rightApplied

/-- Inactivity is preserved by union when both components are inactive. -/
theorem InactiveOn.union {Value : Type} {left right : ModelExt Value}
    {sig : Crush.SMT.Theory.Sig}
    (leftOff : left.InactiveOn sig) (rightOff : right.InactiveOn sig) :
    (left.union right).InactiveOn sig where
  literal := by
    intro literal present
    change (match left.literal? literal with
      | some leftValue => some leftValue
      | none => right.literal? literal) = none
    rw [leftOff.literal literal present,
      rightOff.literal literal present]
  apply := by
    intro identifier present values output applied
    rcases applied with leftApplied | rightApplied
    · exact leftOff.apply identifier present values output leftApplied
    · exact rightOff.apply identifier present values output rightApplied

end ModelExt

end Crush.Metatheory.SMT

namespace Crush.SMT.Model

/-- Model well-formedness is preserved by a well-formed extension. -/
theorem WF.withExt {base : Model} (baseWF : base.WF)
    {ext : Crush.Metatheory.SMT.ModelExt base.Value}
    (extWF : Crush.Metatheory.SMT.ModelExt.WF base ext) :
    (base.withExt ext extWF.toLiteralWF).WF where
  bool_exhaustive := baseWF.bool_exhaustive
  apply_unique := by
    intro identifier values left right leftApplied rightApplied
    rcases leftApplied with leftBase | leftExtra
    · rcases rightApplied with rightBase | rightExtra
      · exact baseWF.apply_unique identifier values left right
          leftBase rightBase
      · exact extWF.base_agree identifier values left right
          leftBase rightExtra
    · rcases rightApplied with rightBase | rightExtra
      · exact (extWF.base_agree identifier values right left
          rightBase leftExtra).symm
      · exact extWF.apply_unique identifier values left right
          leftExtra rightExtra

/-- Adding the empty extension leaves a model unchanged. -/
@[simp] theorem withExt_empty (base : Model) :
    base.withExt
        (Crush.Metatheory.SMT.ModelExt.empty base.Value)
        (Crush.Metatheory.SMT.ModelExt.empty_wf base).toLiteralWF = base := by
  cases base
  simp [withExt, Crush.Metatheory.SMT.ModelExt.empty]

end Crush.SMT.Model

namespace Crush.Metatheory.SMT

variable {symbols : FO.SymbolFamily}

namespace ExtraGraph

/-- Existing functionality proofs for `modelWith` discharge exactly the
generic extension laws. This adapter reuses those proof artifacts instead of
re-proving graph uniqueness for each native component. -/
theorem toExt_wf {encoding : Encoding symbols} {target : FO.FamilyModel symbols}
    (extra : ExtraGraph encoding target)
    (functional : Crush.SMT.ApplyUnique (modelWith encoding target extra)) :
    (extra.toExt).WF (model encoding target) where
  toLiteralWF := extra.toExt_literalWF
  apply_unique := by
    intro identifier values left right leftApplied rightApplied
    exact functional identifier values left right
      (Or.inr leftApplied) (Or.inr rightApplied)
  base_agree := by
    intro identifier values baseOutput extraOutput baseApplied extraApplied
    exact functional identifier values baseOutput extraOutput
      (Or.inl baseApplied) (Or.inr extraApplied)

/-- The compatibility constructor is definitionally the generic constructor. -/
theorem modelWith_eq_withExt {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols} (extra : ExtraGraph encoding target) :
    modelWith encoding target extra =
      (model encoding target).withExt extra.toExt
        extra.toExt_literalWF := by
  rfl

end ExtraGraph

namespace ModelExt

/-- A theory reduct is unchanged, up to the identity carrier isomorphism, by
an extension inactive on that theory's signature. -/
def reductIso {base : Crush.SMT.Model} {ext : ModelExt base.Value}
    (wf : ext.LiteralWF base) {sig : Crush.SMT.Theory.Sig}
    (inactive : ext.InactiveOn sig) :
    Struct.Iso (Model.reduct base sig)
      (Model.reduct (base.withExt ext wf) sig) where
  to := id
  inv := id
  to_inv := by simp
  inv_to := by simp
  inSort := by intro sort present value; rfl
  bool := by intro; rfl
  literal := by
    intro literal present
    cases literal with
    | bool value => rfl
    | num value =>
        change base.literal (.num value) =
          match ext.literal? (.num value) with
          | some output => output
          | none => base.literal (.num value)
        rw [inactive.literal (.num value) present]
    | str value =>
        change base.literal (.str value) =
          match ext.literal? (.str value) with
          | some output => output
          | none => base.literal (.str value)
        rw [inactive.literal (.str value) present]
    | bitvec width value =>
        change base.literal (.bitvec width value) =
          match ext.literal? (.bitvec width value) with
          | some output => output
          | none => base.literal (.bitvec width value)
        rw [inactive.literal (.bitvec width value) present]
  apply := by
    intro identifier present values output
    change base.apply identifier values output ↔
      base.apply identifier (values.map id) (id output) ∨
        ext.apply identifier (values.map id) (id output)
    simp only [List.map_id_fun, id_eq]
    constructor
    · exact Or.inl
    · intro applied
      rcases applied with baseApplied | extraApplied
      · exact baseApplied
      · exact False.elim
          (inactive.apply identifier present values output extraApplied)

/-- Every isomorphism-closed theory remains true after an extension inactive
on its signature. -/
theorem theory {base : Crush.SMT.Model} {ext : ModelExt base.Value}
    (wf : ext.LiteralWF base) {sig : Crush.SMT.Theory.Sig}
    (inactive : ext.InactiveOn sig)
    (theory : Crush.Metatheory.SMT.Theory sig)
    (models : theory.Models (Model.reduct base sig)) :
    theory.Models
      (Model.reduct (base.withExt ext wf) sig) :=
  theory.iso_closed (reductIso wf inactive) models

/-! ## Fixed-carrier evaluation agreement -/

/-- Literal value selected by an extension, falling back to the base model. -/
def resolve (base : Crush.SMT.Model) (ext : ModelExt base.Value)
    (literal : Crush.SMT.Literal) : base.Value :=
  match ext.literal? literal with
  | some value => value
  | none => base.literal literal

mutual
  /-- Two extensions agree on every model observation used by one term.
Logical built-ins use dedicated evaluation rules, so application-graph
agreement is required only for identifiers admitted by `NotBuiltin`. -/
  inductive AgreeOn {base : Crush.SMT.Model}
      (left right : ModelExt base.Value) : Crush.SMT.Term → Prop where
    | bool (value : Bool) : AgreeOn left right (.lit (.bool value))
    | literal {literal : Crush.SMT.Literal} :
        resolve base left literal = resolve base right literal →
          AgreeOn left right (.lit literal)
    | bvar (index : Nat) : AgreeOn left right (.bvar index)
    | app {identifier arguments} :
        AgreeList left right arguments.toList →
        (Crush.SMT.NotBuiltin identifier →
          ∀ values output,
            (base.apply identifier values output ∨
              left.apply identifier values output) ↔
            (base.apply identifier values output ∨
              right.apply identifier values output)) →
          AgreeOn left right (.app identifier arguments)
    | letE {bindings body} :
        AgreeList left right (bindings.toList.map (·.2)) →
        AgreeOn left right body → AgreeOn left right (.letE bindings body)
    | forallE {binders body} : AgreeOn left right body →
        AgreeOn left right (.forallE binders body)
    | existsE {binders body} : AgreeOn left right body →
        AgreeOn left right (.existsE binders body)
    | lam {binders body} : AgreeOn left right body →
        AgreeOn left right (.lam binders body)
    | annot {term attributes} : AgreeOn left right term →
        AgreeOn left right (.annot term attributes)

  /-- Pointwise observation agreement for a term list. -/
  inductive AgreeList {base : Crush.SMT.Model}
      (left right : ModelExt base.Value) : List Crush.SMT.Term → Prop where
    | nil : AgreeList left right []
    | cons {term terms} : AgreeOn left right term →
        AgreeList left right terms →
          AgreeList left right (term :: terms)
end

namespace AgreeOn

/-- Agreement for a logical built-in follows from argument agreement because
its semantics does not consult the model's application graph. -/
theorem builtin {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} {identifier arguments}
    (argumentsAgree : AgreeList left right arguments.toList)
    (logical : ¬Crush.SMT.NotBuiltin identifier) :
    AgreeOn left right (.app identifier arguments) :=
  .app argumentsAgree (fun symbol => False.elim (logical symbol))

theorem app_parts {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} {identifier arguments}
    (agree : AgreeOn left right (.app identifier arguments)) :
    AgreeList left right arguments.toList ∧
      (Crush.SMT.NotBuiltin identifier →
        ∀ values output,
          (base.apply identifier values output ∨
            left.apply identifier values output) ↔
          (base.apply identifier values output ∨
            right.apply identifier values output)) := by
  cases agree with
  | app arguments graph => exact ⟨arguments, graph⟩

theorem let_parts {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} {bindings body}
    (agree : AgreeOn left right (.letE bindings body)) :
    AgreeList left right (bindings.toList.map (·.2)) ∧
      AgreeOn left right body := by
  cases agree with
  | letE bindings body => exact ⟨bindings, body⟩

theorem forall_body {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} {binders body}
    (agree : AgreeOn left right (.forallE binders body)) :
    AgreeOn left right body := by
  cases agree with
  | forallE body => exact body

theorem exists_body {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} {binders body}
    (agree : AgreeOn left right (.existsE binders body)) :
    AgreeOn left right body := by
  cases agree with
  | existsE body => exact body

theorem annot_body {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} {term attributes}
    (agree : AgreeOn left right (.annot term attributes)) :
    AgreeOn left right term := by
  cases agree with
  | annot body => exact body

end AgreeOn

namespace AgreeList

theorem cons_parts {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} {term terms}
    (agree : AgreeList left right (term :: terms)) :
    AgreeOn left right term ∧ AgreeList left right terms := by
  cases agree with
  | cons head tail => exact ⟨head, tail⟩

end AgreeList

/-- Sort-typing evidence transports between extensions of one base model. -/
theorem valuesTyped_transport {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} (leftWF : left.LiteralWF base)
    (rightWF : right.LiteralWF base) {sorts : List Crush.SMT.SSort}
    {values : List base.Value} :
    Crush.SMT.ValuesTyped (base.withExt left leftWF) sorts values →
      Crush.SMT.ValuesTyped (base.withExt right rightWF) sorts values
  | .nil => .nil
  | .cons head tail =>
      .cons (by simpa only [Crush.SMT.Model.withExt_inSort] using head)
        (valuesTyped_transport leftWF rightWF tail)

/-- Boolean-list evidence transports because extensions retain the base
Boolean interpretation. -/
theorem boolValues_transport {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} (leftWF : left.LiteralWF base)
    (rightWF : right.LiteralWF base) {values : List base.Value}
    {booleans : List Bool} :
    Crush.SMT.BoolValues (base.withExt left leftWF) values booleans →
      Crush.SMT.BoolValues (base.withExt right rightWF) values booleans
  | .nil => .nil
  | @Crush.SMT.BoolValues.cons _ value values booleans tail => by
      change Crush.SMT.BoolValues (base.withExt right rightWF)
        (base.bool value :: values) (value :: booleans)
      exact .cons (boolValues_transport leftWF rightWF tail)

/-- Evaluation depends only on the literal and application observations used
by the term. Both models extend one base model, so environments and results
share one carrier and require no casts. -/
theorem eval_transport {base : Crush.SMT.Model}
    {left right : ModelExt base.Value} (leftWF : left.LiteralWF base)
    (rightWF : right.LiteralWF base) {environment : List base.Value}
    {term : Crush.SMT.Term} {value : base.Value}
    (agree : AgreeOn left right term)
    (evaluated : Crush.SMT.Eval (base.withExt left leftWF)
      environment term value) :
    Crush.SMT.Eval (base.withExt right rightWF) environment term value := by
  exact Crush.SMT.Eval.rec (model := base.withExt left leftWF)
    (motive_1 := fun environment term value _ =>
      AgreeOn left right term →
        Crush.SMT.Eval (base.withExt right rightWF)
          environment term value)
    (motive_2 := fun environment terms values _ =>
      AgreeList left right terms →
        Crush.SMT.EvalList (base.withExt right rightWF)
          environment terms values)
    (boolLit := by
      intro environment boolean agreement
      exact .boolLit boolean)
    (literal := by
      intro environment literal notBool agreement
      cases agreement with
      | bool boolean => exact False.elim (notBool boolean rfl)
      | literal equal =>
          have literalEq :
              (base.withExt left leftWF).literal literal =
                (base.withExt right rightWF).literal literal := by
            change resolve base left literal = resolve base right literal
            exact equal
          rw [literalEq]
          exact .literal literal notBool)
    (bvar := by
      intro environment index output lookup agreement
      exact .bvar lookup)
    (symbol := by
      intro environment identifier arguments values output notBuiltin
        argumentsEval applied argumentsIH agreement
      rcases agreement.app_parts with ⟨argumentsAgree, graphAgree⟩
      apply Crush.SMT.Eval.symbol notBuiltin (argumentsIH argumentsAgree)
      change base.apply identifier values output ∨
        right.apply identifier values output
      change base.apply identifier values output ∨
        left.apply identifier values output at applied
      exact (graphAgree notBuiltin values output).mp applied)
    (eqTrue := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval equal leftIH rightIH agreement
      have leftAgree := agreement.app_parts.1.cons_parts.1
      have rightAgree := agreement.app_parts.1.cons_parts.2.cons_parts.1
      simpa only [Crush.SMT.Model.withExt_bool] using Crush.SMT.Eval.eqTrue
        (leftIH leftAgree) (rightIH rightAgree) equal)
    (eqFalse := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval unequal leftIH rightIH agreement
      have leftAgree := agreement.app_parts.1.cons_parts.1
      have rightAgree := agreement.app_parts.1.cons_parts.2.cons_parts.1
      simpa only [Crush.SMT.Model.withExt_bool] using Crush.SMT.Eval.eqFalse
        (leftIH leftAgree) (rightIH rightAgree) unequal)
    (not := by
      intro environment body boolean bodyEval bodyIH agreement
      have bodyAgree := agreement.app_parts.1.cons_parts.1
      simpa only [Crush.SMT.Model.withExt_bool] using
        Crush.SMT.Eval.not (bodyIH bodyAgree))
    (imp := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval leftIH rightIH agreement
      have leftAgree := agreement.app_parts.1.cons_parts.1
      have rightAgree := agreement.app_parts.1.cons_parts.2.cons_parts.1
      simpa only [Crush.SMT.Model.withExt_bool] using Crush.SMT.Eval.imp
        (leftIH leftAgree) (rightIH rightAgree))
    (and := by
      intro environment arguments values booleans argumentsEval boolValues
        argumentsIH agreement
      simpa only [Crush.SMT.Model.withExt_bool] using Crush.SMT.Eval.and
        (argumentsIH agreement.app_parts.1)
        (boolValues_transport leftWF rightWF boolValues))
    (or := by
      intro environment arguments values booleans argumentsEval boolValues
        argumentsIH agreement
      simpa only [Crush.SMT.Model.withExt_bool] using Crush.SMT.Eval.or
        (argumentsIH agreement.app_parts.1)
        (boolValues_transport leftWF rightWF boolValues))
    (letE := by
      intro environment bindings body values output valuesEval bodyEval
        valuesIH bodyIH agreement
      exact .letE (valuesIH agreement.let_parts.1)
        (bodyIH agreement.let_parts.2))
    (forallTrue := by
      intro environment binders body every everyIH agreement
      apply Crush.SMT.Eval.forallTrue
      intro values typed
      exact everyIH values
        (valuesTyped_transport rightWF leftWF typed) agreement.forall_body)
    (forallFalse := by
      intro environment binders body values typed bodyEval bodyIH agreement
      exact .forallFalse (valuesTyped_transport leftWF rightWF typed)
        (bodyIH agreement.forall_body))
    (existsTrue := by
      intro environment binders body values typed bodyEval bodyIH agreement
      exact .existsTrue (valuesTyped_transport leftWF rightWF typed)
        (bodyIH agreement.exists_body))
    (existsFalse := by
      intro environment binders body every everyIH agreement
      apply Crush.SMT.Eval.existsFalse
      intro values typed
      exact everyIH values
        (valuesTyped_transport rightWF leftWF typed) agreement.exists_body)
    (annot := by
      intro environment term attributes output bodyEval bodyIH agreement
      exact .annot (bodyIH agreement.annot_body))
    (nil := by
      intro environment agreement
      exact .nil)
    (cons := by
      intro environment term terms output outputs termEval termsEval
        termIH termsIH agreement
      cases agreement with
      | cons termAgree termsAgree =>
          exact .cons (termIH termAgree) (termsIH termsAgree))
    evaluated agree

end ModelExt

/-- Sort-typing witnesses are unchanged because graph extension changes only
`apply`. -/
theorem valuesTyped_with_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    {sorts : List Crush.SMT.SSort} {values : List (Value target)} :
    Crush.SMT.ValuesTyped (model encoding target) sorts values →
      Crush.SMT.ValuesTyped (modelWith encoding target extra) sorts values
  | .nil => .nil
  | .cons typed rest => .cons (by simpa only [model_inSort, modelWith_inSort] using typed)
      (valuesTyped_with_extra encoding target extra rest)

/-- The inverse conversion is needed beneath universal definition clauses. -/
theorem valuesTyped_without_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    {sorts : List Crush.SMT.SSort} {values : List (Value target)} :
    Crush.SMT.ValuesTyped (modelWith encoding target extra) sorts values →
      Crush.SMT.ValuesTyped (model encoding target) sorts values
  | .nil => .nil
  | .cons typed rest => .cons (by simpa only [model_inSort, modelWith_inSort] using typed)
      (valuesTyped_without_extra encoding target extra rest)

/-- At an identifier absent from the extra graph, application is exactly the
ordinary induced-model application. -/
theorem applies_iff_without_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (identifier : Crush.SMT.Ident)
    (inactive : ∀ values output, ¬extra.apply identifier values output)
    (values : List (Value target)) (output : Value target) :
    (modelWith encoding target extra).apply identifier values output ↔
      (model encoding target).apply identifier values output := by
  constructor
  · rintro (ordinary | derived)
    · exact ordinary
    · exact False.elim (inactive values output derived)
  · exact Or.inl

/-- Totality, typing, and uniqueness of an inactive symbol survive graph
extension. -/
theorem symbolHasType_with_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (identifier : Crush.SMT.Ident)
    (inactive : ∀ values output, ¬extra.apply identifier values output)
    {arguments : List Crush.SMT.SSort} {result : Crush.SMT.SSort}
    (typed : Crush.SMT.SymbolHasType (model encoding target)
      identifier arguments result) :
    Crush.SMT.SymbolHasType (modelWith encoding target extra)
      identifier arguments result := by
  intro values valuesTyped
  have oldTyped := valuesTyped_without_extra encoding target extra valuesTyped
  obtain ⟨output, outputTyped, applied, unique⟩ := typed values oldTyped
  refine ⟨output, by simpa only [model_inSort, modelWith_inSort] using outputTyped,
    (applies_iff_without_extra encoding target extra identifier inactive
      values output).mpr applied, ?_⟩
  intro other otherApplied
  exact unique other ((applies_iff_without_extra encoding target extra
    identifier inactive values other).mp otherApplied)

/-- Constructor application is unchanged when its constructor name is absent
from the extra graph. -/
theorem ctorApplies_with_extra_iff (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (ctor : Crush.SMT.CtorDecl)
    (inactive : ∀ values output,
      ¬extra.apply (.symb ctor.name) values output)
    (values : List (Value target)) (output : Value target) :
    Crush.SMT.CtorApplies (modelWith encoding target extra) ctor values output ↔
      Crush.SMT.CtorApplies (model encoding target) ctor values output := by
  constructor <;> intro applied
  · exact ⟨valuesTyped_without_extra encoding target extra applied.1,
      (applies_iff_without_extra encoding target extra (.symb ctor.name)
        inactive values output).mp applied.2⟩
  · exact ⟨valuesTyped_with_extra encoding target extra applied.1,
      (applies_iff_without_extra encoding target extra (.symb ctor.name)
        inactive values output).mpr applied.2⟩

/-- An extra graph is disjoint from every constructor, selector, and tester
identifier declared by an SMT datatype command. -/
def ExtraGraph.InactiveOnDatatypes {encoding : Encoding symbols}
    {target : FO.FamilyModel symbols} (extra : ExtraGraph encoding target)
    (datatypes : Array (String × Nat × Crush.SMT.DatatypeDecl)) : Prop :=
  ∀ identifier ∈ Crush.SMT.datatypeSymbols datatypes,
    ∀ values output, ¬extra.apply identifier values output

namespace ExtraGraph.InactiveOnDatatypes

theorem ctor {encoding : Encoding symbols} {target : FO.FamilyModel symbols}
    {extra : ExtraGraph encoding target} {datatypes}
    (inactive : extra.InactiveOnDatatypes datatypes)
    {sort : Crush.SMT.SSort} {ctor : Crush.SMT.CtorDecl}
    (member : (sort, ctor) ∈ Crush.SMT.datatypeCtors datatypes) :
    ∀ values output, ¬extra.apply (.symb ctor.name) values output := by
  apply inactive
  simp only [Crush.SMT.datatypeSymbols, List.mem_flatMap]
  exact ⟨(sort, ctor), member, by simp⟩

theorem test {encoding : Encoding symbols} {target : FO.FamilyModel symbols}
    {extra : ExtraGraph encoding target} {datatypes}
    (inactive : extra.InactiveOnDatatypes datatypes)
    {sort : Crush.SMT.SSort} {ctor : Crush.SMT.CtorDecl}
    (member : (sort, ctor) ∈ Crush.SMT.datatypeCtors datatypes) :
    ∀ values output, ¬extra.apply ctor.tester values output := by
  apply inactive
  simp only [Crush.SMT.datatypeSymbols, List.mem_flatMap]
  exact ⟨(sort, ctor), member, by simp⟩

theorem sel {encoding : Encoding symbols} {target : FO.FamilyModel symbols}
    {extra : ExtraGraph encoding target} {datatypes}
    (inactive : extra.InactiveOnDatatypes datatypes)
    {sort : Crush.SMT.SSort} {ctor : Crush.SMT.CtorDecl}
    (member : (sort, ctor) ∈ Crush.SMT.datatypeCtors datatypes)
    {index : Nat} {name : String} {resultSort : Crush.SMT.SSort}
    (lookup : ctor.selDecls[index]? = some (name, resultSort)) :
    ∀ values output, ¬extra.apply (.symb name) values output := by
  apply inactive
  simp only [Crush.SMT.datatypeSymbols, List.mem_flatMap]
  refine ⟨(sort, ctor), member, ?_⟩
  simp only [List.mem_cons, List.mem_map]
  right
  right
  have bounds := (Array.getElem?_eq_some_iff.mp lookup).1
  have equal := (Array.getElem?_eq_some_iff.mp lookup).2
  refine ⟨ctor.selDecls[index], ?_, ?_⟩
  · exact Array.mem_toList_iff.mpr (Array.getElem_mem bounds)
  · simpa using congrArg Prod.fst equal

end ExtraGraph.InactiveOnDatatypes

/-- Native datatype semantics are stable under any graph extension disjoint
from the command's own symbols. -/
theorem datatypesHold_with_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (datatypes : Array (String × Nat × Crush.SMT.DatatypeDecl))
    (inactive : extra.InactiveOnDatatypes datatypes)
    (holds : Crush.SMT.DatatypesHold (model encoding target) datatypes) :
    Crush.SMT.DatatypesHold (modelWith encoding target extra) datatypes := by
  rcases holds with
    ⟨supported, laws, disjoint, exhaustive, testDisjoint, rank, decreases⟩
  refine ⟨supported, ?_, ?_, ?_, ?_, rank, ?_⟩
  · intro sort ctor member
    have old := laws sort ctor member
    have ctorOff := inactive.ctor member
    refine ⟨⟨symbolHasType_with_extra encoding target extra (.symb ctor.name)
        ctorOff old.1.1, ?_⟩, ?_, ?_⟩
    · intro leftArgs rightArgs leftResult rightResult leftApply rightApply equal
      exact old.1.2 _ _ _ _
        ((ctorApplies_with_extra_iff encoding target extra ctor ctorOff _ _).mp
          leftApply)
        ((ctorApplies_with_extra_iff encoding target extra ctor ctorOff _ _).mp
          rightApply) equal
    · intro index name resultSort lookup
      have oldSel := old.2.1 index name resultSort lookup
      have selOff := inactive.sel member lookup
      refine ⟨symbolHasType_with_extra encoding target extra (.symb name)
          selOff oldSel.1, ?_⟩
      intro arguments result selected ctorApplied selectedAt
      have oldCtor := (ctorApplies_with_extra_iff encoding target extra ctor
        ctorOff arguments result).mp ctorApplied
      exact (applies_iff_without_extra encoding target extra (.symb name)
        selOff [result] selected).mpr
          (oldSel.2 arguments result selected oldCtor selectedAt)
    · have testOff := inactive.test member
      refine ⟨symbolHasType_with_extra encoding target extra ctor.tester
          testOff old.2.2.1, ?_⟩
      intro arguments result ctorApplied
      have oldCtor := (ctorApplies_with_extra_iff encoding target extra ctor
        ctorOff arguments result).mp ctorApplied
      exact (applies_iff_without_extra encoding target extra ctor.tester
        testOff [result] ((model encoding target).bool true)).mpr
          (old.2.2.2 arguments result oldCtor)
  · intro leftSort leftCtor rightSort rightCtor leftMem rightMem different
      leftArgs leftResult rightArgs rightResult leftApply rightApply
    exact disjoint leftSort leftCtor rightSort rightCtor leftMem rightMem different
      leftArgs leftResult rightArgs rightResult
      ((ctorApplies_with_extra_iff encoding target extra leftCtor
        (inactive.ctor leftMem) leftArgs leftResult).mp leftApply)
      ((ctorApplies_with_extra_iff encoding target extra rightCtor
        (inactive.ctor rightMem) rightArgs rightResult).mp rightApply)
  · intro name arity datatype member value typed
    have oldTyped : (model encoding target).inSort
        (Crush.SMT.datatypeSort name) value := by
      simpa only [model_inSort, modelWith_inSort] using typed
    obtain ⟨ctor, ctorMem, arguments, oldApply⟩ :=
      exhaustive name arity datatype member value oldTyped
    have pairMem : (Crush.SMT.datatypeSort name, ctor) ∈
        Crush.SMT.datatypeCtors datatypes := by
      simp only [Crush.SMT.datatypeCtors, List.mem_flatMap, List.mem_map]
      exact ⟨(name, arity, datatype), member, ctor, ctorMem, rfl⟩
    exact ⟨ctor, ctorMem, arguments,
      (ctorApplies_with_extra_iff encoding target extra ctor
        (inactive.ctor pairMem) arguments value).mpr oldApply⟩
  · intro sort leftCtor rightCtor leftMem rightMem different arguments result
      applied
    have oldApply := (ctorApplies_with_extra_iff encoding target extra rightCtor
      (inactive.ctor rightMem) arguments result).mp applied
    exact (applies_iff_without_extra encoding target extra leftCtor.tester
      (inactive.test leftMem) [result] ((model encoding target).bool false)).mpr
        (testDisjoint sort leftCtor rightCtor leftMem rightMem different
          arguments result oldApply)
  · intro sort ctor member arguments result applied index fieldSort fieldValue
      sortAt valueAt recursive
    exact decreases sort ctor member arguments result
      ((ctorApplies_with_extra_iff encoding target extra ctor
        (inactive.ctor member) arguments result).mp applied)
      index fieldSort fieldValue sortAt valueAt recursive

/-- A valid native datatype declaration remains valid in the combined model. -/
theorem datatypeCommand_with_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    (datatypes : Array (String × Nat × Crush.SMT.DatatypeDecl))
    (inactive : extra.InactiveOnDatatypes datatypes)
    (valid : (model encoding target).SatisfiesCommand (.declDatatypes datatypes)) :
    (modelWith encoding target extra).SatisfiesCommand
      (.declDatatypes datatypes) :=
  datatypesHold_with_extra encoding target extra datatypes inactive valid

/-- Boolean-list witnesses are likewise independent of the symbol graph. -/
theorem boolValues_with_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    {values : List (Value target)} {booleans : List Bool} :
  Crush.SMT.BoolValues (model encoding target) values booleans →
      Crush.SMT.BoolValues (modelWith encoding target extra) values booleans
  | .nil => .nil
  | @Crush.SMT.BoolValues.cons _ value values booleans rest => by
      have equal : (model encoding target).bool value =
          (modelWith encoding target extra).bool value := by simp
      rw [equal]
      exact .cons (boolValues_with_extra encoding target extra rest)

/-- Extending the graph preserves evaluation whenever the base and extension
agree on every literal and application observation used by the term. -/
theorem eval_with_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    {environment : List (Value target)} {term : Crush.SMT.Term}
    {value : Value target}
    (agree : ModelExt.AgreeOn (base := model encoding target)
      (ModelExt.empty (Value target)) extra.toExt term)
    (evaluated : Crush.SMT.Eval (model encoding target) environment term value) :
    Crush.SMT.Eval (modelWith encoding target extra) environment term value := by
  exact Crush.SMT.Eval.rec (model := model encoding target)
    (motive_1 := fun environment term value _ =>
      ModelExt.AgreeOn (base := model encoding target)
        (ModelExt.empty (Value target)) extra.toExt term →
        Crush.SMT.Eval (modelWith encoding target extra) environment term value)
    (motive_2 := fun environment terms values _ =>
      ModelExt.AgreeList (base := model encoding target)
        (ModelExt.empty (Value target)) extra.toExt terms →
        Crush.SMT.EvalList (modelWith encoding target extra)
          environment terms values)
    (boolLit := by intros; exact .boolLit _)
    (literal := by
      intro environment literal notBool agreement
      cases agreement with
      | bool value => exact False.elim (notBool value rfl)
      | literal equal =>
          have literalEq :
              (model encoding target).literal literal =
                (modelWith encoding target extra).literal literal := by
            change ModelExt.resolve (model encoding target)
              (ModelExt.empty (Value target)) literal =
                ModelExt.resolve (model encoding target) extra.toExt literal
              at equal
            simpa [ModelExt.resolve, ModelExt.empty, modelWith,
              ExtraGraph.toExt] using equal
          rw [literalEq]
          exact .literal literal notBool)
    (bvar := by intros; exact .bvar (by assumption))
    (symbol := by
      intro environment identifier arguments values output notBuiltin
        argumentsEval applied argumentsIH agreement
      rcases agreement.app_parts with ⟨argumentsAgree, graphAgree⟩
      apply Crush.SMT.Eval.symbol notBuiltin (argumentsIH argumentsAgree)
      change (model encoding target).apply identifier values output ∨
        extra.apply identifier values output
      exact (graphAgree notBuiltin values output).mp (Or.inl applied))
    (eqTrue := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval equal leftIH rightIH agreement
      have leftAgree := agreement.app_parts.1.cons_parts.1
      have rightAgree := agreement.app_parts.1.cons_parts.2.cons_parts.1
      simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.eqTrue
        (leftIH leftAgree) (rightIH rightAgree) equal)
    (eqFalse := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval unequal leftIH rightIH agreement
      have leftAgree := agreement.app_parts.1.cons_parts.1
      have rightAgree := agreement.app_parts.1.cons_parts.2.cons_parts.1
      simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.eqFalse
        (leftIH leftAgree) (rightIH rightAgree) unequal)
    (not := by
      intro environment body value bodyEval bodyIH agreement
      have bodyAgree := agreement.app_parts.1.cons_parts.1
      simpa only [model_bool, modelWith_bool] using
        Crush.SMT.Eval.not (bodyIH bodyAgree))
    (imp := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval leftIH rightIH agreement
      have leftAgree := agreement.app_parts.1.cons_parts.1
      have rightAgree := agreement.app_parts.1.cons_parts.2.cons_parts.1
      simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.imp
        (leftIH leftAgree) (rightIH rightAgree))
    (and := by
      intro environment arguments values booleans argumentsEval boolValues
        argumentsIH agreement
      simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.and
        (argumentsIH agreement.app_parts.1)
        (boolValues_with_extra encoding target extra boolValues))
    (or := by
      intro environment arguments values booleans argumentsEval boolValues
        argumentsIH agreement
      simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.or
        (argumentsIH agreement.app_parts.1)
        (boolValues_with_extra encoding target extra boolValues))
    (letE := by
      intro environment bindings body values output valuesEval bodyEval
        valuesIH bodyIH agreement
      exact .letE (valuesIH agreement.let_parts.1)
        (bodyIH agreement.let_parts.2))
    (forallTrue := by
      intro environment binders body every everyIH agreement
      apply Crush.SMT.Eval.forallTrue
      intro values typed
      exact everyIH values
        (valuesTyped_without_extra encoding target extra typed)
        agreement.forall_body)
    (forallFalse := by
      intro environment binders body values typed bodyEval bodyIH agreement
      exact .forallFalse (valuesTyped_with_extra encoding target extra typed)
        (bodyIH agreement.forall_body))
    (existsTrue := by
      intro environment binders body values typed bodyEval bodyIH agreement
      exact .existsTrue (valuesTyped_with_extra encoding target extra typed)
        (bodyIH agreement.exists_body))
    (existsFalse := by
      intro environment binders body every everyIH agreement
      apply Crush.SMT.Eval.existsFalse
      intro values typed
      exact everyIH values
        (valuesTyped_without_extra encoding target extra typed)
        agreement.exists_body)
    (annot := by
      intro environment term attributes value bodyEval bodyIH agreement
      exact .annot (bodyIH agreement.annot_body))
    (nil := by intros; exact .nil)
    (cons := by
      intro environment term terms value values termEval termsEval termIH termsIH
        agreement
      cases agreement with
      | cons termAgree termsAgree =>
          exact .cons (termIH termAgree) (termsIH termsAgree))
    evaluated agree

end Crush.Metatheory.SMT
