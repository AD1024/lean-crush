import Crush.Metatheory.SMT.Model

/-!
# Preservation under derived-symbol graph extension

An `ExtraGraph` is disjoint from every encoded source identifier. Consequently
all evaluations already established in the ordinary induced model remain valid
after native derived symbols, such as datatype well-formedness predicates, are
installed.
-/

namespace Crush.Metatheory.SMT

open Defunctionalization.Flattened

variable {symbols : FO.SymbolFamily}

mutual
  /-- Terms whose literals are all Boolean. The intrinsic FO encoder has this
  property: non-Boolean constants are represented by typed symbols. Keeping the
  property explicit lets native components reinterpret SMT numerals without
  affecting already-encoded FO terms. -/
  inductive LiteralFree : Crush.SMT.Term → Prop where
    | bool (value : Bool) : LiteralFree (.lit (.bool value))
    | bvar (index : Nat) : LiteralFree (.bvar index)
    | app {identifier arguments} :
        LiteralFreeList arguments.toList →
        LiteralFree (.app identifier arguments)
    | letE {bindings body} :
        LiteralFreeList (bindings.toList.map (·.2)) →
        LiteralFree body → LiteralFree (.letE bindings body)
    | forallE {binders body} : LiteralFree body →
        LiteralFree (.forallE binders body)
    | existsE {binders body} : LiteralFree body →
        LiteralFree (.existsE binders body)
    | lam {binders body} : LiteralFree body → LiteralFree (.lam binders body)
    | annot {term attributes} : LiteralFree term →
        LiteralFree (.annot term attributes)

  inductive LiteralFreeList : List Crush.SMT.Term → Prop where
    | nil : LiteralFreeList []
    | cons {term : Crush.SMT.Term} {terms : List Crush.SMT.Term} :
        LiteralFree term → LiteralFreeList terms →
        LiteralFreeList (term :: terms)
end

namespace LiteralFree

theorem app_args {identifier arguments}
    (free : LiteralFree (.app identifier arguments)) :
    LiteralFreeList arguments.toList := by
  cases free with
  | app arguments => exact arguments

theorem let_parts {bindings body}
    (free : LiteralFree (.letE bindings body)) :
    LiteralFreeList (bindings.toList.map (·.2)) ∧
      LiteralFree body := by
  cases free with
  | letE bindings body => exact ⟨bindings, body⟩

theorem forall_body {binders body}
    (free : LiteralFree (.forallE binders body)) : LiteralFree body := by
  cases free with
  | forallE body => exact body

theorem exists_body {binders body}
    (free : LiteralFree (.existsE binders body)) : LiteralFree body := by
  cases free with
  | existsE body => exact body

theorem annot_body {term attributes}
    (free : LiteralFree (.annot term attributes)) : LiteralFree term := by
  cases free with
  | annot body => exact body

end LiteralFree

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

/-- At an identifier not owned by the extra graph, application is exactly the
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
identifier owned by a native datatype command. -/
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
  ⟨valid.1, datatypesHold_with_extra encoding target extra datatypes
    inactive valid.2⟩

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

/-- Extending the graph preserves evaluation of a term that contains no
non-Boolean literals, even when the extension gives numerals a new
interpretation. -/
theorem eval_with_extra (encoding : Encoding symbols)
    (target : FO.FamilyModel symbols) (extra : ExtraGraph encoding target)
    {environment : List (Value target)} {term : Crush.SMT.Term}
    {value : Value target}
    (free : LiteralFree term)
    (evaluated : Crush.SMT.Eval (model encoding target) environment term value) :
    Crush.SMT.Eval (modelWith encoding target extra) environment term value := by
  exact Crush.SMT.Eval.rec (model := model encoding target)
    (motive_1 := fun environment term value _ =>
      LiteralFree term →
        Crush.SMT.Eval (modelWith encoding target extra) environment term value)
    (motive_2 := fun environment terms values _ =>
      LiteralFreeList terms →
        Crush.SMT.EvalList (modelWith encoding target extra)
          environment terms values)
    (boolLit := by intros; exact .boolLit _)
    (literal := by
      intro environment literal notBool free
      cases free with
      | bool value => exact False.elim (notBool value rfl))
    (bvar := by intros; exact .bvar (by assumption))
    (symbol := by
      intro environment identifier arguments values output notBuiltin
        argumentsEval applied argumentsIH free
      exact .symbol notBuiltin (argumentsIH free.app_args) (Or.inl applied))
    (eqTrue := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval equal leftIH rightIH free
      have parts := free.app_args
      cases parts with
      | cons leftFree rest =>
        cases rest with
        | cons rightFree rest =>
          simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.eqTrue
            (leftIH leftFree) (rightIH rightFree) equal)
    (eqFalse := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval unequal leftIH rightIH free
      have parts := free.app_args
      cases parts with
      | cons leftFree rest =>
        cases rest with
        | cons rightFree rest =>
          simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.eqFalse
            (leftIH leftFree) (rightIH rightFree) unequal)
    (not := by
      intro environment body value bodyEval bodyIH free
      have parts := free.app_args
      cases parts with
      | cons bodyFree rest =>
        simpa only [model_bool, modelWith_bool] using
          Crush.SMT.Eval.not (bodyIH bodyFree))
    (imp := by
      intro environment leftTerm rightTerm leftValue rightValue leftEval
        rightEval leftIH rightIH free
      have parts := free.app_args
      cases parts with
      | cons leftFree rest =>
        cases rest with
        | cons rightFree rest =>
          simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.imp
            (leftIH leftFree) (rightIH rightFree))
    (and := by
      intro environment arguments values booleans argumentsEval boolValues
        argumentsIH free
      simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.and
        (argumentsIH free.app_args)
        (boolValues_with_extra encoding target extra boolValues))
    (or := by
      intro environment arguments values booleans argumentsEval boolValues
        argumentsIH free
      simpa only [model_bool, modelWith_bool] using Crush.SMT.Eval.or
        (argumentsIH free.app_args)
        (boolValues_with_extra encoding target extra boolValues))
    (letE := by
      intro environment bindings body values output valuesEval bodyEval
        valuesIH bodyIH free
      exact .letE (valuesIH free.let_parts.1) (bodyIH free.let_parts.2))
    (forallTrue := by
      intro environment binders body every everyIH free
      apply Crush.SMT.Eval.forallTrue
      intro values typed
      exact everyIH values
        (valuesTyped_without_extra encoding target extra typed) free.forall_body)
    (forallFalse := by
      intro environment binders body values typed bodyEval bodyIH free
      exact .forallFalse (valuesTyped_with_extra encoding target extra typed)
        (bodyIH free.forall_body))
    (existsTrue := by
      intro environment binders body values typed bodyEval bodyIH free
      exact .existsTrue (valuesTyped_with_extra encoding target extra typed)
        (bodyIH free.exists_body))
    (existsFalse := by
      intro environment binders body every everyIH free
      apply Crush.SMT.Eval.existsFalse
      intro values typed
      exact everyIH values
        (valuesTyped_without_extra encoding target extra typed) free.exists_body)
    (annot := by
      intro environment term attributes value bodyEval bodyIH free
      exact .annot (bodyIH free.annot_body))
    (nil := by intros; exact .nil)
    (cons := by
      intro environment term terms value values termEval termsEval termIH termsIH
        free
      cases free with
      | cons termFree termsFree => exact .cons (termIH termFree) (termsIH termsFree))
    evaluated free

end Crush.Metatheory.SMT
