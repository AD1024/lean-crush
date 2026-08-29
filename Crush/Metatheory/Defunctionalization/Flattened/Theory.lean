import Crush.Metatheory.Defunctionalization.Flattened.Denotation

/-!
# Validity of the generated flattened theory

Every equation and extensionality axiom emitted by total flattened translation
holds in the same canonical model used for term denotation.  Guards and
primitive constraints are included in the final theorem as well; the current
structural translator emits neither family.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

open scoped Crush.Metatheory

variable {signature : Signature} {context : Context}
variable {start result domain codomain : Ty}

private theorem pull_lift_extend
    {symbols : FO.SymbolFamily} {source target : FO.Context}
    {binder : FO.FOSort} (M : FO.FamilyModel symbols)
    (rho : FO.FamilyRenaming source target)
    (ν : FO.FamilyValuation M target)
    (value : binder.Denote M.carriers) :
    (fun {sort} (ref : FO.Var (binder :: source) sort) =>
      FO.Valuation.extend ν value (FO.FamilyRenaming.lift rho ref)) =
    (fun {sort} (ref : FO.Var (binder :: source) sort) =>
      FO.Valuation.extend (fun {_} sourceRef => ν (rho sourceRef)) value ref) := by
  apply @funext FO.FOSort
    (fun sort => FO.Var (binder :: source) sort → sort.Denote M.carriers)
  intro sort
  funext ref
  cases ref <;> rfl

private def RenameTerm {symbols : FO.SymbolFamily}
    (M : FO.FamilyModel symbols) {source : FO.Context} {sort : FO.FOSort}
    (term : FO.FamilyTerm symbols source sort) : Prop :=
  ∀ {target : FO.Context} (rho : FO.FamilyRenaming source target)
    (ν : FO.FamilyValuation M target),
    ⟦term.rename rho⟧[M, ν] =
      ⟦term⟧[M, fun {_} ref => ν (rho ref)]

private def RenameArgs {symbols : FO.SymbolFamily}
    (M : FO.FamilyModel symbols) {source : FO.Context}
    {sorts : List FO.FOSort}
    (arguments : FO.FamilyArgs symbols source sorts) : Prop :=
  ∀ {target : FO.Context} {result : FO.FOSort}
    (rho : FO.FamilyRenaming source target)
    (ν : FO.FamilyValuation M target)
    (function : FO.SymbolDenote M.carriers sorts result),
    (arguments.rename rho).apply M ν function =
      arguments.apply M (fun {_} ref => ν (rho ref)) function

private theorem rename_core {symbols : FO.SymbolFamily}
    (M : FO.FamilyModel symbols) {source : FO.Context} {sort : FO.FOSort}
    (term : FO.FamilyTerm symbols source sort) : RenameTerm M term := by
  exact FO.FamilyTerm.rec
    (motive_1 := fun _ _ term => RenameTerm M term)
    (motive_2 := fun _ _ arguments => RenameArgs M arguments)
    (var := fun ref => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_1])
    (symbol := fun symbol arguments argumentsIH => by
      unfold RenameTerm
      intro target rho ν
      simpa only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_2] using
        argumentsIH rho ν (M.symbol symbol))
    (boolLit := fun value => by
      unfold RenameTerm
      intro target rho ν
      cases value <;>
        simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_3,
          FO.FamilyTerm.denote.eq_4])
    (not := fun body bodyIH => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_5]
      rw [bodyIH rho ν])
    (and := fun left right leftIH rightIH => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_6]
      rw [leftIH rho ν, rightIH rho ν])
    (or := fun left right leftIH rightIH => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_7]
      rw [leftIH rho ν, rightIH rho ν])
    (imp := fun left right leftIH rightIH => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_8]
      rw [leftIH rho ν, rightIH rho ν])
    (iff := fun left right leftIH rightIH => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_9]
      rw [leftIH rho ν, rightIH rho ν])
    (eq := fun left right leftIH rightIH => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_10]
      rw [leftIH rho ν, rightIH rho ν])
    (forallE := fun body bodyIH => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_11]
      apply propext
      apply forall_congr'
      intro value
      rw [bodyIH]
      rw [pull_lift_extend M rho ν value])
    (existsE := fun body bodyIH => by
      unfold RenameTerm
      intro target rho ν
      simp only [FO.FamilyTerm.rename, FO.FamilyTerm.denote.eq_12]
      apply propext
      apply exists_congr
      intro value
      rw [bodyIH]
      rw [pull_lift_extend M rho ν value])
    (nil := fun {_} => by
      unfold RenameArgs
      intro target result rho ν function
      simp only [FO.FamilyArgs.rename, FO.FamilyArgs.apply.eq_1])
    (cons := fun argument rest argumentIH restIH => by
      unfold RenameArgs
      intro target result rho ν function
      simp only [FO.FamilyArgs.rename, FO.FamilyArgs.apply.eq_2]
      rw [argumentIH rho ν]
      exact restIH rho ν _)
    term

/-- FO family renaming commutes with denotation under the pulled-back
valuation. -/
theorem FO.FamilyTerm.denote_rename
    {symbols : FO.SymbolFamily} (M : FO.FamilyModel symbols)
    {source target : FO.Context} {sort : FO.FOSort}
    (rho : FO.FamilyRenaming source target)
    (term : FO.FamilyTerm symbols source sort)
    (ν : FO.FamilyValuation M target) :
    ⟦term.rename rho⟧[M, ν] =
      ⟦term⟧[M, fun {_} ref => ν (rho ref)] :=
  rename_core M term rho ν

@[simp] theorem FO.FamilyTerm.denote_weaken
    {symbols : FO.SymbolFamily} (M : FO.FamilyModel symbols)
    {source : FO.Context} {sort binder : FO.FOSort}
    (term : FO.FamilyTerm symbols source sort)
    (ν : FO.FamilyValuation M source)
    (value : binder.Denote M.carriers) :
    ⟦term.weaken⟧[M, FO.Valuation.extend ν value] = ⟦term⟧[M, ν] := by
  simpa only [FO.FamilyTerm.weaken, FO.FamilyRenaming.weaken,
    FO.Valuation.extend] using
    FO.FamilyTerm.denote_rename M
      (FO.FamilyRenaming.weaken (source := source) (domain := binder)) term
      (FO.Valuation.extend ν value)

@[simp] theorem targetWeaken_denote (M : Model signature)
    (term : TargetTerm signature context result)
    (ν : TargetValuation M context)
    (value : ⌊domain⌋.Denote (canonicalCarriers M)) :
    ⟦term.weaken⟧[canonicalModel M, targetExtend M ν value] =
      ⟦term⟧[canonicalModel M, ν] := by
  exact FO.FamilyTerm.denote_weaken (canonicalModel M) term ν value

theorem TargetArguments.applyUnary_rename
    (M : Model signature) {source target : Context}
    (rho : FO.FamilyRenaming (targetContext source) (targetContext target))
    (ν : TargetValuation M target)
    (arguments : TargetArguments signature source start result)
    (head : start.Denote M.Base) :
    (arguments.rename rho).applyUnary M ν head =
      arguments.applyUnary M (fun {_} ref => ν (rho ref)) head := by
  induction arguments with
  | nil => rfl
  | cons argument rest restIH =>
      simp only [TargetArguments.rename, TargetArguments.applyUnary]
      rw [FO.FamilyTerm.denote_rename]
      exact restIH _

@[simp] theorem TargetArguments.applyUnary_weaken
    (M : Model signature)
    (ν : TargetValuation M context)
    (value : ⌊domain⌋.Denote (canonicalCarriers M))
    (arguments : TargetArguments signature context start result)
    (head : start.Denote M.Base) :
    (arguments.weaken (domain := domain)).applyUnary M
        (targetExtend M ν value) head =
      arguments.applyUnary M ν head := by
  rw [TargetArguments.weaken, TargetArguments.applyUnary_rename]
  congr 1

@[simp] theorem TargetArguments.applySnoc_weaken
    (M : Model signature)
    (ν : TargetValuation M context)
    (value : ⌊domain⌋.Denote (canonicalCarriers M))
    (head : TargetTerm signature context start)
    (arguments : TargetArguments signature context start
      (.arrow domain codomain)) :
    ((arguments.weaken (domain := domain)).snoc (.var .here)).applyUnary M
        (targetExtend M ν value)
        (fromCanonical M start
          ⟦head.weaken⟧[canonicalModel M, targetExtend M ν value]) =
      arguments.applyUnary M ν
          (fromCanonical M start ⟦head⟧[canonicalModel M, ν])
        (fromCanonical M domain value) := by
  rw [TargetArguments.applyUnary_snoc,
    TargetArguments.applyUnary_weaken, targetWeaken_denote]
  simp only [FO.FamilyTerm.denote.eq_1, targetExtend, FO.Valuation.extend]

/-- The recursively generated pointwise formula is exactly equality after
applying the accumulated source argument prefix. -/
theorem pointwise_iff (M : Model signature)
    {functionDomain functionCodomain current : Ty}
    (leftHead rightHead : TargetTerm signature context
      (.arrow functionDomain functionCodomain))
    (leftArgs rightArgs : TargetArguments signature context
      (.arrow functionDomain functionCodomain) current)
    (ν : TargetValuation M context) :
    ⟦pointwiseEquality leftHead rightHead leftArgs rightArgs⟧[
        canonicalModel M, ν] ↔
      leftArgs.applyUnary M ν
          (fromCanonical M _ ⟦leftHead⟧[canonicalModel M, ν]) =
        rightArgs.applyUnary M ν
          (fromCanonical M _ ⟦rightHead⟧[canonicalModel M, ν]) := by
  induction current generalizing context with
  | bool =>
      simp only [pointwiseEquality, FO.FamilyTerm.denote.eq_10]
      rw [leftArgs.completeApp_denote, rightArgs.completeApp_denote]
  | base sort =>
      simp only [pointwiseEquality, FO.FamilyTerm.denote.eq_10]
      rw [leftArgs.completeApp_denote, rightArgs.completeApp_denote]
  | arrow domain codomain domainIH codomainIH =>
      simp only [pointwiseEquality, FO.FamilyTerm.denote.eq_11]
      constructor
      · intro pointwise
        funext argument
        have applied := (codomainIH (context := domain :: context)
          (leftHead.weaken (domain := ⌊domain⌋))
          (rightHead.weaken (domain := ⌊domain⌋))
          ((leftArgs.weaken (domain := domain)).snoc (.var .here))
          ((rightArgs.weaken (domain := domain)).snoc (.var .here))
          (targetExtend M ν (toCanonical M domain argument))).1
            (pointwise (toCanonical M domain argument))
        have leftStep := TargetArguments.applySnoc_weaken
          (domain := domain) (codomain := codomain) M ν
          (toCanonical M domain argument) leftHead leftArgs
        have rightStep := TargetArguments.applySnoc_weaken
          (domain := domain) (codomain := codomain) M ν
          (toCanonical M domain argument) rightHead rightArgs
        have normalized := leftStep.symm.trans (applied.trans rightStep)
        simpa only [fromCanonical_toCanonical] using normalized
      · intro equal value
        apply (codomainIH (context := domain :: context)
          (leftHead.weaken (domain := ⌊domain⌋))
          (rightHead.weaken (domain := ⌊domain⌋))
          ((leftArgs.weaken (domain := domain)).snoc (.var .here))
          ((rightArgs.weaken (domain := domain)).snoc (.var .here))
          (targetExtend M ν value)).2
        have leftStep := TargetArguments.applySnoc_weaken
          (domain := domain) (codomain := codomain) M ν value leftHead leftArgs
        have rightStep := TargetArguments.applySnoc_weaken
          (domain := domain) (codomain := codomain) M ν value rightHead rightArgs
        exact leftStep.trans
          ((congrFun equal (fromCanonical M domain value)).trans rightStep.symm)

/-- Every emitted function-extensionality sentence is true because canonical
function carriers are genuine source function spaces. -/
theorem extensionality_valid (M : Model signature) (domain codomain : Ty) :
    canonicalModel M ⊨
      (extensionalityFormula (signature := signature) domain codomain) := by
  let functionTy := Ty.arrow domain codomain
  let functionContext : Context := [functionTy, functionTy]
  let left : TargetTerm signature functionContext functionTy := .var (.there .here)
  let right : TargetTerm signature functionContext functionTy := .var .here
  change canonicalModel M ⊨ FO.FamilyFormula.closeForall
    (.imp
      (pointwiseEquality left right (.nil functionTy) (.nil functionTy))
      (.eq left right))
  apply FO.FamilyModel.satisfies_closeForall_of_forall_denote
  intro ν
  simp only [FO.FamilyTerm.denote.eq_8, FO.FamilyTerm.denote.eq_10]
  intro pointwise
  have equal := (pointwise_iff M left right
    (.nil functionTy) (.nil functionTy) ν).1 pointwise
  dsimp only [functionTy] at equal ⊢
  have mapped := congrArg (toCanonical M (.arrow domain codomain)) equal
  simpa only [TargetArguments.applyUnary, toCanonical_fromCanonical] using mapped

@[reducible] def targetTail (M : Model signature)
    (ν : TargetValuation M (domain :: context)) :
    TargetValuation M context :=
  fun {_} ref => ν (.there ref)

@[simp] theorem targetExtend_tail (M : Model signature)
    (ν : TargetValuation M (domain :: context)) :
    (targetExtend M (targetTail (domain := domain) M ν)
      (ν (.here : FO.Var (targetContext (domain :: context)) ⌊domain⌋)) :
        TargetValuation M (domain :: context)) =
      (ν : TargetValuation M (domain :: context)) := by
  apply @funext FO.FOSort
    (fun sort => FO.Var (targetContext (domain :: context)) sort →
      sort.Denote (canonicalCarriers M))
  intro sort
  funext ref
  cases ref <;> rfl

@[simp] theorem FunctionHead.denote_weaken
    (M : Model signature)
    (ν : TargetValuation M context)
    (value : ⌊domain⌋.Denote (canonicalCarriers M))
    (head : FunctionHead signature context start result) :
    (head.weaken (binder := domain)).denote M (targetExtend M ν value) =
      head.denote M ν := by
  cases head with
  | value term =>
      simp only [FunctionHead.weaken, FunctionHead.denote]
      exact congrArg (fromCanonical M (.arrow start result))
        (targetWeaken_denote M term ν value)
  | sourceConstant constant => rfl

@[simp] theorem SpineResult.denote_weaken
    (M : Model signature)
    (ν : TargetValuation M context)
    (value : ⌊domain⌋.Denote (canonicalCarriers M))
    (spine : SpineResult signature context result) :
    (spine.weaken (binder := domain)).denote M (targetExtend M ν value) =
      spine.denote M ν := by
  simp only [SpineResult.weaken, SpineResult.denote]
  rw [TargetArguments.applyUnary_weaken, FunctionHead.denote_weaken]

@[simp] theorem SpineResult.denoteSnoc_weaken
    (M : Model signature)
    (ν : TargetValuation M context)
    (value : ⌊domain⌋.Denote (canonicalCarriers M))
    (spine : SpineResult signature context (.arrow domain codomain)) :
    ((spine.weaken (binder := domain)).snoc (.var .here)).denote M
        (targetExtend M ν value) =
      spine.denote M ν (fromCanonical M domain value) := by
  rw [SpineResult.denote_snoc, SpineResult.denote_weaken]
  simp only [FO.FamilyTerm.denote.eq_1, targetExtend, FO.Valuation.extend]

/-- Saturating two denotationally equal residual function spines produces a
valid closed closure equation. -/
theorem saturate_valid (M : Model signature)
    {closureDomain closureCodomain current : Ty}
    (closureHead : TargetTerm signature context
      (.arrow closureDomain closureCodomain))
    (closureArgs : TargetArguments signature context
      (.arrow closureDomain closureCodomain) current)
    (right : SpineResult signature context current)
    (correct : ∀ ν : TargetValuation M context,
      closureArgs.applyUnary M ν
          (fromCanonical M _ ⟦closureHead⟧[canonicalModel M, ν]) =
        right.denote M ν) :
    canonicalModel M ⊨
      (saturateEquation closureHead closureArgs right).equation := by
  induction current generalizing context with
  | bool =>
      simp only [saturateEquation]
      apply FO.FamilyModel.satisfies_closeForall_of_forall_denote
      intro ν
      simp only [FO.FamilyTerm.denote.eq_10]
      rw [closureArgs.completeApp_denote, SpineResult.finish_denote]
      exact congrArg (toCanonical M .bool) (correct ν)
  | base sort =>
      simp only [saturateEquation]
      apply FO.FamilyModel.satisfies_closeForall_of_forall_denote
      intro ν
      simp only [FO.FamilyTerm.denote.eq_10]
      rw [closureArgs.completeApp_denote, SpineResult.finish_denote]
      exact congrArg (toCanonical M (.base sort)) (correct ν)
  | arrow domain codomain domainIH codomainIH =>
      simp only [saturateEquation]
      apply codomainIH
      intro ν
      let tail : TargetValuation M context :=
        fun {_} ref => ν (.there ref)
      let value : ⌊domain⌋.Denote (canonicalCarriers M) :=
        ν (.here : FO.Var (targetContext (domain :: context)) ⌊domain⌋)
      have valuationEq :
          (targetExtend M tail value : TargetValuation M (domain :: context)) =
            (ν : TargetValuation M (domain :: context)) := by
        apply @funext FO.FOSort
          (fun sort => FO.Var (targetContext (domain :: context)) sort →
            sort.Denote (canonicalCarriers M))
        intro sort
        funext ref
        cases ref <;> rfl
      rw [← valuationEq]
      have leftStep := TargetArguments.applySnoc_weaken
        (domain := domain) (codomain := codomain) M tail value
        closureHead closureArgs
      have rightStep := SpineResult.denoteSnoc_weaken
        (domain := domain) (codomain := codomain) M tail value right
      exact leftStep.trans
        ((congrFun (correct tail) (fromCanonical M domain value)).trans
          rightStep.symm)

theorem FO.FamilyModel.satisfiesTheory_append
    {symbols : FO.SymbolFamily} (model : FO.FamilyModel symbols)
    (left right : FO.FamilyTheory symbols) :
    model ⊨ᵀ (left ++ right) ↔ model ⊨ᵀ left ∧ model ⊨ᵀ right := by
  unfold FO.FamilyModel.SatisfiesTheory
  constructor <;> intro valid
  · constructor <;> intro formula membership
    · exact valid formula (by simp only [List.mem_append]; exact Or.inl membership)
    · exact valid formula (by simp only [List.mem_append]; exact Or.inr membership)
  · intro formula membership
    simp only [List.mem_append] at membership
    grind

/-- Componentwise validity of generated formulas; declarations carry no
semantic obligation. -/
structure GenValid (M : Model signature)
    (generated : GeneratedObligations signature) : Prop where
  equations : canonicalModel M ⊨ᵀ generated.equations
  guards : canonicalModel M ⊨ᵀ generated.guards
  extensionality : canonicalModel M ⊨ᵀ generated.extensionality
  primitives : canonicalModel M ⊨ᵀ generated.primitiveConstraints

namespace GenValid

variable {M : Model signature}

theorem empty (M : Model signature) :
    GenValid M (GeneratedObligations.empty (signature := signature)) := by
  constructor <;> intro formula membership <;> contradiction

theorem append {left right : GeneratedObligations signature}
    (leftValid : GenValid M left) (rightValid : GenValid M right) :
    GenValid M (left.append right) := by
  constructor
  · exact (FO.FamilyModel.satisfiesTheory_append _ _ _).2
      ⟨leftValid.equations, rightValid.equations⟩
  · exact (FO.FamilyModel.satisfiesTheory_append _ _ _).2
      ⟨leftValid.guards, rightValid.guards⟩
  · exact (FO.FamilyModel.satisfiesTheory_append _ _ _).2
      ⟨leftValid.extensionality, rightValid.extensionality⟩
  · exact (FO.FamilyModel.satisfiesTheory_append _ _ _).2
      ⟨leftValid.primitives, rightValid.primitives⟩

theorem declare {generated : GeneratedObligations signature}
    (valid : GenValid M generated) (declaration : DeclaredSymbol signature) :
    GenValid M (generated.declare declaration) := by
  exact ⟨valid.equations, valid.guards, valid.extensionality,
    valid.primitives⟩

theorem addEquation {generated : GeneratedObligations signature}
    (valid : GenValid M generated) (formula : TargetSentence signature)
    (formulaValid : canonicalModel M ⊨ formula) :
    GenValid M { generated with equations := generated.equations ++ [formula] } := by
  constructor
  · apply (FO.FamilyModel.satisfiesTheory_append _ _ _).2
    exact ⟨valid.equations, by
      intro candidate membership
      have equal : candidate = formula := by
        simpa only [List.mem_singleton] using membership
      subst candidate
      exact formulaValid⟩
  · exact valid.guards
  · exact valid.extensionality
  · exact valid.primitives

theorem addExt {generated : GeneratedObligations signature}
    (valid : GenValid M generated) (formula : TargetSentence signature)
    (formulaValid : canonicalModel M ⊨ formula) :
    GenValid M
      { generated with extensionality := generated.extensionality ++ [formula] } := by
  constructor
  · exact valid.equations
  · exact valid.guards
  · apply (FO.FamilyModel.satisfiesTheory_append _ _ _).2
    exact ⟨valid.extensionality, by
      intro candidate membership
      have equal : candidate = formula := by
        simpa only [List.mem_singleton] using membership
      subst candidate
      exact formulaValid⟩
  · exact valid.primitives

theorem theory {generated : GeneratedObligations signature}
    (valid : GenValid M generated) :
    canonicalModel M ⊨ᵀ generated.theory := by
  unfold GeneratedObligations.theory
  rw [FO.FamilyModel.satisfiesTheory_append,
    FO.FamilyModel.satisfiesTheory_append,
    FO.FamilyModel.satisfiesTheory_append]
  exact ⟨⟨⟨valid.equations, valid.guards⟩, valid.extensionality⟩,
    valid.primitives⟩

end GenValid

abbrev ResultValid (M : Model signature)
    (translated : TranslationResult signature context result) : Prop :=
  GenValid M translated.obligations

abbrev SpineValid (M : Model signature)
    (spine : SpineResult signature context result) : Prop :=
  GenValid M spine.generated

structure EqValid (M : Model signature)
    (equation : EquationResult signature) : Prop where
  generated : GenValid M equation.generated
  equation : canonicalModel M ⊨ equation.equation

variable {M : Model signature}

theorem TranslationResult.ofGenerated_valid
    (M : Model signature)
    (term : TargetTerm signature context result)
    (generated : GeneratedObligations signature)
    (valid : GenValid M generated) :
    ResultValid M (TranslationResult.ofGenerated term generated) := by
  exact valid

theorem TranslationResult.replace_valid
    (translated : TranslationResult signature context start)
    (term : TargetTerm signature context result)
    (valid : ResultValid M translated) :
    ResultValid M (translated.replaceTerm term) := by
  exact valid

theorem TranslationResult.combine_valid
    (left : TranslationResult signature context start)
    (right : TranslationResult signature context result)
    (term : TargetTerm signature context domain)
    (leftValid : ResultValid M left) (rightValid : ResultValid M right) :
    ResultValid M (left.combine right term) := by
  exact GenValid.append leftValid rightValid

theorem TranslationResult.addExt_valid
    (translated : TranslationResult signature context result)
    (formula : TargetSentence signature)
    (valid : ResultValid M translated)
    (formulaValid : canonicalModel M ⊨ formula) :
    ResultValid M
      (translated.appendGenerated (extensionality := [formula])) := by
  simpa only [ResultValid, TranslationResult.appendGenerated,
    TranslationResult.obligations, List.append_nil] using
    GenValid.addExt valid formula formulaValid

theorem SpineResult.weaken_valid
    (spine : SpineResult signature context result)
    (valid : SpineValid M spine) :
    SpineValid M (spine.weaken (binder := domain)) := valid

theorem SpineResult.snoc_valid
    (spine : SpineResult signature context (.arrow domain codomain))
    (argument : TargetTerm signature context domain)
    (generated : GeneratedObligations signature)
    (spineValid : SpineValid M spine) (generatedValid : GenValid M generated) :
    SpineValid M (spine.snoc argument generated) := by
  exact GenValid.append spineValid generatedValid

theorem SpineResult.finish_valid
    (spine : SpineResult signature context result)
    (ground : GroundResult result) (valid : SpineValid M spine) :
    ResultValid M (spine.finish ground) := by
  rcases spine with ⟨headDomain, headCodomain, head, arguments, generated⟩
  cases head with
  | value term =>
      exact GenValid.declare valid _
  | sourceConstant constant =>
      exact GenValid.declare valid _

theorem saturate_generated (M : Model signature)
    {closureDomain closureCodomain current : Ty}
    (closureHead : TargetTerm signature context
      (.arrow closureDomain closureCodomain))
    (closureArgs : TargetArguments signature context
      (.arrow closureDomain closureCodomain) current)
    (right : SpineResult signature context current)
    (valid : SpineValid M right) :
    GenValid M (saturateEquation closureHead closureArgs right).generated := by
  induction current generalizing context with
  | bool =>
      simpa only [saturateEquation] using
        SpineResult.finish_valid right .bool valid
  | base sort =>
      simpa only [saturateEquation] using
        SpineResult.finish_valid right (.base sort) valid
  | arrow domain codomain domainIH codomainIH =>
      simp only [saturateEquation]
      apply codomainIH
      apply SpineResult.snoc_valid
      · exact SpineResult.weaken_valid right valid
      · exact GenValid.empty M

theorem saturate_eqValid (M : Model signature)
    {closureDomain closureCodomain current : Ty}
    (closureHead : TargetTerm signature context
      (.arrow closureDomain closureCodomain))
    (closureArgs : TargetArguments signature context
      (.arrow closureDomain closureCodomain) current)
    (right : SpineResult signature context current)
    (valid : SpineValid M right)
    (correct : ∀ ν : TargetValuation M context,
      closureArgs.applyUnary M ν
          (fromCanonical M _ ⟦closureHead⟧[canonicalModel M, ν]) =
        right.denote M ν) :
    EqValid M (saturateEquation closureHead closureArgs right) :=
  ⟨saturate_generated M closureHead closureArgs right valid,
    saturate_valid M closureHead closureArgs right correct⟩

theorem finishClosure_valid
    (closure : Closure signature)
    (contextEq : closure.context = context)
    (domainEq : closure.domain = domain)
    (codomainEq : closure.codomain = codomain)
    (closureTerm : TargetTerm signature context (.arrow domain codomain))
    (equation : EquationResult signature)
    (valid : EqValid M equation) :
    ResultValid M (finishClosure closure contextEq domainEq codomainEq
      closureTerm equation) := by
  subst contextEq
  subst domainEq
  subst codomainEq
  let declarations :=
    (GeneratedObligations.empty (signature := signature))
      |>.declare (.of (Symbol.application
        { domain := closure.domain, codomain := closure.codomain }))
      |>.declare (.of (Symbol.closure closure))
  let generated := declarations.append equation.generated
  have declarationsValid : GenValid M declarations :=
    (GenValid.empty M).declare _ |>.declare _
  have generatedValid : GenValid M generated :=
    declarationsValid.append valid.generated
  exact generatedValid.addEquation equation.equation valid.equation

noncomputable def SpineGen (M : Model signature)
    {Γ : Context} {ty : Ty} (term : Term signature Γ ty) : Prop :=
  match ty with
  | .bool | .base _ => True
  | .arrow _ _ => ∀ {Δ : Context} (ρ : Renaming Γ Δ),
      SpineValid M (translateSpineWith ρ term)

noncomputable def BodyCorrect (M : Model signature)
    {Γ Δ : Context} {current closureDomain closureCodomain : Ty}
    (ρ : Renaming Γ Δ) (term : Term signature Γ current)
    (closureHead : TargetTerm signature Δ
      (.arrow closureDomain closureCodomain))
    (closureArgs : TargetArguments signature Δ
      (.arrow closureDomain closureCodomain) current) : Prop :=
  ∀ ν : TargetValuation M Δ,
    closureArgs.applyUnary M ν
        (fromCanonical M _ ⟦closureHead⟧[canonicalModel M, ν]) =
      ⟦term.rename ρ⟧[M, sourceValuation M ν]

noncomputable def LambdaGen (M : Model signature)
    {Γ : Context} {current : Ty} (term : Term signature Γ current) : Prop :=
  ∀ {Δ : Context} (ρ : Renaming Γ Δ)
    {closureDomain closureCodomain : Ty}
    (closureHead : TargetTerm signature Δ
      (.arrow closureDomain closureCodomain))
    (closureArgs : TargetArguments signature Δ
      (.arrow closureDomain closureCodomain) current),
    BodyCorrect M ρ term closureHead closureArgs →
      EqValid M (translateLambdaBodyWith ρ term closureHead closureArgs)

structure TermGenValid (M : Model signature)
    {Γ : Context} {ty : Ty} (term : Term signature Γ ty) : Prop where
  result : ∀ {Δ : Context} (ρ : Renaming Γ Δ),
    ResultValid M (translateWith ρ term)
  spine : SpineGen M term
  lambda : LambdaGen M term

theorem groundEq_valid (M : Model signature)
    {Γ Δ : Context} {result closureDomain closureCodomain : Ty}
    (ground : GroundResult result) (ρ : Renaming Γ Δ)
    (term : Term signature Γ result)
    (closureHead : TargetTerm signature Δ
      (.arrow closureDomain closureCodomain))
    (closureArgs : TargetArguments signature Δ
      (.arrow closureDomain closureCodomain) result)
    (translatedValid : ResultValid M (translateWith ρ term))
    (correct : BodyCorrect M ρ term closureHead closureArgs) :
    EqValid M (translateLambdaBodyWith ρ term closureHead closureArgs) := by
  cases ground with
  | bool =>
      constructor
      · simpa only [translateLambdaBodyWith] using translatedValid
      · simp only [translateLambdaBodyWith]
        apply FO.FamilyModel.satisfies_closeForall_of_forall_denote
        intro ν
        simp only [FO.FamilyTerm.denote.eq_10]
        rw [closureArgs.completeApp_denote, translateWith_denote]
        exact congrArg (toCanonical M .bool) (correct ν)
  | base sort =>
      constructor
      · simpa only [translateLambdaBodyWith] using translatedValid
      · simp only [translateLambdaBodyWith]
        apply FO.FamilyModel.satisfies_closeForall_of_forall_denote
        intro ν
        simp only [FO.FamilyTerm.denote.eq_10]
        rw [closureArgs.completeApp_denote, translateWith_denote]
        exact congrArg (toCanonical M (.base sort)) (correct ν)

theorem openLambda_valid (M : Model signature)
    {Γ Δ : Context} {domain codomain closureDomain closureCodomain : Ty}
    (ρ : Renaming Γ Δ) (body : Term signature (domain :: Γ) codomain)
    (closureHead : TargetTerm signature Δ
      (.arrow closureDomain closureCodomain))
    (closureArgs : TargetArguments signature Δ
      (.arrow closureDomain closureCodomain) (.arrow domain codomain))
    (bodyValid : LambdaGen M body)
    (correct : BodyCorrect M ρ (.lam body) closureHead closureArgs) :
    EqValid M
      (translateLambdaBodyWith ρ (.lam body) closureHead closureArgs) := by
  simp only [translateLambdaBodyWith]
  apply bodyValid (Renaming.lift ρ)
  intro ν
  let tail : TargetValuation M Δ :=
    fun {_} ref => ν (.there ref)
  let value : ⌊domain⌋.Denote (canonicalCarriers M) :=
    ν (.here : FO.Var (targetContext (domain :: Δ)) ⌊domain⌋)
  have valuationEq :
      (targetExtend M tail value : TargetValuation M (domain :: Δ)) =
        (ν : TargetValuation M (domain :: Δ)) := by
    apply @funext FO.FOSort
      (fun sort => FO.Var (targetContext (domain :: Δ)) sort →
        sort.Denote (canonicalCarriers M))
    intro sort
    funext ref
    cases ref <;> rfl
  rw [← valuationEq]
  have leftStep := TargetArguments.applySnoc_weaken
    (domain := domain) (codomain := codomain) M tail value
    closureHead closureArgs
  have applied := congrFun (correct tail) (fromCanonical M domain value)
  simp only [Term.rename, Term.denote] at applied
  rw [sourceValuation_extend M tail value]
  exact leftStep.trans applied

/-- One structural induction validates output from all three translator modes. -/
private theorem generated_core (M : Model signature) :
    {Γ : Context} → {ty : Ty} → (term : Term signature Γ ty) →
      TermGenValid M term := by
  intro Γ ty term
  induction term with
  | var ref =>
      rename_i actualContext actualTy
      cases actualTy with
      | bool =>
          refine ⟨?_, True.intro, ?_⟩
          · intro Δ ρ
            simp only [translateWith]
            exact GenValid.empty M
          · intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
            exact groundEq_valid M .bool ρ (.var ref) closureHead closureArgs
              (by simp only [translateWith]; exact GenValid.empty M) correct
      | base sort =>
          refine ⟨?_, True.intro, ?_⟩
          · intro Δ ρ
            simp only [translateWith]
            exact GenValid.empty M
          · intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
            exact groundEq_valid M (.base sort) ρ (.var ref) closureHead closureArgs
              (by simp only [translateWith]; exact GenValid.empty M) correct
      | arrow domain codomain =>
          have spineValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
              SpineValid M (translateSpineWith ρ (.var ref)) := by
            intro Δ ρ
            simp only [translateSpineWith]
            exact GenValid.empty M
          refine ⟨?_, spineValid, ?_⟩
          · intro Δ ρ
            simp only [translateWith]
            apply finishClosure_valid
            apply saturate_eqValid
            · exact spineValid ρ
            · intro ν
              have closureEq := etaClosure_denote M (.var (ρ ref)) ν
              have mapped := congrArg
                (fromCanonical M (.arrow domain codomain)) closureEq
              rw [fromCanonical_toCanonical] at mapped
              exact mapped.trans
                (translateSpineWith_denote M ρ (.var ref) ν).symm
          · intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
            simp only [translateLambdaBodyWith]
            apply saturate_eqValid
            · exact spineValid ρ
            · intro ν
              exact (correct ν).trans
                (translateSpineWith_denote M ρ (.var ref) ν).symm
  | const constant =>
      rename_i actualContext actualTy
      cases actualTy with
      | bool =>
          have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
              ResultValid M (translateWith ρ (.const constant)) := by
            intro Δ ρ
            simp only [translateWith]
            exact (GenValid.empty M).declare _
          refine ⟨resultValid, True.intro, ?_⟩
          intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
          exact groundEq_valid M .bool ρ (.const constant) closureHead closureArgs
            (resultValid ρ) correct
      | base sort =>
          have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
              ResultValid M (translateWith ρ (.const constant)) := by
            intro Δ ρ
            simp only [translateWith]
            exact (GenValid.empty M).declare _
          refine ⟨resultValid, True.intro, ?_⟩
          intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
          exact groundEq_valid M (.base sort) ρ (.const constant)
            closureHead closureArgs (resultValid ρ) correct
      | arrow domain codomain =>
          have spineValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
              SpineValid M (translateSpineWith ρ (.const constant)) := by
            intro Δ ρ
            simp only [translateSpineWith]
            exact GenValid.empty M
          refine ⟨?_, spineValid, ?_⟩
          · intro Δ ρ
            simp only [translateWith]
            apply finishClosure_valid
            apply saturate_eqValid
            · exact spineValid ρ
            · intro ν
              have closureEq := etaClosure_denote M (.const constant) ν
              have mapped := congrArg
                (fromCanonical M (.arrow domain codomain)) closureEq
              rw [fromCanonical_toCanonical] at mapped
              exact mapped.trans
                (translateSpineWith_denote M ρ (.const constant) ν).symm
          · intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
            simp only [translateLambdaBodyWith]
            apply saturate_eqValid
            · exact spineValid ρ
            · intro ν
              exact (correct ν).trans
                (translateSpineWith_denote M ρ (.const constant) ν).symm
  | boolLit value =>
      rename_i actualContext
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.boolLit value)) := by
        intro Δ ρ
        simp only [translateWith]
        exact GenValid.empty M
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.boolLit value) closureHead closureArgs
        (resultValid ρ) correct
  | not body bodyIH =>
      rename_i actualContext
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.not body)) := by
        intro Δ ρ
        simp only [translateWith]
        exact TranslationResult.replace_valid _ _ (bodyIH.result ρ)
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.not body) closureHead closureArgs
        (resultValid ρ) correct
  | and left right leftIH rightIH =>
      rename_i actualContext
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.and left right)) := by
        intro Δ ρ
        simp only [translateWith]
        exact TranslationResult.combine_valid _ _ _
          (leftIH.result ρ) (rightIH.result ρ)
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.and left right) closureHead closureArgs
        (resultValid ρ) correct
  | or left right leftIH rightIH =>
      rename_i actualContext
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.or left right)) := by
        intro Δ ρ
        simp only [translateWith]
        exact TranslationResult.combine_valid _ _ _
          (leftIH.result ρ) (rightIH.result ρ)
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.or left right) closureHead closureArgs
        (resultValid ρ) correct
  | imp left right leftIH rightIH =>
      rename_i actualContext
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.imp left right)) := by
        intro Δ ρ
        simp only [translateWith]
        exact TranslationResult.combine_valid _ _ _
          (leftIH.result ρ) (rightIH.result ρ)
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.imp left right) closureHead closureArgs
        (resultValid ρ) correct
  | iff left right leftIH rightIH =>
      rename_i actualContext
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.iff left right)) := by
        intro Δ ρ
        simp only [translateWith]
        exact TranslationResult.combine_valid _ _ _
          (leftIH.result ρ) (rightIH.result ρ)
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.iff left right) closureHead closureArgs
        (resultValid ρ) correct
  | eq left right leftIH rightIH =>
      rename_i actualContext operandType
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.eq left right)) := by
        intro Δ ρ
        cases operandType with
        | bool | base =>
            simp only [translateWith]
            exact TranslationResult.combine_valid _ _ _
              (leftIH.result ρ) (rightIH.result ρ)
        | arrow domain codomain =>
            simp only [translateWith]
            apply TranslationResult.addExt_valid
            · exact TranslationResult.combine_valid _ _ _
                (leftIH.result ρ) (rightIH.result ρ)
            · exact extensionality_valid M domain codomain
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.eq left right) closureHead closureArgs
        (resultValid ρ) correct
  | lam body bodyIH =>
      rename_i actualContext domain codomain
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.lam body)) := by
        intro Δ ρ
        let closure : Closure signature :=
          Closure.ofBody
            (LambdaBody.etaBody (.lam (body.rename (Renaming.lift ρ))))
        let closureTerm : TargetTerm signature Δ (.arrow domain codomain) :=
          .symbol (Symbol.closure closure) (captureArgs closure.captureRefs)
        simp only [translateWith]
        apply finishClosure_valid
        have closureCorrect : BodyCorrect M ρ (.lam body) closureTerm
            (.nil (.arrow domain codomain)) := by
          intro ν
          simp only [TargetArguments.applyUnary]
          change ⟦closureTerm⟧[canonicalModel M, ν] =
            ⟦Term.lam (body.rename (Renaming.lift ρ))⟧[
              M, sourceValuation M ν]
          have closureEq := etaClosure_denote M
            (.lam (body.rename (Renaming.lift ρ))) ν
          simpa only [closureTerm, closure, toCanonical, FO.arrowSort,
            FO.FOSort.ofTy] using closureEq
        have equationValid := openLambda_valid M ρ body closureTerm
          (.nil (.arrow domain codomain)) bodyIH.lambda closureCorrect
        simpa only [closureTerm, closure, translateLambdaBodyWith] using
          equationValid
      refine ⟨resultValid, ?_, ?_⟩
      · intro Δ ρ
        simpa only [translateSpineWith, translateWith, SpineValid, ResultValid]
          using resultValid ρ
      · intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
        exact openLambda_valid M ρ body closureHead closureArgs
          bodyIH.lambda correct
  | app fn argument fnIH argumentIH =>
      rename_i actualContext appDomain appCodomain
      cases appCodomain with
      | bool =>
          have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
              ResultValid M (translateWith ρ (.app fn argument)) := by
            intro Δ ρ
            simp only [translateWith]
            apply SpineResult.finish_valid
            apply SpineResult.snoc_valid
            · exact fnIH.spine ρ
            · exact argumentIH.result ρ
          refine ⟨resultValid, True.intro, ?_⟩
          intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
          exact groundEq_valid M .bool ρ (.app fn argument)
            closureHead closureArgs (resultValid ρ) correct
      | base sort =>
          have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
              ResultValid M (translateWith ρ (.app fn argument)) := by
            intro Δ ρ
            simp only [translateWith]
            apply SpineResult.finish_valid
            apply SpineResult.snoc_valid
            · exact fnIH.spine ρ
            · exact argumentIH.result ρ
          refine ⟨resultValid, True.intro, ?_⟩
          intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
          exact groundEq_valid M (.base sort) ρ (.app fn argument)
            closureHead closureArgs (resultValid ρ) correct
      | arrow residualDomain residualCodomain =>
          have spineValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
              SpineValid M (translateSpineWith ρ (.app fn argument)) := by
            intro Δ ρ
            simp only [translateSpineWith]
            apply SpineResult.snoc_valid
            · exact fnIH.spine ρ
            · exact argumentIH.result ρ
          refine ⟨?_, spineValid, ?_⟩
          · intro Δ ρ
            simp only [translateWith]
            apply finishClosure_valid
            apply saturate_eqValid
            · exact spineValid ρ
            · intro ν
              have closureEq := etaClosure_denote M
                (.app (fn.rename ρ) (argument.rename ρ)) ν
              have mapped := congrArg
                (fromCanonical M (.arrow residualDomain residualCodomain))
                closureEq
              rw [fromCanonical_toCanonical] at mapped
              exact mapped.trans
                (translateSpineWith_denote M ρ (.app fn argument) ν).symm
          · intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
            simp only [translateLambdaBodyWith]
            apply saturate_eqValid
            · exact spineValid ρ
            · intro ν
              exact (correct ν).trans
                (translateSpineWith_denote M ρ (.app fn argument) ν).symm
  | forallE body bodyIH =>
      rename_i actualContext domain
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.forallE body)) := by
        intro Δ ρ
        simp only [translateWith]
        exact bodyIH.result (Renaming.lift ρ)
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.forallE body) closureHead closureArgs
        (resultValid ρ) correct
  | existsE body bodyIH =>
      rename_i actualContext domain
      have resultValid : ∀ {Δ : Context} (ρ : Renaming actualContext Δ),
          ResultValid M (translateWith ρ (.existsE body)) := by
        intro Δ ρ
        simp only [translateWith]
        exact bodyIH.result (Renaming.lift ρ)
      refine ⟨resultValid, True.intro, ?_⟩
      intro Δ ρ closureDomain closureCodomain closureHead closureArgs correct
      exact groundEq_valid M .bool ρ (.existsE body) closureHead closureArgs
        (resultValid ρ) correct

/-- Generated output remains valid under every source-context renaming. -/
theorem translateWith_generated_valid (M : Model signature)
    {Γ Δ : Context} {ty : Ty} (ρ : Renaming Γ Δ)
    (term : Term signature Γ ty) :
    ResultValid M (translateWith ρ term) :=
  (generated_core M term).result ρ

/-- The complete auxiliary theory produced by flattened translation is valid
in the same canonical model as the translated term. -/
theorem generated_valid (M : Model signature)
    (term : Term signature context result) :
    canonicalModel M ⊨ᵀ 𝓕⟦term⟧.theory := by
  apply GenValid.theory
  exact translateWith_generated_valid M Renaming.id term

/-- Term component of a translated closed formula, exposed as an FO sentence. -/
def translatedSentence (formula : Sentence signature) :
    TargetSentence signature :=
  𝓕⟦formula⟧.term

/-- Complete target theory for a translated source sentence. -/
def translatedTheory (formula : Sentence signature) :
    TargetTheory signature :=
  𝓕⟦formula⟧.theory ++ [translatedSentence formula]

/-- A satisfying source model extends to one canonical model satisfying the
whole flattened target theory. -/
theorem model_extension (M : Model signature) (formula : Sentence signature)
    (sourceValid : M ⊨ formula) :
    canonicalModel M ⊨ᵀ translatedTheory formula := by
  rw [translatedTheory, FO.FamilyModel.satisfiesTheory_append]
  constructor
  · exact generated_valid M formula
  · intro targetFormula membership
    simp only [List.mem_singleton] at membership
    subst targetFormula
    change ⟦𝓕⟦formula⟧.term⟧[
      canonicalModel M, targetVal M (Valuation.empty M.Base)]
    rw [translate_denote]
    exact sourceValid

/-- Unsatisfiability of the flattened target theory reflects to the source
sentence. -/
theorem target_unsat_implies_source_unsat (formula : Sentence signature)
    (targetUnsat : FO.FamilyTheoryUnsatisfiable (translatedTheory formula)) :
    Unsatisfiable formula := by
  intro M sourceValid
  exact targetUnsat (canonicalModel M)
    (model_extension M formula sourceValid)

end Crush.Metatheory.Defunctionalization.Flattened
