import Crush.Metatheory.Defunctionalization.Flattened.Currying
import Crush.Metatheory.Defunctionalization.Flattened.Translate
import Crush.Metatheory.Notation

/-!
# Denotation of total flattened translation

The canonical flattened model interprets the term component of total
translation exactly as the renamed higher-order source term.  Generated
equations are handled separately: term denotation depends only on the canonical
interpretations of exact-capture closures and flattened application symbols.
-/

namespace Crush.Metatheory.Defunctionalization.Flattened

open scoped Crush.Metatheory

variable {signature : Signature} {context : Context}
variable {start result domain codomain : Ty}

/-- Extend a target valuation while retaining the source-context-shaped index. -/
@[reducible] noncomputable def targetExtend (M : Model signature)
    (ν : TargetValuation M context)
    (value : (FO.FOSort.ofTy domain).Denote (canonicalCarriers M)) :
    TargetValuation M (domain :: context) :=
  FO.Valuation.extend ν value

/-- Reading an extended target valuation extends the corresponding source
valuation by the same type-directed value. -/
@[simp] theorem sourceValuation_extend_apply (M : Model signature)
    (ν : TargetValuation M context)
    (value : (FO.FOSort.ofTy domain).Denote (canonicalCarriers M))
    {ty : Ty} (ref : Var (domain :: context) ty) :
    sourceValuation M (context := domain :: context)
        (targetExtend M ν value) ref =
      Valuation.extend (sourceValuation M ν)
        (fromCanonical M domain value) ref := by
  cases ref <;> rfl

theorem sourceValuation_extend (M : Model signature)
    (ν : TargetValuation M context)
    (value : (FO.FOSort.ofTy domain).Denote (canonicalCarriers M)) :
    (sourceValuation M (context := domain :: context)
      (targetExtend M ν value) : Valuation M.Base (domain :: context)) =
    (fun {_} ref => Valuation.extend (sourceValuation M ν)
      (fromCanonical M domain value) ref) := by
  apply @funext Ty
    (fun ty => Var (domain :: context) ty → ty.Denote M.Base)
  intro ty
  funext ref
  exact sourceValuation_extend_apply M ν value ref

/-- The eta closure chosen for a residual function term denotes that term. -/
theorem etaClosure_denote (M : Model signature)
    (term : Term signature context (.arrow domain codomain))
    (ν : TargetValuation M context) :
    let closure : Closure signature :=
      Closure.ofBody (LambdaBody.etaBody term)
    ⟦FO.FamilyTerm.symbol (Symbol.closure closure)
      (captureArgs closure.captureRefs)⟧[canonicalModel M, ν] =
      toCanonical M (.arrow domain codomain)
        ⟦term⟧[M, sourceValuation M ν] := by
  dsimp only
  rw [denote_closure, LambdaBody.denote_etaBody]

namespace FunctionHead

/-- Source function represented by a translated spine head. -/
@[reducible] noncomputable def denote (M : Model signature)
    (ν : TargetValuation M context) :
    FunctionHead signature context domain codomain →
      (Ty.arrow domain codomain).Denote M.Base
  | .value term => fromCanonical M _ ⟦term⟧[canonicalModel M, ν]
  | .sourceConstant constant => M.const constant

end FunctionHead

namespace SpineResult

/-- Source value represented by a translated, possibly incomplete spine. -/
@[reducible] noncomputable def denote (M : Model signature)
    (ν : TargetValuation M context)
    (spine : SpineResult signature context result) : result.Denote M.Base :=
  spine.arguments.applyUnary M ν (spine.head.denote M ν)

@[simp] theorem denote_snoc (M : Model signature)
    (ν : TargetValuation M context)
    (spine : SpineResult signature context (.arrow domain codomain))
    (argument : TargetTerm signature context domain)
    (generated : AuxiliaryTheory signature) :
    (spine.snoc argument generated).denote M ν =
      spine.denote M ν
        (fromCanonical M domain ⟦argument⟧[canonicalModel M, ν]) := by
  simp only [SpineResult.denote, SpineResult.snoc]
  exact TargetArguments.applyUnary_snoc M ν spine.arguments argument
    (spine.head.denote M ν)

/-- Finishing a ground spine preserves its represented source value. -/
theorem finish_denote (M : Model signature)
    (ν : TargetValuation M context)
    (spine : SpineResult signature context result)
    (ground : GroundResult result) :
    ⟦(spine.finish ground).term⟧[canonicalModel M, ν] =
      toCanonical M result (spine.denote M ν) := by
  rcases spine with ⟨headDomain, headCodomain, head, arguments, generated⟩
  cases head with
  | value term =>
      simpa only [SpineResult.finish, TermTranslation.ofGenerated,
        SpineResult.denote, FunctionHead.denote] using
        arguments.completeApp_denote M ν term ground
  | sourceConstant constant =>
      simpa only [SpineResult.finish, TermTranslation.ofGenerated,
        SpineResult.denote, FunctionHead.denote] using
        arguments.sourceApp_denote M ν constant ground

end SpineResult

@[simp] theorem finishClosure_term
    {target : Context} {domain codomain : Ty}
    (closure : Closure signature)
    (contextEq : closure.context = target)
    (domainEq : closure.domain = domain)
    (codomainEq : closure.codomain = codomain)
    (closureTerm : TargetTerm signature target (.arrow domain codomain))
    (equation : EquationResult signature) :
    (finishClosure closure contextEq domainEq codomainEq
      closureTerm equation).term = closureTerm := by
  subst contextEq
  subst domainEq
  subst codomainEq
  rfl

/-- Correctness proposition for spine translation, trivial at non-arrow types. -/
noncomputable def SpineCorrect (M : Model signature) {Γ : Context} {ty : Ty}
    (term : Term signature Γ ty) : Prop :=
  match ty with
  | .bool | .base _ => True
  | .arrow domain codomain =>
      ∀ {Δ : Context} (r : Renaming Γ Δ)
        (ν : TargetValuation M Δ),
        (translateSpineWith r term).denote M ν =
          ⟦term.rename r⟧[M, sourceValuation M ν]

/-- One structural induction establishes ordinary and spine denotation
correctness together. -/
private theorem denote_core (M : Model signature) :
    {Γ : Context} → {ty : Ty} → (term : Term signature Γ ty) →
    (∀ {Δ : Context} (r : Renaming Γ Δ)
      (ν : TargetValuation M Δ),
      ⟦(translateWith r term).term⟧[canonicalModel M, ν] =
        toCanonical M ty ⟦term.rename r⟧[M, sourceValuation M ν]) ∧
      SpineCorrect M term := by
  intro Γ ty term
  induction term with
  | var ref =>
      rename_i actualContext actualTy
      cases actualTy with
      | bool =>
          constructor
          · intro Δ r ν
            simp only [translateWith, TermTranslation.ofGenerated,
              FO.FamilyTerm.denote.eq_1, Term.rename, Term.denote,
              sourceValuation]
          · trivial
      | base sort =>
          constructor
          · intro Δ r ν
            simp only [translateWith, TermTranslation.ofGenerated,
              FO.FamilyTerm.denote.eq_1, Term.rename, Term.denote,
              sourceValuation]
          · trivial
      | arrow domain codomain =>
          constructor
          · intro Δ r ν
            simp only [translateWith, finishClosure_term, Term.rename]
            exact etaClosure_denote M (.var (r ref)) ν
          · intro Δ r ν
            rw [translateSpineWith.eq_1]
            simp only [SpineResult.denote, TargetArguments.applyUnary,
              FunctionHead.denote, Term.rename, Term.denote, sourceValuation]
            rw [FO.FamilyTerm.denote.eq_1]
  | const constant =>
      rename_i actualContext actualTy
      cases actualTy with
      | bool =>
          constructor
          · intro Δ r ν
            simpa only [translateWith, TermTranslation.ofGenerated,
              Term.rename, Term.denote, TargetArguments.applyUnary] using
              (TargetArguments.nil .bool).sourceApp_denote M ν constant .bool
          · trivial
      | base sort =>
          constructor
          · intro Δ r ν
            simpa only [translateWith, TermTranslation.ofGenerated,
              Term.rename, Term.denote, TargetArguments.applyUnary] using
              (TargetArguments.nil (.base sort)).sourceApp_denote
                M ν constant (.base sort)
          · trivial
      | arrow domain codomain =>
          constructor
          · intro Δ r ν
            simp only [translateWith, finishClosure_term, Term.rename]
            exact etaClosure_denote M (.const constant) ν
          · intro Δ r ν
            rw [translateSpineWith.eq_2]
            simp only [SpineResult.denote, TargetArguments.applyUnary,
              FunctionHead.denote, Term.rename, Term.denote]
  | boolLit value =>
      constructor
      · intro Δ r ν
        cases value <;>
          simp only [translateWith, TermTranslation.ofGenerated,
            FO.FamilyTerm.denote.eq_3, FO.FamilyTerm.denote.eq_4,
            Term.rename, Term.denote, toCanonical]
      · trivial
  | not body bodyIH =>
      constructor
      · intro Δ r ν
        simp only [translateWith, TermTranslation.replaceTerm,
          FO.FamilyTerm.denote.eq_5, Term.rename, Term.denote, toCanonical]
        rw [bodyIH.1 r ν]
      · trivial
  | and left right leftIH rightIH =>
      constructor
      · intro Δ r ν
        simp only [translateWith, TermTranslation.combine,
          FO.FamilyTerm.denote.eq_6, Term.rename, Term.denote, toCanonical]
        rw [leftIH.1 r ν, rightIH.1 r ν]
      · trivial
  | or left right leftIH rightIH =>
      constructor
      · intro Δ r ν
        simp only [translateWith, TermTranslation.combine,
          FO.FamilyTerm.denote.eq_7, Term.rename, Term.denote, toCanonical]
        rw [leftIH.1 r ν, rightIH.1 r ν]
      · trivial
  | imp left right leftIH rightIH =>
      constructor
      · intro Δ r ν
        simp only [translateWith, TermTranslation.combine,
          FO.FamilyTerm.denote.eq_8, Term.rename, Term.denote, toCanonical]
        rw [leftIH.1 r ν, rightIH.1 r ν]
      · trivial
  | iff left right leftIH rightIH =>
      constructor
      · intro Δ r ν
        simp only [translateWith, TermTranslation.combine,
          FO.FamilyTerm.denote.eq_9, Term.rename, Term.denote, toCanonical]
        rw [leftIH.1 r ν, rightIH.1 r ν]
      · trivial
  | eq left right leftIH rightIH =>
      rename_i operandType
      constructor
      · intro Δ r ν
        cases operandType <;>
          simp only [translateWith.eq_13, translateWith.eq_14,
            translateWith.eq_15, TermTranslation.combine,
            TermTranslation.appendOutput, FO.FamilyTerm.denote.eq_10,
            Term.rename, Term.denote, toCanonical] <;>
          rw [leftIH.1 r ν, rightIH.1 r ν]
      · trivial
  | lam body bodyIH =>
      rename_i actualContext domain codomain
      constructor
      · intro Δ r ν
        simp only [translateWith, finishClosure_term, Term.rename]
        exact etaClosure_denote M (.lam (body.rename (Renaming.lift r))) ν
      · intro Δ r ν
        rw [translateSpineWith.eq_3]
        simp only [SpineResult.denote, TargetArguments.applyUnary,
          FunctionHead.denote, finishClosure_term, Term.rename]
        have closureCorrect := etaClosure_denote M
          (.lam (body.rename (Renaming.lift r))) ν
        have mapped := congrArg (fromCanonical M (.arrow domain codomain))
          closureCorrect
        exact mapped.trans (fromCanonical_toCanonical M _ _)
  | app fn argument fnIH argumentIH =>
      rename_i actualContext appDomain appCodomain
      cases appCodomain with
      | bool =>
          constructor
          · intro Δ r ν
            rw [translateWith.eq_17, SpineResult.finish_denote,
              SpineResult.denote_snoc, fnIH.2 r ν,
              argumentIH.1 r ν, fromCanonical_toCanonical]
            rfl
          · trivial
      | base sort =>
          constructor
          · intro Δ r ν
            rw [translateWith.eq_18, SpineResult.finish_denote,
              SpineResult.denote_snoc, fnIH.2 r ν,
              argumentIH.1 r ν, fromCanonical_toCanonical]
            rfl
          · trivial
      | arrow residualDomain residualCodomain =>
          constructor
          · intro Δ r ν
            rw [translateWith.eq_19]
            simp only [finishClosure_term, Term.rename]
            exact etaClosure_denote M
              (.app (fn.rename r) (argument.rename r)) ν
          · intro Δ r ν
            rw [translateSpineWith.eq_4, SpineResult.denote_snoc,
              fnIH.2 r ν, argumentIH.1 r ν,
              fromCanonical_toCanonical]
            rfl
  | forallE body bodyIH =>
      rename_i domain
      constructor
      · intro Δ r ν
        cases domain <;>
          simp only [translateWith.eq_20, TermTranslation.ofGenerated,
            FO.FamilyTerm.denote.eq_11, Term.rename, Term.denote,
            toCanonical] <;>
          apply propext <;>
          apply forall_congr' <;>
          intro value <;>
          have bodyCorrect := bodyIH.1 (Renaming.lift r)
            (targetExtend M ν value) <;>
          rw [sourceValuation_extend M ν value] at bodyCorrect <;>
          exact bodyCorrect.to_iff
      · trivial
  | existsE body bodyIH =>
      rename_i domain
      constructor
      · intro Δ r ν
        cases domain <;>
          simp only [translateWith.eq_21, TermTranslation.ofGenerated,
            FO.FamilyTerm.denote.eq_12, Term.rename, Term.denote,
            toCanonical] <;>
          apply propext <;>
          apply exists_congr <;>
          intro value <;>
          have bodyCorrect := bodyIH.1 (Renaming.lift r)
            (targetExtend M ν value) <;>
          rw [sourceValuation_extend M ν value] at bodyCorrect <;>
          exact bodyCorrect.to_iff
      · trivial

/-- The term component of translation denotes the renamed source term in the
canonical flattened model. -/
theorem translateWith_denote (M : Model signature)
    {Γ Δ : Context} {ty : Ty}
    (r : Renaming Γ Δ) (term : Term signature Γ ty)
    (ν : TargetValuation M Δ) :
    ⟦(translateWith r term).term⟧[canonicalModel M, ν] =
      toCanonical M ty ⟦term.rename r⟧[M, sourceValuation M ν] :=
  (denote_core M term).1 r ν

/-- A translated spine denotes the renamed higher-order application prefix. -/
theorem translateSpineWith_denote (M : Model signature)
    {Γ Δ : Context} {domain codomain : Ty}
    (r : Renaming Γ Δ)
    (term : Term signature Γ (.arrow domain codomain))
    (ν : TargetValuation M Δ) :
    (translateSpineWith r term).denote M ν =
      ⟦term.rename r⟧[M, sourceValuation M ν] :=
  (denote_core M term).2 r ν

/-- Canonical target valuation obtained by pointwise type erasure. -/
noncomputable def targetVal (M : Model signature) :
    {Γ : Context} → Valuation M.Base Γ →
      TargetValuation M Γ
  | [], _ => FO.Valuation.empty (canonicalCarriers M)
  | ty :: Γ, ρ =>
      targetExtend M
        (targetVal M (fun {_} ref => ρ (.there ref)))
        (toCanonical M ty (ρ .here))

@[simp] theorem sourceVal_targetVal_apply (M : Model signature) :
    {Γ : Context} → (ρ : Valuation M.Base Γ) →
    {ty : Ty} → (ref : Var Γ ty) →
    sourceValuation M (targetVal M ρ) ref = ρ ref
  | _ :: _, ρ, _, .here => by
      simp only [targetVal, targetExtend, sourceValuation,
        FO.Valuation.extend, targetVar, fromCanonical_toCanonical]
  | _ :: _, ρ, _, .there ref => by
      simpa only [targetVal, targetExtend, sourceValuation,
        FO.Valuation.extend, targetVar] using
        sourceVal_targetVal_apply M
          (fun {_} tailRef => ρ (.there tailRef)) ref

theorem sourceVal_targetVal (M : Model signature)
    (ρ : Valuation M.Base context) :
    (fun {ty} ref => sourceValuation M (targetVal M ρ) (ty := ty) ref) =
      (fun {ty} ref => ρ (ty := ty) ref) := by
  apply @funext Ty (fun ty => Var context ty → ty.Denote M.Base)
  intro ty
  funext ref
  exact sourceVal_targetVal_apply M ρ ref

/-- The same canonical valuation is related to its source valuation in the
unary reference model. -/
theorem targetVal_related (M : Model signature)
    (ρ : Valuation M.Base context) :
    ValuationRel M (Defunctionalization.canonicalModel M)
      (fun _ sourceValue targetValue => sourceValue = targetValue)
      ρ (targetVal M ρ) := by
  intro ty ref
  apply (Defunctionalization.canonical_valueRel_iff M ty _ _).2
  exact (sourceVal_targetVal_apply M ρ ref).symm

/-- Top-level flattened translation preserves denotation. -/
theorem translate_denote (M : Model signature)
    (term : Term signature context result)
    (ρ : Valuation M.Base context) :
    ⟦𝓕⟦term⟧.term⟧[canonicalModel M, targetVal M ρ] =
      toCanonical M result ⟦term⟧[M, ρ] := by
  rw [translate]
  rw [translateWith_denote]
  rw [sourceVal_targetVal]
  rw [Term.denote_rename]
  rfl

/-- Unary reference translation has the same canonical denotation. -/
theorem unary_denote (M : Model signature)
    (term : Term signature context result)
    (ρ : Valuation M.Base context) :
    ⟦𝒟⟦term⟧⟧[Defunctionalization.canonicalModel M, targetVal M ρ] =
      toCanonical M result ⟦term⟧[M, ρ] := by
  have related := fundamental (Defunctionalization.canonicalModelRelation M)
    term ρ (targetVal M ρ) (targetVal_related M ρ)
  have equality :=
    (Defunctionalization.canonical_valueRel_iff M result _ _).1 related
  have mapped := congrArg (toCanonical M result) equality
  exact (mapped.trans (toCanonical_fromCanonical M _ _)).symm

/-- The emitted flattened and unary reference translations agree
semantically in their canonical models. -/
theorem flattened_refines_unary (M : Model signature)
    (term : Term signature context result)
    (ρ : Valuation M.Base context) :
    ⟦𝓕⟦term⟧.term⟧[canonicalModel M, targetVal M ρ] =
      ⟦𝒟⟦term⟧⟧[Defunctionalization.canonicalModel M, targetVal M ρ] := by
  rw [translate_denote, unary_denote]

end Crush.Metatheory.Defunctionalization.Flattened
