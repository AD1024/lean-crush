/-
Copyright Strata Contributors

SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Crush

/-!
# Case study: Strata type matching

This is a dependency-free extraction of proof patterns from Strata's Lambda type
unifier. It retains the recursive monotype, simultaneous substitution, structural
matching, and occurs-check arguments while abstracting away Strata's hash-map and
error-reporting infrastructure.

The recursive decomposition is proved manually. `crush` is used only after each
recursive definition has been exposed, for constructor, Boolean, and arithmetic
leaves. All calls use proof reconstruction.

Source: [Strata](https://github.com/AD1024/Strata), files
`Strata/DL/Lambda/LTy.lean`, `LTyUnify.lean`, and `LTyUnifyProps.lean`.
-/

namespace StrataCaseStudy

set_option crush.trust "reconstruct"
set_option crush.timeout 15

noncomputable section

abbrev TyIdentifier := String

inductive LMonoTy where
  | ftvar (name : TyIdentifier)
  | tcons (name : String) (args : List LMonoTy)
  | bitvec (size : Nat)
  deriving Repr

noncomputable instance : DecidableEq LMonoTy := Classical.typeDecidableEq LMonoTy

abbrev LMonoTys := List LMonoTy
abbrev Subst := TyIdentifier → Option LMonoTy

mutual
  def LMonoTy.subst (S : Subst) : LMonoTy → LMonoTy
    | .ftvar name => (S name).getD (.ftvar name)
    | .tcons name args => .tcons name (LMonoTys.subst S args)
    | .bitvec width => .bitvec width

  def LMonoTys.subst (S : Subst) : LMonoTys → LMonoTys
    | [] => []
    | ty :: rest => LMonoTy.subst S ty :: LMonoTys.subst S rest
end

mutual
  def LMonoTy.freeVars : LMonoTy → List TyIdentifier
    | .ftvar name => [name]
    | .tcons _ args => LMonoTys.freeVars args
    | .bitvec _ => []

  def LMonoTys.freeVars : LMonoTys → List TyIdentifier
    | [] => []
    | ty :: rest => LMonoTy.freeVars ty ++ LMonoTys.freeVars rest
end

mutual
  def LMonoTy.size : LMonoTy → Nat
    | .ftvar _ => 1
    | .tcons _ args => 1 + LMonoTys.size args
    | .bitvec _ => 1

  def LMonoTys.size : LMonoTys → Nat
    | [] => 0
    | ty :: rest => LMonoTy.size ty + LMonoTys.size rest
end

mutual
  def LMonoTy.matches (S : Subst) : LMonoTy → LMonoTy → Bool
    | .ftvar name, target =>
        decide (LMonoTy.subst S (.ftvar name) = target)
    | .tcons name patterns, .tcons targetName targets =>
        decide (name = targetName) && LMonoTys.matches S patterns targets
    | .bitvec width, .bitvec targetWidth =>
        decide (width = targetWidth)
    | _, _ => false

  def LMonoTys.matches (S : Subst) : LMonoTys → LMonoTys → Bool
    | [], [] => true
    | pattern :: patterns, target :: targets =>
        LMonoTy.matches S pattern target && LMonoTys.matches S patterns targets
    | _, _ => false
end

mutual
  theorem LMonoTy.matches_sound (S : Subst) (pattern target : LMonoTy)
      (h : LMonoTy.matches S pattern target = true) :
      LMonoTy.subst S pattern = target := by
    cases pattern with
    | ftvar name =>
      simp only [LMonoTy.matches, decide_eq_true_eq] at h
      exact h
    | bitvec width =>
      cases target with
      | bitvec targetWidth =>
        simp only [LMonoTy.matches, decide_eq_true_eq] at h
        simp only [LMonoTy.subst]
        crush [h]
      | ftvar _ | tcons _ _ =>
        simp only [LMonoTy.matches, Bool.false_eq_true] at h
    | tcons name patterns =>
      cases target with
      | tcons targetName targets =>
        simp only [LMonoTy.matches, Bool.and_eq_true, decide_eq_true_eq] at h
        have hargs := LMonoTys.matches_sound S patterns targets h.2
        simp only [LMonoTy.subst]
        crush [h.1, hargs]
      | ftvar _ | bitvec _ =>
        simp only [LMonoTy.matches, Bool.false_eq_true] at h

  theorem LMonoTys.matches_sound (S : Subst) (patterns targets : LMonoTys)
      (h : LMonoTys.matches S patterns targets = true) :
      LMonoTys.subst S patterns = targets := by
    cases patterns with
    | nil =>
      cases targets with
      | nil => rfl
      | cons _ _ =>
        simp only [LMonoTys.matches, Bool.false_eq_true] at h
    | cons pattern patterns =>
      cases targets with
      | nil =>
        simp only [LMonoTys.matches, Bool.false_eq_true] at h
      | cons target targets =>
        simp only [LMonoTys.matches, Bool.and_eq_true] at h
        have hhead := LMonoTy.matches_sound S pattern target h.1
        have htail := LMonoTys.matches_sound S patterns targets h.2
        simp only [LMonoTys.subst]
        crush [hhead, htail]
end

mutual
  theorem LMonoTy.matches_complete (S : Subst) (pattern target : LMonoTy)
      (h : LMonoTy.subst S pattern = target) :
      LMonoTy.matches S pattern target = true := by
    cases pattern with
    | ftvar name =>
      simp only [LMonoTy.matches, decide_eq_true_eq]
      exact h
    | bitvec width =>
      cases target with
      | bitvec targetWidth =>
        simp only [LMonoTy.subst, LMonoTy.bitvec.injEq] at h
        simp only [LMonoTy.matches, decide_eq_true_eq]
        crush [h]
      | ftvar _ | tcons _ _ =>
        simp only [LMonoTy.subst] at h
        contradiction
    | tcons name patterns =>
      cases target with
      | tcons targetName targets =>
        simp only [LMonoTy.subst, LMonoTy.tcons.injEq] at h
        have hargs := LMonoTys.matches_complete S patterns targets h.2
        simp only [LMonoTy.matches, Bool.and_eq_true, decide_eq_true_eq]
        crush [h.1, hargs]
      | ftvar _ | bitvec _ =>
        simp only [LMonoTy.subst] at h
        contradiction

  theorem LMonoTys.matches_complete (S : Subst) (patterns targets : LMonoTys)
      (h : LMonoTys.subst S patterns = targets) :
      LMonoTys.matches S patterns targets = true := by
    cases patterns with
    | nil =>
      cases targets with
      | nil => rfl
      | cons _ _ =>
        simp only [LMonoTys.subst] at h
        contradiction
    | cons pattern patterns =>
      cases targets with
      | nil =>
        simp only [LMonoTys.subst] at h
        contradiction
      | cons target targets =>
        simp only [LMonoTys.subst, List.cons.injEq] at h
        have hhead := LMonoTy.matches_complete S pattern target h.1
        have htail := LMonoTys.matches_complete S patterns targets h.2
        simp only [LMonoTys.matches, Bool.and_eq_true]
        crush [hhead, htail]
end

theorem LMonoTy.matches_iff (S : Subst) (pattern target : LMonoTy) :
    LMonoTy.matches S pattern target = true ↔
      LMonoTy.subst S pattern = target :=
  ⟨LMonoTy.matches_sound S pattern target,
    LMonoTy.matches_complete S pattern target⟩

mutual
  theorem LMonoTy.subst_ftvar_size_le_of_mem
      (S : Subst) (id : TyIdentifier) (ty : LMonoTy)
      (h : id ∈ LMonoTy.freeVars ty) :
      LMonoTy.size (LMonoTy.subst S (.ftvar id)) ≤
        LMonoTy.size (LMonoTy.subst S ty) := by
    cases ty with
    | ftvar name =>
      simp only [LMonoTy.freeVars, List.mem_singleton] at h
      subst name
      exact Nat.le_refl _
    | bitvec width =>
      simp only [LMonoTy.freeVars, List.not_mem_nil] at h
    | tcons name args =>
      simp only [LMonoTy.freeVars] at h
      have hargs := LMonoTys.subst_ftvar_size_le_of_mem S id args h
      simp only [LMonoTy.subst, LMonoTy.size] at hargs ⊢
      generalize LMonoTy.size ((S id).getD (.ftvar id)) = baseSize at hargs ⊢
      generalize LMonoTys.size (LMonoTys.subst S args) = argsSize at hargs ⊢
      crush [hargs]

  theorem LMonoTys.subst_ftvar_size_le_of_mem
      (S : Subst) (id : TyIdentifier) (tys : LMonoTys)
      (h : id ∈ LMonoTys.freeVars tys) :
      LMonoTy.size (LMonoTy.subst S (.ftvar id)) ≤
        LMonoTys.size (LMonoTys.subst S tys) := by
    cases tys with
    | nil =>
      simp only [LMonoTys.freeVars, List.not_mem_nil] at h
    | cons ty rest =>
      simp only [LMonoTys.freeVars, List.mem_append] at h
      simp only [LMonoTys.subst, LMonoTys.size]
      cases h with
      | inl hty =>
        have hhead := LMonoTy.subst_ftvar_size_le_of_mem S id ty hty
        crush [hhead]
      | inr hrest =>
        have htail := LMonoTys.subst_ftvar_size_le_of_mem S id rest hrest
        crush [htail]
end

theorem LMonoTy.subst_ftvar_ne_of_occurs
    (S : Subst) (id : TyIdentifier) (ty : LMonoTy)
    (hoccurs : id ∈ LMonoTy.freeVars ty)
    (hne : ty ≠ .ftvar id) :
    LMonoTy.subst S (.ftvar id) ≠ LMonoTy.subst S ty := by
  cases ty with
  | ftvar name =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hoccurs
    subst name
    exact False.elim (hne rfl)
  | bitvec width =>
    simp only [LMonoTy.freeVars, List.not_mem_nil] at hoccurs
  | tcons name args =>
    intro heq
    simp only [LMonoTy.freeVars] at hoccurs
    have hle := LMonoTys.subst_ftvar_size_le_of_mem S id args hoccurs
    have hlt :
        LMonoTy.size (LMonoTy.subst S (.ftvar id)) <
          LMonoTy.size (LMonoTy.subst S (.tcons name args)) := by
      simp only [LMonoTy.subst, LMonoTy.size] at hle ⊢
      generalize LMonoTy.size ((S id).getD (.ftvar id)) = baseSize at hle ⊢
      generalize LMonoTys.size (LMonoTys.subst S args) = argsSize at hle ⊢
      crush [hle]
    have hsize := congrArg LMonoTy.size heq
    crush [hlt, hsize]

theorem LMonoTy.occurs_check_rejects_cycle
    (S : Subst) (id : TyIdentifier) (ty : LMonoTy)
    (hoccurs : id ∈ LMonoTy.freeVars ty)
    (hne : ty ≠ .ftvar id) :
    LMonoTy.matches S (.ftvar id) (LMonoTy.subst S ty) = false := by
  have hne' := LMonoTy.subst_ftvar_ne_of_occurs S id ty hoccurs hne
  simpa only [LMonoTy.matches, decide_eq_false_iff_not] using hne'

end

/-- info: 'StrataCaseStudy.LMonoTy.occurs_check_rejects_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LMonoTy.occurs_check_rejects_cycle

end StrataCaseStudy
