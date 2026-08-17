import Crush

/-!
# Case study: Strata type matching

This is a dependency-free extraction of Strata's Lambda type-matching argument. It
retains recursive monotypes, simultaneous substitution, a state-threading matcher,
and its soundness, completeness, and occurs-check properties while abstracting away
Strata's hash-map and error-reporting infrastructure.

The definitions use `@[crush_unfold]`, whose relevance filtering supplies only the
equations reachable from each query. The proofs keep mutually recursive constructor
decomposition explicit while `crush` handles substitution extension, coverage and
disjointness invariants, state preservation across list elements, and occurs-check
arithmetic. All calls use proof reconstruction.

Source: [Strata](https://github.com/strata-org/Strata), files
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
  @[crush_unfold]
  def LMonoTy.subst (S : Subst) : LMonoTy → LMonoTy
    | .ftvar name => (S name).getD (.ftvar name)
    | .tcons name args => .tcons name (LMonoTys.subst S args)
    | .bitvec width => .bitvec width

  @[crush_unfold]
  def LMonoTys.subst (S : Subst) : LMonoTys → LMonoTys
    | [] => []
    | ty :: rest => LMonoTy.subst S ty :: LMonoTys.subst S rest
end

mutual
  @[crush_unfold]
  def LMonoTy.freeVars : LMonoTy → List TyIdentifier
    | .ftvar name => [name]
    | .tcons _ args => LMonoTys.freeVars args
    | .bitvec _ => []

  @[crush_unfold]
  def LMonoTys.freeVars : LMonoTys → List TyIdentifier
    | [] => []
    | ty :: rest => LMonoTy.freeVars ty ++ LMonoTys.freeVars rest
end

mutual
  @[crush_unfold]
  def LMonoTy.size : LMonoTy → Nat
    | .ftvar _ => 1
    | .tcons _ args => 1 + LMonoTys.size args
    | .bitvec _ => 1

  @[crush_unfold]
  def LMonoTys.size : LMonoTys → Nat
    | [] => 0
    | ty :: rest => LMonoTy.size ty + LMonoTys.size rest
end

@[crush_unfold]
def Subst.empty : Subst := fun _ => none

@[crush_unfold]
def Subst.insert (S : Subst) (name : TyIdentifier) (ty : LMonoTy) : Subst :=
  fun query => if query = name then some ty else S query

@[crush_unfold]
def Subst.Extends (new old : Subst) : Prop :=
  ∀ name ty, old name = some ty → new name = some ty

@[crush_unfold]
def Subst.Covers (S : Subst) (vars : List TyIdentifier) : Prop :=
  ∀ name, name ∈ vars → ∃ ty, S name = some ty

@[crush_unfold]
def VarsDisjoint (xs ys : List TyIdentifier) : Prop :=
  ∀ name, name ∈ xs → name ∉ ys

mutual
  @[crush_unfold]
  def LMonoTy.matchCore (S : Subst) : LMonoTy → LMonoTy → Option Subst
    | .ftvar name, target =>
        if name ∈ target.freeVars then
          none
        else
          match S name with
          | none => some (S.insert name target)
          | some bound => if bound = target then some S else none
    | .tcons name patterns, .tcons targetName targets =>
        if name = targetName then LMonoTys.matchCore S patterns targets else none
    | .bitvec width, .bitvec targetWidth =>
        if width = targetWidth then some S else none
    | _, _ => none

  @[crush_unfold]
  def LMonoTys.matchCore (S : Subst) : LMonoTys → LMonoTys → Option Subst
    | [], [] => some S
    | pattern :: patterns, target :: targets =>
        match LMonoTy.matchCore S pattern target with
        | some next => LMonoTys.matchCore next patterns targets
        | none => none
    | _, _ => none
end

theorem Subst.Extends.refl (S : Subst) : S.Extends S := by
  crush

theorem Subst.insert_extends (S : Subst) (name : TyIdentifier) (ty : LMonoTy)
    (hfresh : S name = none) :
    (S.insert name ty).Extends S := by
  crush

theorem Subst.extends_insert {S M : Subst} {name : TyIdentifier} {ty : LMonoTy}
    (hMS : M.Extends S) (hname : M name = some ty) :
    M.Extends (S.insert name ty) := by
  crush

theorem Subst.Covers.left_of_append {S : Subst} {xs ys : List TyIdentifier}
    (hcover : S.Covers (xs ++ ys)) :
    S.Covers xs := by
  crush [List.mem_append, *]

theorem Subst.Covers.right_of_append {S : Subst} {xs ys : List TyIdentifier}
    (hcover : S.Covers (xs ++ ys)) :
    S.Covers ys := by
  crush [List.mem_append, *]

theorem VarsDisjoint.left_of_append
    {xs xs' ys ys' : List TyIdentifier}
    (hdisj : VarsDisjoint (xs ++ xs') (ys ++ ys')) :
    VarsDisjoint xs ys := by
  crush [List.mem_append, *]

theorem VarsDisjoint.right_of_append
    {xs xs' ys ys' : List TyIdentifier}
    (hdisj : VarsDisjoint (xs ++ xs') (ys ++ ys')) :
    VarsDisjoint xs' ys' := by
  crush [List.mem_append, *]

theorem Subst.covers_ftvar (S : Subst) (name : TyIdentifier) (ty : LMonoTy)
    (hfind : S name = some ty) :
    S.Covers (LMonoTy.ftvar name).freeVars := by
  crush [List.mem_singleton, *]

mutual
  theorem LMonoTy.subst_eq_of_extends
      {S M : Subst} (ty : LMonoTy)
      (hMS : M.Extends S) (hcover : S.Covers ty.freeVars) :
      LMonoTy.subst M ty = LMonoTy.subst S ty := by
    cases ty with
    | ftvar name =>
      simp only [LMonoTy.freeVars, LMonoTy.subst,
        Subst.Extends, Subst.Covers] at *
      crush [List.mem_singleton, *]
    | bitvec _ => rfl
    | tcons name args =>
      have ih := LMonoTys.subst_eq_of_extends args hMS hcover
      crush

  theorem LMonoTys.subst_eq_of_extends
      {S M : Subst} (tys : LMonoTys)
      (hMS : M.Extends S) (hcover : S.Covers tys.freeVars) :
      LMonoTys.subst M tys = LMonoTys.subst S tys := by
    cases tys with
    | nil => rfl
    | cons ty rest =>
      have ihHead := LMonoTy.subst_eq_of_extends (S := S) (M := M) ty hMS
      have ihTail := LMonoTys.subst_eq_of_extends (S := S) (M := M) rest hMS
      crush [List.mem_append, *]
end

mutual
  theorem LMonoTy.matchCore_sound
      (S : Subst) (pattern target : LMonoTy) (result : Subst)
      (hmatch : LMonoTy.matchCore S pattern target = some result) :
      result.Extends S ∧
        result.Covers pattern.freeVars ∧
        LMonoTy.subst result pattern = target := by
    cases pattern with
    | ftvar name =>
      by_cases hoccurs : name ∈ target.freeVars
      · simp [LMonoTy.matchCore, hoccurs] at hmatch
      · cases hfind : S name with
        | none =>
          simp [LMonoTy.matchCore, hoccurs, hfind] at hmatch
          subst result
          exact ⟨Subst.insert_extends S name target hfind,
            Subst.covers_ftvar _ name target (by simp [Subst.insert]),
            by simp [LMonoTy.subst, Subst.insert]⟩
        | some bound =>
          by_cases heq : bound = target
          · simp [LMonoTy.matchCore, hoccurs, hfind, heq] at hmatch
            subst result
            exact ⟨Subst.Extends.refl S,
              Subst.covers_ftvar S name bound hfind,
              by simp [LMonoTy.subst, hfind, heq]⟩
          · simp [LMonoTy.matchCore, hoccurs, hfind, heq] at hmatch
    | bitvec width =>
      cases target <;>
        simp only [LMonoTy.matchCore, LMonoTy.freeVars, LMonoTy.subst] at hmatch ⊢
      all_goals try split at hmatch
      all_goals simp_all [Subst.Extends, Subst.Covers]
    | tcons name patterns =>
      cases target with
      | tcons targetName targets =>
        by_cases heq : name = targetName
        · subst targetName
          simp only [LMonoTy.matchCore, ↓reduceIte] at hmatch
          have hargs :=
            LMonoTys.matchCore_sound S patterns targets result hmatch
          simpa only [LMonoTy.freeVars, LMonoTy.subst,
            LMonoTy.tcons.injEq, true_and] using hargs
        · simp [LMonoTy.matchCore, heq] at hmatch
      | ftvar _ | bitvec _ =>
        simp [LMonoTy.matchCore] at hmatch

  theorem LMonoTys.matchCore_sound
      (S : Subst) (patterns targets : LMonoTys) (result : Subst)
      (hmatch : LMonoTys.matchCore S patterns targets = some result) :
      result.Extends S ∧
        result.Covers (LMonoTys.freeVars patterns) ∧
        LMonoTys.subst result patterns = targets := by
    cases patterns with
    | nil =>
      cases targets <;>
        simp_all [LMonoTys.matchCore, Subst.Extends, Subst.Covers,
          LMonoTys.freeVars, LMonoTys.subst]
    | cons pattern patterns =>
      cases targets with
      | nil =>
        simp [LMonoTys.matchCore] at hmatch
      | cons target targets =>
        cases hhead : LMonoTy.matchCore S pattern target with
        | none =>
          simp [LMonoTys.matchCore, hhead] at hmatch
        | some next =>
          simp only [LMonoTys.matchCore, hhead] at hmatch
          have hhead' := LMonoTy.matchCore_sound S pattern target next hhead
          have htail := LMonoTys.matchCore_sound next patterns targets result hmatch
          have hstable :=
            LMonoTy.subst_eq_of_extends pattern htail.1 hhead'.2.1
          simp only [LMonoTys.freeVars, LMonoTys.subst,
            Subst.Extends, Subst.Covers] at hhead' htail ⊢
          set_option crush.autoUnfold false in
            crush [List.mem_append, *]
end

mutual
  theorem LMonoTy.matchCore_complete
      (S M : Subst) (pattern target : LMonoTy)
      (hMS : M.Extends S)
      (hdisj : VarsDisjoint pattern.freeVars target.freeVars)
      (hmatch : LMonoTy.subst M pattern = target) :
      ∃ result,
        LMonoTy.matchCore S pattern target = some result ∧
        M.Extends result := by
    cases pattern with
    | ftvar name =>
      cases hvalue : M name with
      | none =>
        simp [LMonoTy.subst, hvalue] at hmatch
        subst target
        exact False.elim ((hdisj name (by simp [LMonoTy.freeVars]))
          (by simp [LMonoTy.freeVars]))
      | some value =>
        have hvalueEq : value = target := by
          simpa [LMonoTy.subst, hvalue] using hmatch
        subst value
        have hoccurs : name ∉ target.freeVars :=
          hdisj name (by simp [LMonoTy.freeVars])
        cases hfind : S name with
        | none =>
          refine ⟨S.insert name target, ?_, Subst.extends_insert hMS hvalue⟩
          simp [LMonoTy.matchCore, hoccurs, hfind]
        | some bound =>
          refine ⟨S, ?_, hMS⟩
          simp_all [LMonoTy.matchCore, Subst.Extends]
    | bitvec width =>
      cases target <;>
        simp_all [LMonoTy.subst, LMonoTy.matchCore]
    | tcons name patterns =>
      cases target with
      | tcons targetName targets =>
        simp only [LMonoTy.subst, LMonoTy.tcons.injEq] at hmatch
        obtain ⟨rfl, hmatch⟩ := hmatch
        obtain ⟨result, hresult, hMresult⟩ :=
          LMonoTys.matchCore_complete S M patterns targets
            hMS hdisj hmatch
        exact ⟨result, by simpa [LMonoTy.matchCore] using hresult, hMresult⟩
      | ftvar _ | bitvec _ =>
        simp [LMonoTy.subst] at hmatch

  theorem LMonoTys.matchCore_complete
      (S M : Subst) (patterns targets : LMonoTys)
      (hMS : M.Extends S)
      (hdisj : VarsDisjoint (LMonoTys.freeVars patterns)
        (LMonoTys.freeVars targets))
      (hmatch : LMonoTys.subst M patterns = targets) :
      ∃ result,
        LMonoTys.matchCore S patterns targets = some result ∧
        M.Extends result := by
    cases patterns with
    | nil =>
      cases targets <;>
        simp_all [LMonoTys.subst, LMonoTys.matchCore]
    | cons pattern patterns =>
      cases targets with
      | nil =>
        simp [LMonoTys.subst] at hmatch
      | cons target targets =>
        simp only [LMonoTys.subst, List.cons.injEq] at hmatch
        simp only [LMonoTys.freeVars] at hdisj
        obtain ⟨next, hnext, hMnext⟩ :=
          LMonoTy.matchCore_complete S M pattern target
            hMS (VarsDisjoint.left_of_append hdisj) hmatch.1
        obtain ⟨result, hresult, hMresult⟩ :=
          LMonoTys.matchCore_complete next M patterns targets
            hMnext (VarsDisjoint.right_of_append hdisj) hmatch.2
        refine ⟨result, ?_, hMresult⟩
        simp [LMonoTys.matchCore, hnext, hresult]
end

theorem LMonoTy.matching_sound
    (pattern target : LMonoTy) (result : Subst)
    (hmatch : LMonoTy.matchCore Subst.empty pattern target = some result) :
    LMonoTy.subst result pattern = target :=
  (LMonoTy.matchCore_sound Subst.empty pattern target result hmatch).2.2

theorem LMonoTy.matching_complete
    (pattern target : LMonoTy) (M : Subst)
    (hdisj : VarsDisjoint pattern.freeVars target.freeVars)
    (hmatch : LMonoTy.subst M pattern = target) :
    ∃ result,
      LMonoTy.matchCore Subst.empty pattern target = some result ∧
      LMonoTy.subst result pattern = target := by
  have hempty : M.Extends Subst.empty := by
    crush
  obtain ⟨result, hresult, _⟩ :=
    LMonoTy.matchCore_complete Subst.empty M pattern target
      hempty hdisj hmatch
  exact ⟨result, hresult,
    LMonoTy.matching_sound pattern target result hresult⟩

mutual
  theorem LMonoTy.subst_ftvar_size_le_of_mem
      (S : Subst) (id : TyIdentifier) (ty : LMonoTy)
      (h : id ∈ LMonoTy.freeVars ty) :
      LMonoTy.size (LMonoTy.subst S (.ftvar id)) ≤
        LMonoTy.size (LMonoTy.subst S ty) := by
    cases ty with
    | ftvar name => simp_all [LMonoTy.freeVars]
    | bitvec width => simp_all [LMonoTy.freeVars]
    | tcons name args =>
      simp only [LMonoTy.freeVars] at h
      have hargs := LMonoTys.subst_ftvar_size_le_of_mem S id args h
      simp only [LMonoTy.subst, LMonoTy.size] at hargs ⊢
      set_option crush.autoUnfold false in crush

  theorem LMonoTys.subst_ftvar_size_le_of_mem
      (S : Subst) (id : TyIdentifier) (tys : LMonoTys)
      (h : id ∈ LMonoTys.freeVars tys) :
      LMonoTy.size (LMonoTy.subst S (.ftvar id)) ≤
        LMonoTys.size (LMonoTys.subst S tys) := by
    cases tys with
    | nil => simp_all [LMonoTys.freeVars]
    | cons ty rest =>
      have hhead := LMonoTy.subst_ftvar_size_le_of_mem S id ty
      have htail := LMonoTys.subst_ftvar_size_le_of_mem S id rest
      simp only [LMonoTys.freeVars, List.mem_append] at h
      simp only [LMonoTys.subst, LMonoTys.size, LMonoTy.subst] at hhead htail ⊢
      crush
end

theorem LMonoTy.subst_ftvar_ne_of_occurs
    (S : Subst) (id : TyIdentifier) (ty : LMonoTy)
    (hoccurs : id ∈ LMonoTy.freeVars ty)
    (hne : ty ≠ .ftvar id) :
    LMonoTy.subst S (.ftvar id) ≠ LMonoTy.subst S ty := by
  cases ty with
  | ftvar name => simp_all [LMonoTy.freeVars]
  | bitvec width => simp_all [LMonoTy.freeVars]
  | tcons name args =>
    intro heq
    simp only [LMonoTy.freeVars] at hoccurs
    have hle := LMonoTys.subst_ftvar_size_le_of_mem S id args hoccurs
    have hsize := congrArg LMonoTy.size heq
    crush

theorem LMonoTy.matchCore_rejects_cycle
    (S : Subst) (id : TyIdentifier) (ty : LMonoTy)
    (hoccurs : id ∈ LMonoTy.freeVars ty) :
    LMonoTy.matchCore S (.ftvar id) ty = none := by
  crush

end

/-- info: 'StrataCaseStudy.LMonoTy.matching_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LMonoTy.matching_complete

end StrataCaseStudy
