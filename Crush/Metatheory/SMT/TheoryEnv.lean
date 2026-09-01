import Crush.Metatheory.SMT.Theory
import Crush.SMT.TheoryReqs

/-!
# Registered SMT theories and finite combinations

The syntax registry is paired with one semantic theory per modeled entry.
`Comb` is a finite, dependency-closed selection of those entries. Its models
are full SMT models whose reduct to every selected signature satisfies that
component theory. This is the finite reduct-based combination used by the
lowering theorem.
-/

namespace Crush.Metatheory.SMT.Theory

open Crush.SMT
open Crush.SMT.Theory

/-- Characteristic function of a finite set of modeled theory entries. -/
abbrev Reqs (sigEnv : SigEnv) := Fin sigEnv.modeled.length → Bool

/-- Dependency closure supplied with a finite registry. Keeping the closure
operator and its laws together lets small registries use reducible definitions
without introducing quotient-backed finite sets or opaque hashing. -/
structure Closure (sigEnv : SigEnv) where
  close : Reqs sigEnv → Reqs sigEnv
  includes : ∀ requirements theory,
    requirements theory = true → close requirements theory = true
  deps : ∀ requirements theory,
    close requirements theory = true →
      ∀ dependency, dependency ∈ sigEnv.depIds theory →
        close requirements dependency = true
  least : ∀ requirements (closed : Reqs sigEnv),
    (∀ theory, requirements theory = true → closed theory = true) →
    (∀ theory, closed theory = true →
      ∀ dependency, dependency ∈ sigEnv.depIds theory →
        closed dependency = true) →
    ∀ theory, close requirements theory = true → closed theory = true

/-- A syntax registry together with semantic declarations and a checked
dependency-closure operation. The dependent `decl` field fixes each semantic
theory to the signature of the corresponding syntax entry. -/
structure Env where
  sigEnv : SigEnv
  sig_wf : sigEnv.WF
  decl : (theory : Fin sigEnv.modeled.length) →
    Crush.Metatheory.SMT.Theory (sigEnv.modeled.get theory).sig
  closure : Closure sigEnv

/-- A dependency-closed finite combination of registered SMT theories. -/
structure Comb (env : Env) where
  active : Reqs env.sigEnv
  deps : ∀ theory, active theory = true →
    ∀ dependency, dependency ∈ env.sigEnv.depIds theory →
      active dependency = true

namespace Comb

/-- Two combinations are equal when they select the same entries. -/
@[ext] theorem ext {env : Env} {left right : Comb env}
    (equal : ∀ theory, left.active theory = right.active theory) :
    left = right := by
  cases left with
  | mk leftActive leftDeps =>
    cases right with
    | mk rightActive rightDeps =>
      have activeEq : leftActive = rightActive := funext equal
      subst rightActive
      rfl

/-- Combination with no optional interpreted theory. -/
def empty (env : Env) : Comb env where
  active := fun _ => false
  deps := by simp

/-- Close an arbitrary finite requirement set under registered dependencies. -/
def close (env : Env) (requirements : Reqs env.sigEnv) : Comb env where
  active := env.closure.close requirements
  deps := env.closure.deps requirements

/-- Combination induced by every modeled theory used in a command array. -/
def ofCommands (env : Env) (commands : Array Command) : Comb env :=
  close env (env.sigEnv.usesCommands commands)

/-- Union of two theory combinations. -/
def union {env : Env} (left right : Comb env) : Comb env where
  active := fun theory => left.active theory || right.active theory
  deps := by
    intro theory active dependency member
    simp only [Bool.or_eq_true] at active ⊢
    cases active with
    | inl leftActive => exact Or.inl (left.deps theory leftActive dependency member)
    | inr rightActive => exact Or.inr (right.deps theory rightActive dependency member)

@[simp] theorem empty_active {env : Env} (theory : Fin env.sigEnv.modeled.length) :
    (empty env).active theory = false := rfl

@[simp] theorem close_active {env : Env} (requirements : Reqs env.sigEnv)
    (theory : Fin env.sigEnv.modeled.length) :
    (close env requirements).active theory =
      env.closure.close requirements theory := rfl

@[simp] theorem union_active {env : Env} (left right : Comb env)
    (theory : Fin env.sigEnv.modeled.length) :
    (union left right).active theory =
      (left.active theory || right.active theory) := rfl

/-- Closing requirements never omits a directly used theory. -/
theorem active_of_required {env : Env} {requirements : Reqs env.sigEnv}
    {theory : Fin env.sigEnv.modeled.length}
    (required : requirements theory = true) :
    (close env requirements).active theory = true :=
  env.closure.includes requirements theory required

/-- Command-induced combinations never omit a theory found by syntax
traversal. -/
theorem active_of_used {env : Env} {commands : Array Command}
    {theory : Fin env.sigEnv.modeled.length}
    (used : env.sigEnv.usesCommands commands theory = true) :
    (ofCommands env commands).active theory = true :=
  active_of_required used

theorem union_empty_left {env : Env} (comb : Comb env) :
    union (empty env) comb = comb := by
  ext theory
  simp [union]

theorem union_empty_right {env : Env} (comb : Comb env) :
    union comb (empty env) = comb := by
  ext theory
  simp [union]

theorem union_assoc {env : Env} (first second third : Comb env) :
    union (union first second) third = union first (union second third) := by
  ext theory
  simp [union, Bool.or_assoc]

theorem union_comm {env : Env} (left right : Comb env) :
    union left right = union right left := by
  ext theory
  simp [union, Bool.or_comm]

theorem union_idem {env : Env} (comb : Comb env) :
    union comb comb = comb := by
  ext theory
  simp [union]

/-- A full model of a finite combination: the logical model laws hold, and
the reduct to every selected signature is a model of that component theory. -/
structure Models {env : Env} (comb : Comb env) (model : Model) : Prop where
  wf : model.WF
  theory : ∀ theory, comb.active theory = true →
    (env.decl theory).Models
      (Model.reduct model (env.sigEnv.modeled.get theory).sig)

/-- A well-typed command sequence with no model of its command-induced theory
combination. -/
structure CommandsUnsat (env : Env) (commands : Array Command) : Prop where
  inFragment : CommandsInFragment commands
  wellTyped : CommandsWellTyped commands
  noModel : ∀ model : Model, Models (ofCommands env commands) model →
    ¬model.SatisfiesCommands commands

/-- Models of an empty optional combination are exactly well-formed logical
models. -/
theorem models_empty_iff {env : Env} {model : Model} :
    Models (empty env) model ↔ model.WF := by
  constructor
  · exact Models.wf
  · intro wf
    exact ⟨wf, by simp⟩

/-- Every semantic registry has a model of its empty optional combination. -/
theorem models_empty_exists (env : Env) :
    ∃ model : Model, Models (empty env) model := by
  rcases Model.wf_exists with ⟨model, wf⟩
  exact ⟨model, models_empty_iff.mpr wf⟩

/-- Reduct semantics turns finite union into conjunction of component model
classes. This is the n-ary form of `Theory.sum`. -/
theorem models_union_iff {env : Env} {left right : Comb env} {model : Model} :
    Models (union left right) model ↔ Models left model ∧ Models right model := by
  constructor
  · intro models
    constructor
    · exact ⟨models.wf, fun theory active =>
        models.theory theory (by simp [union, active])⟩
    · exact ⟨models.wf, fun theory active =>
        models.theory theory (by simp [union, active])⟩
  · rintro ⟨leftModels, rightModels⟩
    refine ⟨leftModels.wf, ?_⟩
    intro theory active
    simp only [union_active, Bool.or_eq_true] at active
    cases active with
    | inl leftActive => exact leftModels.theory theory leftActive
    | inr rightActive => exact rightModels.theory theory rightActive

end Comb

end Crush.Metatheory.SMT.Theory
