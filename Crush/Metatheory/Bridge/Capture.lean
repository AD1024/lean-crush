import Crush.Translation.HOEncoding
import Crush.Metatheory.Defunctionalization.Collect

/-!
# Executable closure-capture refinement

This module specifies free-variable occurrence independently of the accumulator
used by production and proves that the actual total collector returns exactly
the occurring variables.  Production's eligibility filter is then characterized
as the conjunction of occurrence and SMT-local eligibility.

Ordering is not abstracted away: `collectFVarsOrdered` remains the executable
first-occurrence traversal consumed by `emitClosure`.  The membership theorem
establishes exactness, while the no-duplicate theorem below establishes that its
ordered output is a valid closure environment rather than a multiset.
-/

namespace Crush.Metatheory.Bridge

open Lean
open Crush.Metatheory.Defunctionalization

/-- Lean derives `BEq FVarId` from its sole `Name` field but does not publish the
corresponding lawfulness witness. The bridge needs that proposition-level fact. -/
instance : LawfulBEq FVarId where
  eq_of_beq := by
    intro left right equality
    cases left with
    | mk leftName =>
      cases right with
      | mk rightName =>
        simp only [BEq.beq] at equality
        cases Name.beq_iff_eq.mp equality
        rfl
  rfl := by
    intro value
    cases value with
    | mk name => exact Name.beq_iff_eq.mpr rfl

instance : DecidableEq FVarId := fun left right =>
  decidable_of_iff (left == right) beq_iff_eq

/-- Structural occurrence of a free-variable identity in a Lean expression.
Binder names and binder indices cannot bind an `FVarId`; occurrences in binder
types, values, and bodies are therefore all free occurrences. -/
def fvarOccurs (needle : FVarId) : Expr → Bool
  | .fvar found => found == needle
  | .app fn argument => fvarOccurs needle fn || fvarOccurs needle argument
  | .lam _ type body _ => fvarOccurs needle type || fvarOccurs needle body
  | .forallE _ type body _ => fvarOccurs needle type || fvarOccurs needle body
  | .letE _ type value body _ =>
      fvarOccurs needle type || fvarOccurs needle value || fvarOccurs needle body
  | .mdata _ body => fvarOccurs needle body
  | .proj _ _ body => fvarOccurs needle body
  | _ => false

/-- The production accumulator contains a variable exactly when it was already
present or occurs in the traversed expression. -/
theorem collectFVarsOrdered_go_mem (expression : Expr)
    (accumulator : Array FVarId) (needle : FVarId) :
    needle ∈ collectFVarsOrdered.go expression accumulator ↔
      needle ∈ accumulator ∨ fvarOccurs needle expression = true := by
  induction expression generalizing accumulator with
  | bvar | sort | const | mvar | lit => simp [collectFVarsOrdered.go, fvarOccurs]
  | fvar found =>
      simp only [collectFVarsOrdered.go, fvarOccurs]
      split <;> rename_i present
      · have foundMem : found ∈ accumulator :=
          Array.mem_of_contains_eq_true present
        constructor
        · exact fun membership => Or.inl membership
        · intro membership
          cases membership with
          | inl already => exact already
          | inr equality =>
              have : found = needle := eq_of_beq equality
              simpa [this] using foundMem
      · simp only [Array.mem_push, beq_iff_eq]
        exact or_congr_right eq_comm
  | app fn argument fnIH argumentIH =>
      simp [collectFVarsOrdered.go, fvarOccurs, fnIH, argumentIH, Bool.or_eq_true,
        or_assoc]
  | lam name type body binderInfo typeIH bodyIH =>
      simp [collectFVarsOrdered.go, fvarOccurs, typeIH, bodyIH, Bool.or_eq_true,
        or_assoc]
  | forallE name type body binderInfo typeIH bodyIH =>
      simp [collectFVarsOrdered.go, fvarOccurs, typeIH, bodyIH, Bool.or_eq_true,
        or_assoc]
  | letE name type value body nondep typeIH valueIH bodyIH =>
      simp [collectFVarsOrdered.go, fvarOccurs, typeIH, valueIH, bodyIH,
        Bool.or_eq_true, or_assoc]
  | mdata data body bodyIH =>
      simp [collectFVarsOrdered.go, fvarOccurs, bodyIH]
  | proj typeName index body bodyIH =>
      simp [collectFVarsOrdered.go, fvarOccurs, bodyIH]

/-- Exact membership specification for the collector actually used by the live
defunctionalization pass. -/
@[simp] theorem collectFVarsOrdered_mem (expression : Expr) (needle : FVarId) :
    needle ∈ collectFVarsOrdered expression ↔ fvarOccurs needle expression = true := by
  simpa [collectFVarsOrdered] using
    collectFVarsOrdered_go_mem expression #[] needle

/-- The accumulator traversal preserves uniqueness. Consequently, production's
capture order contains one parameter per free-variable identity. -/
theorem collectFVarsOrdered_go_nodup (expression : Expr)
    (accumulator : Array FVarId) (unique : accumulator.toList.Nodup) :
    (collectFVarsOrdered.go expression accumulator).toList.Nodup := by
  induction expression generalizing accumulator with
  | bvar | sort | const | mvar | lit => simpa [collectFVarsOrdered.go]
  | fvar found =>
      simp only [collectFVarsOrdered.go]
      split <;> rename_i present
      · exact unique
      · have absent : found ∉ accumulator := by
          intro membership
          exact present (Array.contains_eq_true_of_mem membership)
        have cross : ∀ item ∈ accumulator, ¬item = found := by
          intro item membership equality
          apply absent
          exact equality ▸ membership
        simpa [Array.toList_push, List.nodup_append] using And.intro unique cross
  | app fn argument fnIH argumentIH =>
      exact argumentIH _ (fnIH _ unique)
  | lam name type body binderInfo typeIH bodyIH =>
      exact bodyIH _ (typeIH _ unique)
  | forallE name type body binderInfo typeIH bodyIH =>
      exact bodyIH _ (typeIH _ unique)
  | letE name type value body nondep typeIH valueIH bodyIH =>
      exact bodyIH _ (valueIH _ (typeIH _ unique))
  | mdata data body bodyIH => exact bodyIH _ unique
  | proj typeName index body bodyIH => exact bodyIH _ unique

theorem collectFVarsOrdered_nodup (expression : Expr) :
    (collectFVarsOrdered expression).toList.Nodup := by
  apply collectFVarsOrdered_go_nodup
  simp

theorem selectClosureCaptures_nodup (expression : Expr)
    (eligible : FVarId → Bool) :
    (selectClosureCaptures expression eligible).toList.Nodup := by
  rw [selectClosureCaptures, Array.toList_filter]
  exact (collectFVarsOrdered_nodup expression).filter _

/-- Exact membership specification for the eligibility-filtered capture list
actually used by `emitClosure`. -/
@[simp] theorem selectClosureCaptures_mem (expression : Expr)
    (eligible : FVarId → Bool) (needle : FVarId) :
    needle ∈ selectClosureCaptures expression eligible ↔
      fvarOccurs needle expression = true ∧ eligible needle = true := by
  simp only [selectClosureCaptures, Array.mem_filter]
  rw [collectFVarsOrdered_mem]

/-! ## Exact bridge to intrinsic closure contexts -/

/-- A position-preserving correspondence between an intrinsic de Bruijn context
and the live free variables representing it. The intrinsic type at each position
is definitionally derived from the retained live type bridge. -/
inductive ContextBridge : Context → Type where
  | nil : ContextBridge []
  | cons {context : Context}
      (fvar : FVarId) (type : TypeBridge)
      (tail : ContextBridge context) : ContextBridge (type.ty :: context)

namespace ContextBridge

def fvar : {context : Context} → ContextBridge context → PackedVar context → FVarId
  | _ :: _, .cons fvar _ _, .pack (.here) => fvar
  | _ :: _, .cons _ _ tail, .pack (.there ref) => tail.fvar (.pack ref)

def type : {context : Context} → ContextBridge context → PackedVar context → TypeBridge
  | _ :: _, .cons _ type _, .pack (.here) => type
  | _ :: _, .cons _ _ tail, .pack (.there ref) => tail.type (.pack ref)

theorem type_eq {context : Context} (bridge : ContextBridge context)
    (item : PackedVar context) : (bridge.type item).ty = item.type := by
  cases bridge with
  | nil =>
      cases item with
      | pack ref => exact nomatch ref
  | cons fvar type tail =>
      cases item with
      | pack ref =>
          cases ref with
          | here => rfl
          | there ref => exact tail.type_eq (.pack ref)

/-- Live variables in intrinsic context order. -/
def fvars : {context : Context} → ContextBridge context → List FVarId
  | [], .nil => []
  | _ :: _, .cons fvar _ tail => fvar :: tail.fvars

/-- Live type bridges in the same intrinsic context order. -/
def types : {context : Context} → ContextBridge context → List TypeBridge
  | [], .nil => []
  | _ :: _, .cons _ type tail => type :: tail.types

def Nodup {context : Context} (bridge : ContextBridge context) : Prop :=
  bridge.fvars.Nodup

end ContextBridge

/-- The exact executable refinement obligation for one modeled closure.

The right side is derived exclusively from the intrinsic collector's typed
references. The left side is the actual production function used by
`emitClosure`. Thus a term reifier need only construct this certificate; it
cannot silently choose a different capture set or order. -/
structure ClosureCaptureCertificate {signature : Signature}
    (closure : Closure signature) where
  lambda : Expr
  context : ContextBridge closure.context
  eligible : FVarId → Bool
  contextNodup : context.Nodup
  captures_eq :
    (selectClosureCaptures lambda eligible).toList =
      closure.captureRefs.map context.fvar

namespace ClosureCaptureCertificate

/-- Live type bridges in the exact capture order certified above. -/
def captureTypeBridges {signature : Signature} {closure : Closure signature}
    (certificate : ClosureCaptureCertificate closure) : List TypeBridge :=
  closure.captureRefs.map certificate.context.type

theorem captureTypeBridges_types {signature : Signature} {closure : Closure signature}
    (certificate : ClosureCaptureCertificate closure) :
    certificate.captureTypeBridges.map TypeBridge.ty = closure.captureTypes := by
  simp only [captureTypeBridges, Closure.captureTypes, List.map_map]
  apply List.map_congr_left
  intro item membership
  exact certificate.context.type_eq item

/-- Consequently, mapping the certified live capture types to FO sorts produces
the exact constructor telescope selected by the verified pass. -/
theorem closureDecl_args {signature : Signature} {closure : Closure signature}
    (certificate : ClosureCaptureCertificate closure) :
    (FO.closureDecl closure.captureTypes closure.domain closure.codomain).args =
      certificate.captureTypeBridges.map (FO.FOSort.ofTy ∘ TypeBridge.ty) := by
  rw [FO.closureDecl_args, ← certificate.captureTypeBridges_types]
  exact List.map_map

theorem capture_count {signature : Signature} {closure : Closure signature}
    (certificate : ClosureCaptureCertificate closure) :
    (selectClosureCaptures certificate.lambda certificate.eligible).size =
      closure.captures.length := by
  change (selectClosureCaptures certificate.lambda certificate.eligible).toList.length = _
  rw [certificate.captures_eq, List.length_map,
    Closure.captureRefs_length]

theorem captures_nodup {signature : Signature} {closure : Closure signature}
    (certificate : ClosureCaptureCertificate closure) :
    (closure.captureRefs.map certificate.context.fvar).Nodup := by
  rw [← certificate.captures_eq]
  exact selectClosureCaptures_nodup certificate.lambda certificate.eligible

end ClosureCaptureCertificate

end Crush.Metatheory.Bridge
