import Crush.Metatheory.Defunctionalization.Syntax

/-!
# Closure capture

This module describes a lambda occurrence, computes its exact free-variable
captures, and defines the declaration shapes used by flattened translation.
-/

namespace Crush.Metatheory.Defunctionalization

variable {types : List Ty} {ty domain codomain : Ty}
variable {signature : Signature} {context : Context}

/-- The numeric position of a typed de Bruijn reference. -/
def refToNat {types : List Ty} {ty : Ty} (ref : Ref types ty) : Nat :=
  match ref with
  | .here => 0
  | .there ref => refToNat ref + 1

/-- Remove the variable introduced by a binder and re-index references to its
outer context. -/
def leaveBinder (indices : List Nat) : List Nat :=
  indices.filterMap fun
    | 0 => none
    | index + 1 => some index

/-- Free local-variable positions of a term, with duplicates removed.  The order
is deterministic and follows the first left-to-right occurrence in the syntax. -/
def freeVarIndices {signature : Signature} {context : Context} {ty : Ty}
    (term : Term signature context ty) : List Nat :=
  match term with
  | .var ref => [refToNat ref]
  | .const _ | .boolLit _ => []
  | .not body => freeVarIndices body
  | .and left right | .or left right | .imp left right | .iff left right |
      .eq left right =>
      (freeVarIndices left ++ freeVarIndices right).eraseDups
  | .lam body | .forallE body | .existsE body =>
      (leaveBinder (freeVarIndices body)).eraseDups
  | .app fn argument =>
      (freeVarIndices fn ++ freeVarIndices argument).eraseDups

/-- A typed lambda occurrence.  `captures` contains positions in `context`, not
positions in the lambda body's extended context. -/
structure Closure (signature : Signature) where
  context : Context
  domain : Ty
  codomain : Ty
  body : Term signature (domain :: context) codomain

namespace Closure

/-- Construct a closure descriptor and compute its exact outer captures. -/
@[reducible] def ofBody {signature : Signature} {context : Context} {domain codomain : Ty}
    (body : Term signature (domain :: context) codomain) : Closure signature :=
  { context, domain, codomain, body }

/-- Exactly the outer variables referenced by the lambda body. -/
def captures (closure : Closure signature) : List Nat :=
  leaveBinder (freeVarIndices closure.body)

end Closure

/-- A variable whose type is existentially packaged but whose context remains
intrinsically fixed. -/
inductive PackedVar (context : Context) where
  | pack {ty : Ty} : Var context ty → PackedVar context

namespace PackedVar

@[reducible] def type : PackedVar context → Ty
  | .pack (ty := ty) _ => ty

@[reducible] def index : PackedVar context → Nat
  | .pack ref => refToNat ref

/-- Total lookup of a typed variable by its numeric de Bruijn position. -/
def at? : (context : Context) → Nat → Option (PackedVar context)
  | [], _ => none
  | _ :: _, 0 => some (.pack .here)
  | _ :: tail, index + 1 =>
      (at? tail index).map fun
        | .pack ref => .pack (.there ref)

end PackedVar

namespace Closure

/-- Typed references corresponding to the closure's exact capture positions. -/
def captureRefs (closure : Closure signature) : List (PackedVar closure.context) :=
  closure.captures.filterMap (PackedVar.at? closure.context)

/-- Source types of captured variables, derived from typed references rather
than independently indexing the context. -/
@[reducible] def captureTypes (closure : Closure signature) : List Ty :=
  closure.captureRefs.map PackedVar.type

end Closure

/-- A complete source arrow type used as the key of one target function sort and
its flattened application symbol. -/
structure Arrow where
  domain : Ty
  codomain : Ty
  deriving BEq, DecidableEq, Hashable, Repr

/-- A source constant's ordinary first-order declaration.  Arrow constants are
fully flattened, matching the translator `defaultApp` path.  When such a constant is
used as a value, the later eta phase creates a closure around this declaration. -/
def sourceDecl (ty : Ty) : FO.SymbolDecl :=
  let (arguments, result) := FO.flattenArrow ty
  { args := arguments.map FO.FOSort.ofTy
    result := FO.FOSort.ofTy result }

@[simp] theorem sourceDecl_base (sort : BaseSort) :
    sourceDecl (.base sort) = { args := [], result := .base sort } := rfl

@[simp] theorem sourceDecl_bool :
    sourceDecl .bool = { args := [], result := .bool } := rfl

@[simp] theorem sourceDecl_arrow (domain codomain : Ty) :
    sourceDecl (.arrow domain codomain) =
      { args := (domain :: (FO.flattenArrow codomain).1).map FO.FOSort.ofTy
        result := FO.FOSort.ofTy (FO.flattenArrow codomain).2 } := rfl

@[simp] theorem freeVarIndices_var (ref : Ref context ty) :
    freeVarIndices (Term.var (signature := signature) ref) = [refToNat ref] := rfl

/-- Every de Bruijn reference points inside its typing context. -/
theorem refToNat_lt_length (ref : Ref types ty) : refToNat ref < types.length := by
  induction ref with
  | here => simp [refToNat]
  | there ref inductionHypothesis =>
      simp only [refToNat, List.length_cons]
      omega

private theorem mergeIndices_lt {left right : List Nat} {bound : Nat}
    (leftBound : ∀ index ∈ left, index < bound)
    (rightBound : ∀ index ∈ right, index < bound) :
    ∀ index ∈ (left ++ right).eraseDups, index < bound := by
  intro index membership
  simp only [List.mem_eraseDups, List.mem_append] at membership
  exact membership.elim (leftBound index) (rightBound index)

private theorem leaveBinder_lt {indices : List Nat} {bound : Nat}
    (indicesBound : ∀ index ∈ indices, index < bound + 1) :
    ∀ index ∈ leaveBinder indices, index < bound := by
  intro index membership
  simp only [leaveBinder, List.mem_filterMap] at membership
  obtain ⟨bodyIndex, bodyMembership, mapped⟩ := membership
  cases bodyIndex with
  | zero => simp at mapped
  | succ bodyIndex =>
      simp only [Option.some.injEq] at mapped
      subst index
      have bodyBound := indicesBound (bodyIndex + 1) bodyMembership
      omega

/-- Free-variable collection never produces an out-of-bounds context position. -/
theorem freeVarIndices_lt :
    (term : Term signature context ty) →
      ∀ index ∈ freeVarIndices term, index < context.length := by
  intro term
  induction term with
  | var ref =>
      intro index membership
      simp only [freeVarIndices, List.mem_singleton] at membership
      subst index
      exact refToNat_lt_length ref
  | const | boolLit => simp [freeVarIndices]
  | not body inductionHypothesis => simpa [freeVarIndices] using inductionHypothesis
  | and left right leftIH rightIH =>
      simpa [freeVarIndices] using mergeIndices_lt leftIH rightIH
  | or left right leftIH rightIH =>
      simpa [freeVarIndices] using mergeIndices_lt leftIH rightIH
  | imp left right leftIH rightIH =>
      simpa [freeVarIndices] using mergeIndices_lt leftIH rightIH
  | iff left right leftIH rightIH =>
      simpa [freeVarIndices] using mergeIndices_lt leftIH rightIH
  | eq left right leftIH rightIH =>
      simpa [freeVarIndices] using mergeIndices_lt leftIH rightIH
  | app fn argument fnIH argumentIH =>
      simpa [freeVarIndices] using mergeIndices_lt fnIH argumentIH
  | lam body bodyIH =>
      intro index membership
      simp only [freeVarIndices, List.mem_eraseDups] at membership
      exact leaveBinder_lt bodyIH index membership
  | forallE body bodyIH =>
      intro index membership
      simp only [freeVarIndices, List.mem_eraseDups] at membership
      exact leaveBinder_lt bodyIH index membership
  | existsE body bodyIH =>
      intro index membership
      simp only [freeVarIndices, List.mem_eraseDups] at membership
      exact leaveBinder_lt bodyIH index membership

/-- In particular, every recorded closure capture has a type in its context. -/
theorem Closure.capture_lt (closure : Closure signature)
    (index : Nat) (membership : index ∈ closure.captures) :
    index < closure.context.length := by
  exact leaveBinder_lt (freeVarIndices_lt closure.body) index membership

@[simp] theorem PackedVar.at?_isSome_iff (context : Context) (index : Nat) :
    (PackedVar.at? context index).isSome = true ↔ index < context.length := by
  induction context generalizing index with
  | nil => simp [PackedVar.at?]
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => simp [PackedVar.at?]
      | succ index =>
          simp [PackedVar.at?, inductionHypothesis]

private theorem filterMap_length_of_isSome {α β : Type} {values : List α}
    {f : α → Option β}
    (present : ∀ value ∈ values, (f value).isSome = true) :
    (values.filterMap f).length = values.length := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      have headPresent := present value (by simp)
      have tailPresent : ∀ item ∈ values, (f item).isSome = true := by
        intro item membership
        exact present item (by simp [membership])
      cases lookup : f value with
      | none => simp [lookup] at headPresent
      | some result =>
          simp only [List.filterMap_cons, lookup, List.length_cons]
          rw [inductionHypothesis tailPresent]

/-- Exact captures are never lost when converted to typed references. -/
theorem Closure.captureRefs_length (closure : Closure signature) :
    closure.captureRefs.length = closure.captures.length := by
  apply filterMap_length_of_isSome
  intro index membership
  exact (PackedVar.at?_isSome_iff closure.context index).2
    (closure.capture_lt index membership)

end Crush.Metatheory.Defunctionalization
