import Crush.Metatheory.Defunctionalization.Collect

/-!
# Stable closure-ID annotation

Closure constructors occupy the final segment of `Plan.targetSignature`.  This
module assigns each lambda occurrence the zero-based position of its constructor
in that segment.  Annotation uses exactly the preorder of `closures`: a lambda is
recorded before lambdas nested in its body, and binary terms visit left before
right.

The syntax remains intrinsically typed; annotation can neither change a type nor
introduce malformed application.  IDs are natural numbers here, accompanied by
proved bounds below.  The target translator will turn those bounds into typed FO
symbol references.
-/

namespace Crush.Metatheory.Defunctionalization

variable {signature : Signature} {context : Context} {ty domain codomain : Ty}

/-- Source syntax with a stable constructor ID attached to every lambda. -/
inductive AnnotatedTerm (signature : Signature) : Context → Ty → Type where
  | var {context : Context} {ty : Ty} :
      Var context ty → AnnotatedTerm signature context ty
  | const {context : Context} {ty : Ty} :
      Const signature ty → AnnotatedTerm signature context ty
  | boolLit {context : Context} : Bool → AnnotatedTerm signature context .bool
  | not {context : Context} :
      AnnotatedTerm signature context .bool → AnnotatedTerm signature context .bool
  | and {context : Context} :
      AnnotatedTerm signature context .bool → AnnotatedTerm signature context .bool →
      AnnotatedTerm signature context .bool
  | or {context : Context} :
      AnnotatedTerm signature context .bool → AnnotatedTerm signature context .bool →
      AnnotatedTerm signature context .bool
  | imp {context : Context} :
      AnnotatedTerm signature context .bool → AnnotatedTerm signature context .bool →
      AnnotatedTerm signature context .bool
  | iff {context : Context} :
      AnnotatedTerm signature context .bool → AnnotatedTerm signature context .bool →
      AnnotatedTerm signature context .bool
  | eq {context : Context} {ty : Ty} :
      AnnotatedTerm signature context ty → AnnotatedTerm signature context ty →
      AnnotatedTerm signature context .bool
  | lam {context : Context} {domain codomain : Ty} :
      (closureId : Nat) → AnnotatedTerm signature (domain :: context) codomain →
      AnnotatedTerm signature context (.arrow domain codomain)
  | app {context : Context} {domain codomain : Ty} :
      AnnotatedTerm signature context (.arrow domain codomain) →
      AnnotatedTerm signature context domain → AnnotatedTerm signature context codomain
  | forallE {context : Context} {domain : Ty} :
      AnnotatedTerm signature (domain :: context) .bool →
      AnnotatedTerm signature context .bool
  | existsE {context : Context} {domain : Ty} :
      AnnotatedTerm signature (domain :: context) .bool →
      AnnotatedTerm signature context .bool

/-- Result of annotation from a supplied initial constructor ID. -/
structure Annotation (signature : Signature) (context : Context) (ty : Ty) where
  term : AnnotatedTerm signature context ty
  nextId : Nat

/-- Total preorder annotation.  The returned counter is the first unused ID. -/
def annotateFrom {signature : Signature} {context : Context} {ty : Ty} (start : Nat) :
    (term : Term signature context ty) → Annotation signature context ty
  | .var ref => ⟨.var ref, start⟩
  | .const ref => ⟨.const ref, start⟩
  | .boolLit value => ⟨.boolLit value, start⟩
  | .not body =>
      let annotated := annotateFrom start body
      ⟨.not annotated.term, annotated.nextId⟩
  | .and left right =>
      let leftResult := annotateFrom start left
      let rightResult := annotateFrom leftResult.nextId right
      ⟨.and leftResult.term rightResult.term, rightResult.nextId⟩
  | .or left right =>
      let leftResult := annotateFrom start left
      let rightResult := annotateFrom leftResult.nextId right
      ⟨.or leftResult.term rightResult.term, rightResult.nextId⟩
  | .imp left right =>
      let leftResult := annotateFrom start left
      let rightResult := annotateFrom leftResult.nextId right
      ⟨.imp leftResult.term rightResult.term, rightResult.nextId⟩
  | .iff left right =>
      let leftResult := annotateFrom start left
      let rightResult := annotateFrom leftResult.nextId right
      ⟨.iff leftResult.term rightResult.term, rightResult.nextId⟩
  | .eq left right =>
      let leftResult := annotateFrom start left
      let rightResult := annotateFrom leftResult.nextId right
      ⟨.eq leftResult.term rightResult.term, rightResult.nextId⟩
  | .lam body =>
      let bodyResult := annotateFrom (start + 1) body
      ⟨.lam start bodyResult.term, bodyResult.nextId⟩
  | .app fn argument =>
      let fnResult := annotateFrom start fn
      let argumentResult := annotateFrom fnResult.nextId argument
      ⟨.app fnResult.term argumentResult.term, argumentResult.nextId⟩
  | .forallE body =>
      let annotated := annotateFrom start body
      ⟨.forallE annotated.term, annotated.nextId⟩
  | .existsE body =>
      let annotated := annotateFrom start body
      ⟨.existsE annotated.term, annotated.nextId⟩

/-- Annotate a term from constructor ID zero. -/
def annotate (term : Term signature context ty) : AnnotatedTerm signature context ty :=
  (annotateFrom 0 term).term

/-- Closure IDs in syntax traversal order. -/
def AnnotatedTerm.closureIds {signature : Signature} {context : Context} {ty : Ty}
    (term : AnnotatedTerm signature context ty) : List Nat :=
  match term with
  | .var _ | .const _ | .boolLit _ => []
  | .not body => body.closureIds
  | .and left right | .or left right | .imp left right | .iff left right |
      .eq left right => left.closureIds ++ right.closureIds
  | .lam closureId body => closureId :: body.closureIds
  | .app fn argument => fn.closureIds ++ argument.closureIds
  | .forallE body | .existsE body => body.closureIds

/-- Erase IDs to recover the original intrinsically typed source term. -/
def AnnotatedTerm.erase {signature : Signature} {context : Context} {ty : Ty}
    (term : AnnotatedTerm signature context ty) : Term signature context ty :=
  match term with
  | .var ref => .var ref
  | .const ref => .const ref
  | .boolLit value => .boolLit value
  | .not body => .not body.erase
  | .and left right => .and left.erase right.erase
  | .or left right => .or left.erase right.erase
  | .imp left right => .imp left.erase right.erase
  | .iff left right => .iff left.erase right.erase
  | .eq left right => .eq left.erase right.erase
  | .lam _ body => .lam body.erase
  | .app fn argument => .app fn.erase argument.erase
  | .forallE body => .forallE body.erase
  | .existsE body => .existsE body.erase

/-- Closure IDs paired with the typed descriptors from which their constructor
declarations and defining axioms will be generated. -/
def AnnotatedTerm.closureEntries {signature : Signature} {context : Context} {ty : Ty}
    (term : AnnotatedTerm signature context ty) : List (Nat × Closure signature) :=
  match term with
  | .var _ | .const _ | .boolLit _ => []
  | .not body => body.closureEntries
  | .and left right | .or left right | .imp left right | .iff left right |
      .eq left right => left.closureEntries ++ right.closureEntries
  | .lam closureId body =>
      (closureId, Closure.ofBody body.erase) :: body.closureEntries
  | .app fn argument => fn.closureEntries ++ argument.closureEntries
  | .forallE body | .existsE body => body.closureEntries

@[simp] theorem closureEntries_ids (term : AnnotatedTerm signature context ty) :
    term.closureEntries.map Prod.fst = term.closureIds := by
  induction term <;>
    simp [AnnotatedTerm.closureEntries, AnnotatedTerm.closureIds, *]

@[simp] theorem closureEntries_descriptors (term : AnnotatedTerm signature context ty) :
    term.closureEntries.map Prod.snd = closures term.erase := by
  induction term <;>
    simp [AnnotatedTerm.closureEntries, AnnotatedTerm.erase, closures, *]

/-- Annotation consumes exactly one ID per collected closure. -/
theorem annotateFrom_nextId (start : Nat) (term : Term signature context ty) :
    (annotateFrom start term).nextId = start + (closures term).length := by
  induction term generalizing start <;>
    simp [annotateFrom, closures, *] <;> omega

/-- Annotation is type- and syntax-preserving after ID erasure. -/
theorem annotateFrom_erase (start : Nat) (term : Term signature context ty) :
    (annotateFrom start term).term.erase = term := by
  induction term generalizing start <;>
    simp [annotateFrom, AnnotatedTerm.erase, *]

@[simp] theorem annotate_erase (term : Term signature context ty) :
    (annotate term).erase = term := annotateFrom_erase 0 term

/-- Annotation assigns the consecutive interval beginning at `start`, in exactly
the same order as the collected closure list. -/
theorem annotateFrom_closureIds (start : Nat) (term : Term signature context ty) :
    (annotateFrom start term).term.closureIds =
      List.range' start (closures term).length := by
  induction term generalizing start <;>
    simp [annotateFrom, closures, AnnotatedTerm.closureIds, *,
      annotateFrom_nextId, List.range'_succ]

@[simp] theorem annotate_closureIds (term : Term signature context ty) :
    (annotate term).closureIds = List.range (closures term).length := by
  simpa [annotate, List.range_eq_range'] using annotateFrom_closureIds 0 term

/-- Every generated closure ID selects an existing collected constructor. -/
theorem closureId_lt (term : Term signature context ty) (closureId : Nat)
    (membership : closureId ∈ (annotate term).closureIds) :
    closureId < (closures term).length := by
  rw [annotate_closureIds] at membership
  exact List.mem_range.mp membership

/-- The annotated entries are an indexed presentation of precisely the collected
closure list, not a second independently computed set. -/
theorem annotate_entries (term : Term signature context ty) :
    (annotate term).closureEntries.map Prod.snd = closures term := by
  simp

end Crush.Metatheory.Defunctionalization
