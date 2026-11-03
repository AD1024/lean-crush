import Test.SoundnessRegression.Dependencies

/-!
Encoding decisions must retain their Nonempty and LawfulBEq evidence so axiom,
admission, and unsafe dependencies remain visible to Lean. Recursive auxiliary
declarations cannot witness inhabitation, and evidence introduced under translation
binders cannot escape into the final proof.
-/

open Lean Meta Crush

namespace SoundnessEncodingEvidence

set_option linter.unusedVariables false
set_option crush.trust "trust"

-- Reject recursive self-references and local helpers as witnesses.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
def recursiveEmpty : Empty := by
  exfalso
  have h : ∀ x : Empty, x ≠ x := fun x => x.elim
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem recursiveNonempty : Nonempty Empty := by
  exfalso
  have h : ∀ x : Empty, x ≠ x := fun x => x.elim
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
def outer : Nat := 0
where
  helper : Empty := by
    exfalso
    have h : ∀ x : Empty, x ≠ x := fun x => x.elim
    crush

inductive AxiomEmpty : Type
axiom emptyInstance : Nonempty AxiomEmpty
attribute [instance] emptyInstance

theorem retainsNonemptyAxiom : False := by
  have h : ∀ x : AxiomEmpty, x ≠ x := fun x => nomatch x
  crush

inductive AdmittedEmpty : Type
-- Reuse an existing admission to test its transitive evidence dependency.
instance : Nonempty AdmittedEmpty := False.elim
  ((by decide : (0 : Int) ≠ 1) SoundnessDependencies.sorryEquality)

theorem retainsNonemptyAdmission : False := by
  have h : ∀ x : AdmittedEmpty, x ≠ x := fun x => nomatch x
  crush

inductive UnsafeEmpty : Type
unsafe def unsafeWitness : UnsafeEmpty := unsafeCast ()
set_option linter.defProp false in
set_option warn.classDefReducibility false in
@[instance, instance_reducible] unsafe def unsafeInstance : Nonempty UnsafeEmpty := ⟨unsafeWitness⟩

/-- error: (kernel) invalid declaration, it uses unsafe declaration -/
#guard_msgs(error, substring := true) in
theorem rejectsUnsafeEvidence : False := by
  have h : ∀ x : UnsafeEmpty, x ≠ x := fun x => nomatch x
  crush

structure Token where
  value : Int
instance : BEq Token := ⟨fun _ _ => false⟩
axiom lawfulToken : LawfulBEq Token
attribute [instance] lawfulToken

theorem retainsLawfulness : False := by
  have h : ∀ t : Token, (t == t) = false := fun _ => rfl
  have e : ∃ t : Token, t = t := ⟨⟨0⟩, rfl⟩
  crush

-- Retain evidence supplied by original local assumptions.
theorem localValue (α : Type) (x : α) (h : ∀ a : α, a ≠ a) : False := by crush
theorem localNonempty (α : Type) (hne : Nonempty α)
    (h : ∀ a : α, a ≠ a) : False := by crush

run_meta do
  for (name, dependency) in #[(``retainsNonemptyAxiom, ``emptyInstance),
      (``retainsNonemptyAdmission, ``sorryAx), (``retainsLawfulness, ``lawfulToken)] do
    let axioms ← collectAxioms name
    unless axioms.contains ``Crush.crushSorry && axioms.contains dependency do
      throwError "trusted proof {name} lost encoding evidence {dependency}: {axioms}"

-- Reject evidence introduced only inside translation.
run_meta do
  let (_, state) ← TranslateM.run {} do
    withLocalDeclD `hyp (mkConst ``True) fun hyp => do
      if ← TranslateM.recordEncodingEvidence (mkConst ``True) hyp then
        throwError "translation-local evidence was accepted unconditionally"
  unless state.encodingEvidence.isEmpty do
    throwError "translation-local evidence escaped into the query state"

end SoundnessEncodingEvidence
