/-!
# Guarded subtype encodings

Some Lean types occupy only a guarded subset of their SMT carrier.  Production's
primary example is `Nat`, represented by `Int` together with `0 ≤ x`.  Universal
binders use implication, existential binders use conjunction, and every generated
result is constrained to satisfy the guard.

`Encoding` states the exact semantic contract: the source carrier is equivalent
to the subtype of guarded target values.  The theorems below validate the three
production uses of `wfCondition`: binder guards, result guards, and guarded
function extensionality.
-/

namespace Crush.Metatheory.Guarded

universe u v

set_option linter.checkUnivs false

/-- An equivalence between a source carrier and the well-formed subset of a
larger target carrier. -/
structure Encoding where
  Source : Type u
  Target : Type v
  sourceNonempty : Nonempty Source
  encode : Source → Target
  guard : Target → Prop
  encode_guard : ∀ value, guard (encode value)
  decode : (value : Target) → guard value → Source
  decode_encode : ∀ value, decode (encode value) (encode_guard value) = value
  encode_decode : ∀ value (wellFormed : guard value),
    encode (decode value wellFormed) = value

namespace Encoding

variable (encoding : Encoding)

/-- Production's universal-binder shape: `wf x ⇒ body`. -/
def guardedForall (body : encoding.Target → Prop) : Prop :=
  ∀ value, encoding.guard value → body value

/-- Production's existential-binder shape: `wf x ∧ body`. -/
def guardedExists (body : encoding.Target → Prop) : Prop :=
  ∃ value, encoding.guard value ∧ body value

theorem encode_injective : Function.Injective encoding.encode := by
  intro left right equality
  have subtypeEquality :
      (⟨encoding.encode left, encoding.encode_guard left⟩ :
        Subtype encoding.guard) =
      ⟨encoding.encode right, encoding.encode_guard right⟩ :=
    Subtype.ext equality
  have decoded := congrArg
    (fun value : Subtype encoding.guard =>
      encoding.decode value.1 value.2) subtypeEquality
  simpa only [encoding.decode_encode] using decoded

/-- A source predicate and its target image agree on encoded values iff source
universal quantification agrees with the production guarded universal. -/
theorem forall_iff_guardedForall
    (sourceBody : encoding.Source → Prop)
    (targetBody : encoding.Target → Prop)
    (bodyRelated : ∀ value,
      sourceBody value ↔ targetBody (encoding.encode value)) :
    (∀ value, sourceBody value) ↔ encoding.guardedForall targetBody := by
  constructor
  · intro sourceForall targetValue wellFormed
    have related := bodyRelated (encoding.decode targetValue wellFormed)
    rw [encoding.encode_decode targetValue wellFormed] at related
    exact related.mp (sourceForall _)
  · intro targetForall sourceValue
    exact (bodyRelated sourceValue).mpr
      (targetForall (encoding.encode sourceValue)
        (encoding.encode_guard sourceValue))

/-- Existential quantification uses the dual conjunction guard. -/
theorem exists_iff_guardedExists
    (sourceBody : encoding.Source → Prop)
    (targetBody : encoding.Target → Prop)
    (bodyRelated : ∀ value,
      sourceBody value ↔ targetBody (encoding.encode value)) :
    (∃ value, sourceBody value) ↔ encoding.guardedExists targetBody := by
  constructor
  · rintro ⟨sourceValue, sourceProof⟩
    exact ⟨encoding.encode sourceValue, encoding.encode_guard sourceValue,
      (bodyRelated sourceValue).mp sourceProof⟩
  · rintro ⟨targetValue, wellFormed, targetProof⟩
    refine ⟨encoding.decode targetValue wellFormed, ?_⟩
    have related := bodyRelated (encoding.decode targetValue wellFormed)
    rw [encoding.encode_decode targetValue wellFormed] at related
    exact related.mpr targetProof

/-- Equality is reflected and preserved by a guarded encoding. -/
theorem encode_eq_iff (left right : encoding.Source) :
    encoding.encode left = encoding.encode right ↔ left = right := by
  constructor
  · exact fun equality => (encode_injective encoding) equality
  · exact congrArg encoding.encode

/-- Totalize decoding outside the source image.  Production axioms only expose
the behavior at guarded arguments, so the arbitrary default is unobservable. -/
noncomputable def decodeDefault (value : encoding.Target) : encoding.Source :=
  by
    classical
    exact if wellFormed : encoding.guard value then encoding.decode value wellFormed
      else Classical.choice encoding.sourceNonempty

@[simp] theorem decodeDefault_encode (value : encoding.Source) :
    encoding.decodeDefault (encoding.encode value) = value := by
  rw [decodeDefault]
  simp only [dif_pos (encoding.encode_guard value), encoding.decode_encode]

/-- Canonical total target interpretation of a source function. -/
noncomputable def liftFunction (fn : encoding.Source → encoding.Source) :
    encoding.Target → encoding.Target :=
  fun argument => encoding.encode (fn (encoding.decodeDefault argument))

/-- Canonical interpretation of an arbitrary symbol whose result uses this
guarded encoding.  This is the semantic counterpart of `emitResultWF`. -/
def liftResult {Argument : Type} (fn : Argument → encoding.Source) :
    Argument → encoding.Target :=
  fun argument => encoding.encode (fn argument)

theorem liftResult_guard {Argument : Type}
    (fn : Argument → encoding.Source) (argument : Argument) :
    encoding.guard (encoding.liftResult fn argument) :=
  encoding.encode_guard _

@[simp] theorem liftFunction_encode
    (fn : encoding.Source → encoding.Source) (argument : encoding.Source) :
    encoding.liftFunction fn (encoding.encode argument) =
      encoding.encode (fn argument) := by
  simp [liftFunction]

/-- The generated `app` result-WF axiom holds for the canonical lifted
interpretation, including at target values outside the source image. -/
theorem liftFunction_result_guard
    (fn : encoding.Source → encoding.Source) (argument : encoding.Target) :
    encoding.guard (encoding.liftFunction fn argument) := by
  exact encoding.encode_guard _

/-- Production's extensionality premise needs equality only at guarded
arguments.  Such guarded pointwise agreement reflects source function equality. -/
theorem function_eq_of_guarded_lift_eq
    (left right : encoding.Source → encoding.Source)
    (pointwise : ∀ argument, encoding.guard argument →
      encoding.liftFunction left argument =
        encoding.liftFunction right argument) :
    left = right := by
  funext argument
  apply encoding.encode_injective
  simpa using pointwise (encoding.encode argument)
    (encoding.encode_guard argument)

/-- Lift a guarded encoding through an optional datatype.  The target datatype
is freely generated over the larger field carrier, and its recursive guard
excludes precisely the constructors containing an ill-formed field.  This is the
one-field instance of production's `needsWFGuard`/datatype `wf_T` construction. -/
def option : Encoding where
  Source := Option encoding.Source
  Target := Option encoding.Target
  sourceNonempty := ⟨none⟩
  encode
    | none => none
    | some value => some (encoding.encode value)
  guard
    | none => True
    | some value => encoding.guard value
  encode_guard
    | none => trivial
    | some value => encoding.encode_guard value
  decode
    | none, _ => none
    | some value, wellFormed => some (encoding.decode value wellFormed)
  decode_encode := by
    intro value
    cases value with
    | none => rfl
    | some value => simp [encoding.decode_encode]
  encode_decode := by
    intro value wellFormed
    cases value with
    | none => rfl
    | some value =>
        exact congrArg some (encoding.encode_decode value wellFormed)

end Encoding

/-! ## The production `Nat ↪ Int` instance -/

/-- `Nat` is represented as the nonnegative subset of `Int`, exactly matching
`emitSort`, `wfCondition`, and `guardSort` in the live translator. -/
def natInt : Encoding where
  Source := Nat
  Target := Int
  sourceNonempty := inferInstance
  encode := Int.ofNat
  guard := fun value => 0 ≤ value
  encode_guard := Int.zero_le_ofNat
  decode := fun value _ => value.toNat
  decode_encode := by intro value; simp
  encode_decode := by
    intro value wellFormed
    exact Int.toNat_of_nonneg wellFormed

@[simp] theorem natInt_guard_encode (value : Nat) :
    natInt.guard (natInt.encode value) :=
  natInt.encode_guard value

theorem natInt_guard_iff (value : Int) :
    natInt.guard value ↔ 0 ≤ value := Iff.rfl

theorem nat_forall_iff_int_guarded
    (sourceBody : Nat → Prop) (targetBody : Int → Prop)
    (bodyRelated : ∀ value,
      sourceBody value ↔ targetBody (Int.ofNat value)) :
    (∀ value : Nat, sourceBody value) ↔
      ∀ value : Int, 0 ≤ value → targetBody value :=
  natInt.forall_iff_guardedForall sourceBody targetBody bodyRelated

theorem nat_exists_iff_int_guarded
    (sourceBody : Nat → Prop) (targetBody : Int → Prop)
    (bodyRelated : ∀ value,
      sourceBody value ↔ targetBody (Int.ofNat value)) :
    (∃ value : Nat, sourceBody value) ↔
      ∃ value : Int, 0 ≤ value ∧ targetBody value :=
  natInt.exists_iff_guardedExists sourceBody targetBody bodyRelated

/-- Production's result-WF assertion for a `Nat → Nat` application is valid in
the canonical guarded model. -/
theorem nat_liftFunction_result_nonnegative (fn : Nat → Nat) (argument : Int) :
    (0 : Int) ≤ (natInt.liftFunction fn argument : Int) :=
  natInt.liftFunction_result_guard fn argument

/-- The guarded extensionality axiom emitted for `Nat → Nat` reflects genuine
source function equality even though negative target integers are deliberately
excluded from its premise. -/
theorem nat_function_eq_of_nonnegative_pointwise (left right : Nat → Nat)
    (pointwise : ∀ argument : Int, 0 ≤ argument →
      natInt.liftFunction left argument = natInt.liftFunction right argument) :
    left = right :=
  natInt.function_eq_of_guarded_lift_eq left right pointwise

/-- Every well-formed target integer is the image of a `Nat`; this is the model
extension fact used when a guarded target witness must be pulled back. -/
theorem nonnegative_int_is_encoded_nat (value : Int) (wellFormed : 0 ≤ value) :
    ∃ sourceValue : Nat, Int.ofNat sourceValue = value :=
  ⟨value.toNat, Int.toNat_of_nonneg wellFormed⟩

/-- Concrete recursive datatype guard generated for `Option Nat`. -/
theorem optionNat_guard_none : natInt.option.guard none := trivial

theorem optionNat_guard_some (value : Int) :
    natInt.option.guard (some value) ↔ 0 ≤ value := Iff.rfl

theorem optionNat_guard_encode (value : Option Nat) :
    natInt.option.guard (natInt.option.encode value) :=
  natInt.option.encode_guard value

end Crush.Metatheory.Guarded
