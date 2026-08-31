/-!
# Representing a source type inside a target type

The Crush translator sometimes represents a source type with an existing SMT type plus a
predicate selecting the values that belong to the source type.  For example,
`Nat` is represented by `Int` together with `0 ≤ x`.  We call the selecting
predicate a *guard* and the complete encode/guard/decode package a guarded-subset
representation.

`SubsetRepresentation Source Target` states that `Source` is equivalent to the
subtype of `Target` values satisfying the guard. `Encoding` packages such a
representation when its source and target types are not known to the caller.
The remaining definitions validate the three translator uses of `wfCondition`:
binder guards, result guards, and guarded function extensionality.
-/

namespace Crush.Metatheory.Guarded

universe u v

set_option linter.checkUnivs false

/-- Evidence that `Source` is represented by exactly those `Target` values that
satisfy `guard`. -/
structure SubsetRepresentation (Source : Type u) (Target : Type v) where
  sourceNonempty : Nonempty Source
  encode : Source → Target
  guard : Target → Prop
  encode_guard : ∀ value, guard (encode value)
  decode : (value : Target) → guard value → Source
  decode_encode : ∀ value, decode (encode value) (encode_guard value) = value
  encode_decode : ∀ value (wellFormed : guard value),
    encode (decode value wellFormed) = value

/-- A guarded-subset representation with its source and target types packaged
existentially. This is the form stored by a translation sort hook. -/
structure Encoding where
  Source : Type u
  Target : Type v
  representation : SubsetRepresentation Source Target

namespace Encoding

theorem sourceNonempty (encoding : Encoding) : Nonempty encoding.Source :=
  encoding.representation.sourceNonempty

@[reducible] def encode (encoding : Encoding) : encoding.Source → encoding.Target :=
  encoding.representation.encode

@[reducible] def guard (encoding : Encoding) : encoding.Target → Prop :=
  encoding.representation.guard

theorem encode_guard (encoding : Encoding) (value : encoding.Source) :
    encoding.guard (encoding.encode value) :=
  encoding.representation.encode_guard value

@[reducible] def decode (encoding : Encoding) (value : encoding.Target)
    (valid : encoding.guard value) : encoding.Source :=
  encoding.representation.decode value valid

theorem decode_encode (encoding : Encoding) (value : encoding.Source) :
    encoding.decode (encoding.encode value) (encoding.encode_guard value) = value :=
  encoding.representation.decode_encode value

theorem encode_decode (encoding : Encoding) (value : encoding.Target)
    (valid : encoding.guard value) :
    encoding.encode (encoding.decode value valid) = value :=
  encoding.representation.encode_decode value valid

end Encoding

/-- The target carrier is inhabited because it contains every encoded source
value. -/
theorem SubsetRepresentation.targetNonempty {Source : Type u} {Target : Type v}
    (representation : SubsetRepresentation Source Target) : Nonempty Target :=
  let ⟨value⟩ := representation.sourceNonempty
  ⟨representation.encode value⟩

/-- Totalize an indexed relation's decoder outside its guarded image. -/
noncomputable def SubsetRepresentation.decodeDefault
    {Source : Type u} {Target : Type v}
    (representation : SubsetRepresentation Source Target) (value : Target) : Source := by
  classical
  exact if valid : representation.guard value then representation.decode value valid
    else Classical.choice representation.sourceNonempty

@[simp] theorem SubsetRepresentation.decodeDefault_encode
    {Source : Type u} {Target : Type v}
    (representation : SubsetRepresentation Source Target) (value : Source) :
    representation.decodeDefault (representation.encode value) = value := by
  rw [SubsetRepresentation.decodeDefault]
  simp only [dif_pos (representation.encode_guard value),
    representation.decode_encode]

theorem SubsetRepresentation.encode_injective
    {Source : Type u} {Target : Type v}
    (representation : SubsetRepresentation Source Target) :
    Function.Injective representation.encode := by
  intro left right equal
  have subtypeEqual :
      (⟨representation.encode left, representation.encode_guard left⟩ :
        Subtype representation.guard) =
        ⟨representation.encode right, representation.encode_guard right⟩ :=
    Subtype.ext equal
  have decoded := congrArg
    (fun value : Subtype representation.guard =>
      representation.decode value.1 value.2) subtypeEqual
  simpa only [representation.decode_encode] using decoded

/-- Equality is reflected and preserved by an indexed guarded relation. -/
theorem SubsetRepresentation.encode_eq_iff
    {Source : Type u} {Target : Type v}
    (representation : SubsetRepresentation Source Target) (left right : Source) :
    representation.encode left = representation.encode right ↔ left = right :=
  ⟨fun equal => representation.encode_injective equal,
    congrArg representation.encode⟩

/-- Source universal quantification is target quantification restricted to the
guarded image. -/
theorem SubsetRepresentation.forall_iff {Source : Type u} {Target : Type v}
    (representation : SubsetRepresentation Source Target)
    (sourceBody : Source → Prop)
    (targetBody : Target → Prop)
    (bodyRelated : ∀ value,
      sourceBody value ↔ targetBody (representation.encode value)) :
    (∀ value, sourceBody value) ↔
      ∀ value, representation.guard value → targetBody value := by
  constructor
  · intro sourceForall targetValue guarded
    have related := bodyRelated (representation.decode targetValue guarded)
    rw [representation.encode_decode targetValue guarded] at related
    exact related.mp (sourceForall _)
  · intro targetForall sourceValue
    exact (bodyRelated sourceValue).mpr
      (targetForall (representation.encode sourceValue)
        (representation.encode_guard sourceValue))

/-- Source existential quantification is target quantification restricted to
the guarded image. -/
theorem SubsetRepresentation.exists_iff {Source : Type u} {Target : Type v}
    (representation : SubsetRepresentation Source Target)
    (sourceBody : Source → Prop)
    (targetBody : Target → Prop)
    (bodyRelated : ∀ value,
      sourceBody value ↔ targetBody (representation.encode value)) :
    (∃ value, sourceBody value) ↔
      ∃ value, representation.guard value ∧ targetBody value := by
  constructor
  · rintro ⟨value, valid⟩
    exact ⟨representation.encode value, representation.encode_guard value,
      (bodyRelated value).mp valid⟩
  · rintro ⟨value, guarded, valid⟩
    refine ⟨representation.decode value guarded, ?_⟩
    have related := bodyRelated (representation.decode value guarded)
    rw [representation.encode_decode value guarded] at related
    exact related.mpr valid

/-- Identity relation used by carriers that need no enlargement. -/
def SubsetRepresentation.refl (Value : Type u) [Nonempty Value] :
    SubsetRepresentation Value Value where
  sourceNonempty := inferInstance
  encode := id
  guard := fun _ => True
  encode_guard := by simp
  decode := fun value _ => value
  decode_encode := by simp
  encode_decode := by simp

namespace Encoding

variable (encoding : Encoding)

/-- The Crush translator's universal-binder shape: `wf x ⇒ body`. -/
def guardedForall (body : encoding.Target → Prop) : Prop :=
  ∀ value, encoding.guard value → body value

/-- The Crush translator's existential-binder shape: `wf x ∧ body`. -/
def guardedExists (body : encoding.Target → Prop) : Prop :=
  ∃ value, encoding.guard value ∧ body value

theorem encode_injective : Function.Injective encoding.encode := by
  exact encoding.representation.encode_injective

/-- A source predicate and its target image agree on encoded values iff source
universal quantification agrees with the emitted guarded universal. -/
theorem forall_iff_guardedForall
    (sourceBody : encoding.Source → Prop)
    (targetBody : encoding.Target → Prop)
    (bodyRelated : ∀ value,
      sourceBody value ↔ targetBody (encoding.encode value)) :
    (∀ value, sourceBody value) ↔ encoding.guardedForall targetBody :=
  encoding.representation.forall_iff sourceBody targetBody bodyRelated

/-- Existential quantification uses the dual conjunction guard. -/
theorem exists_iff_guardedExists
    (sourceBody : encoding.Source → Prop)
    (targetBody : encoding.Target → Prop)
    (bodyRelated : ∀ value,
      sourceBody value ↔ targetBody (encoding.encode value)) :
    (∃ value, sourceBody value) ↔ encoding.guardedExists targetBody :=
  encoding.representation.exists_iff sourceBody targetBody bodyRelated

/-- Equality is reflected and preserved by a guarded encoding. -/
theorem encode_eq_iff (left right : encoding.Source) :
    encoding.encode left = encoding.encode right ↔ left = right :=
  encoding.representation.encode_eq_iff left right

/-- Totalize decoding outside the source image.  Emitted axioms only expose
the behavior at guarded arguments, so the arbitrary default is unobservable. -/
noncomputable def decodeDefault (value : encoding.Target) : encoding.Source :=
  encoding.representation.decodeDefault value

@[simp] theorem decodeDefault_encode (value : encoding.Source) :
    encoding.decodeDefault (encoding.encode value) = value :=
  encoding.representation.decodeDefault_encode value

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

/-- The Crush translator's extensionality premise needs equality only at guarded
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

end Encoding

/-! ## The translator's `Nat ↪ Int` instance -/

/-- `Nat` is represented as the nonnegative subset of `Int`, exactly matching
`emitSort`, `wfCondition`, and `guardSort` in the Crush translator. -/
def natInt : Encoding where
  Source := Nat
  Target := Int
  representation := {
    sourceNonempty := inferInstance
    encode := Int.ofNat
    guard := fun value => 0 ≤ value
    encode_guard := Int.zero_le_ofNat
    decode := fun value _ => value.toNat
    decode_encode := by intro value; simp
    encode_decode := by
      intro value wellFormed
      exact Int.toNat_of_nonneg wellFormed }

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

/-- The Crush translator's result-WF assertion for a `Nat → Nat` application is valid in
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

end Crush.Metatheory.Guarded
