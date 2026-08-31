import Crush.Metatheory.Datatype.Semantics
import Crush.Metatheory.Guarded.Encoding

/-!
# Guarded datatype carriers

Lift guarded representations of external base fields through any productive
reified datatype block. The target remains the same finite free algebra over
larger field carriers; a recursive structural guard selects exactly the values
that come from the source datatype.
-/

namespace Crush.Metatheory.Guarded

universe u v

/-- Guarded representations for every external base sort. -/
abbrev BaseRepresentations (Source : BaseSort → Type u) (Target : BaseSort → Type v) :=
  ∀ sort, SubsetRepresentation (Source sort) (Target sort)

end Crush.Metatheory.Guarded

namespace Crush.Metatheory.Datatype

open Crush.Metatheory.Guarded

universe u v

mutual
  /-- A target datatype value is well formed when every external payload is
  guarded and every recursive payload is structurally well formed. -/
  def Val.WF {arity : Nat} {block : Block arity}
      {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop) :
      {data : DataRef block} → Val block Target data → Prop
    | _, .ctor _ args => args.WF base

  /-- Structural well-formedness of one constructor telescope. -/
  def Args.WF {arity : Nat} {block : Block arity}
      {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop) :
      {fields : List (FieldDecl arity)} → Args block Target fields → Prop
    | _, .nil => True
    | _, .base value rest => base _ value ∧ rest.WF base
    | _, .data value rest => value.WF base ∧ rest.WF base
end

/-- Guard associated with one field carrier. -/
def FieldDecl.WF {arity : Nat} {block : Block arity}
    {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop)
    (field : FieldDecl arity) (value : field.Denote block Target) : Prop :=
  match field with
  | ⟨_, .base sort⟩ => base sort value
  | ⟨_, .data _⟩ => value.WF base

/-- A well-formed constructor telescope gives a guarded value at every typed
field position. -/
theorem Args.get_wf {arity : Nat} {block : Block arity}
    {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop)
    {fields : List (FieldDecl arity)} (args : Args block Target fields)
    {field : FieldDecl arity} (ref : Ref fields field)
    (wellFormed : args.WF base) : field.WF base (args.get ref) := by
  induction ref with
  | here =>
      cases args with
      | base value rest | data value rest => exact wellFormed.1
  | there ref ih =>
      cases args with
      | base value rest | data value rest => exact ih rest wellFormed.2

/-- A telescope is well formed exactly when every typed field lookup is
well formed. -/
theorem Args.wf_iff_get {arity : Nat} {block : Block arity}
    {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop)
    {fields : List (FieldDecl arity)} (args : Args block Target fields) :
    args.WF base ↔ ∀ field (ref : Ref fields field),
      field.WF base (args.get ref) := by
  constructor
  · intro wellFormed field ref
    exact args.get_wf base ref wellFormed
  · intro every
    cases args with
    | nil => exact trivial
    | base value rest =>
        exact ⟨every _ .here,
          (rest.wf_iff_get base).2 fun field ref => every field (.there ref)⟩
    | data value rest =>
        exact ⟨every _ .here,
          (rest.wf_iff_get base).2 fun field ref => every field (.there ref)⟩

@[simp] theorem Val.ctor_wf {arity : Nat} {block : Block arity}
    {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ref : CtorRef block data ctor) (args : Args block Target ctor.fields) :
    (mk ref args).WF base ↔ args.WF base := Iff.rfl

/-- A matching selector recovers a guarded field from a well-formed constructor.
No condition is needed for its arbitrary nonmatching fallback. -/
theorem sel_wf {arity : Nat} {block : Block arity}
    {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop)
    {data : DataRef block} {ctor : CtorDecl arity}
    (ctorRef : CtorRef block data ctor) {field : FieldDecl arity}
    (fieldRef : FieldRef ctor field) (fallback : field.Denote block Target)
    (args : Args block Target ctor.fields) (wellFormed : args.WF base) :
    field.WF base (sel ctorRef fieldRef fallback (mk ctorRef args)) := by
  rw [sel_ctor]
  exact args.get_wf base fieldRef wellFormed

/-- Canonical fallback for a total selector. It is semantically irrelevant on
the matching constructor selected by the emitted guard. -/
noncomputable def FieldDecl.fallback {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type u} {Target : BaseSort → Type v}
    (base : BaseRepresentations Source Target) (productive : Productive block)
    (field : FieldDecl arity) : field.Denote block Target := by
  classical
  cases field with
  | mk name sort =>
      cases sort with
      | base sort => exact Classical.choice (base sort).targetNonempty
      | data child =>
          exact Classical.choice (val_nonempty productive
            (fun sort => (base sort).targetNonempty) child)

/-- Emitted datatype guard: whenever a constructor tester accepts,
every selector belonging to that constructor returns a guarded field. -/
def Val.SelWF {arity : Nat} {block : Block arity}
    {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop)
    {data : DataRef block} (value : Val block Target data) : Prop :=
  ∀ (ctor : CtorDecl arity) (ctorRef : CtorRef block data ctor)
      (field : FieldDecl arity) (fieldRef : FieldRef ctor field)
      (fallback : field.Denote block Target),
    IsCtor ctorRef value →
      field.WF base (sel ctorRef fieldRef fallback value)

/-- Structural well-formedness validates the selector-form guard. -/
theorem Val.selWF_of_wf {arity : Nat} {block : Block arity}
    {Target : BaseSort → Type v} (base : ∀ sort, Target sort → Prop)
    {data : DataRef block} {value : Val block Target data}
    (wellFormed : value.WF base) : value.SelWF base := by
  intro ctor ctorRef field fieldRef fallback isCtor
  rcases isCtor with ⟨args, equal⟩
  have argsWF : args.WF base := by
    apply (Val.ctor_wf base ctorRef args).1
    exact equal ▸ wellFormed
  rw [← equal, sel_ctor]
  exact args.get_wf base fieldRef argsWF

/-- Tester/selector guards recover the structural recursive predicate. -/
theorem Val.wf_of_selWF {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type u} {Target : BaseSort → Type v}
    (base : BaseRepresentations Source Target) (productive : Productive block)
    {data : DataRef block} {value : Val block Target data}
    (guarded : value.SelWF (fun sort => (base sort).guard)) :
    value.WF (fun sort => (base sort).guard) := by
  cases value with
  | ctor ctorRef args =>
      apply (Val.ctor_wf _ ctorRef args).2
      apply (args.wf_iff_get _).2
      intro field fieldRef
      let fallback := field.fallback base productive
      simpa [fallback] using guarded _ ctorRef _ fieldRef fallback
        (test_ctor ctorRef args)

/-- The recursive structural guard and the Crush translator's tester/selector form are
equivalent for every productive block. -/
theorem Val.wf_iff_selWF {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type u} {Target : BaseSort → Type v}
    (base : BaseRepresentations Source Target) (productive : Productive block)
    {data : DataRef block} (value : Val block Target data) :
    value.WF (fun sort => (base sort).guard) ↔
      value.SelWF (fun sort => (base sort).guard) :=
  ⟨Val.selWF_of_wf _, Val.wf_of_selWF base productive⟩

mutual
  /-- Encode a source datatype without changing its constructor tree. -/
  def Val.encode {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) :
      {data : DataRef block} → Val block Source data → Val block Target data
    | _, .ctor ctor args => .ctor ctor (args.encode base)

  /-- Encode every external field in a constructor telescope. -/
  def Args.encode {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) :
      {fields : List (FieldDecl arity)} →
        Args block Source fields → Args block Target fields
    | _, .nil => .nil
    | _, .base value rest => .base ((base _).encode value) (rest.encode base)
    | _, .data value rest => .data (value.encode base) (rest.encode base)
end

/-- Pointwise field encoding preserves and reflects the constructor selected by
a tester. -/
theorem Val.isCtor_encode_iff {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type u} {Target : BaseSort → Type v}
    (base : BaseRepresentations Source Target) {data : DataRef block}
    {ctor : CtorDecl arity} (ref : CtorRef block data ctor)
    (value : Val block Source data) :
    IsCtor ref (value.encode base) ↔ IsCtor ref value := by
  cases value with
  | @ctor actualData actualCtor actualRef args =>
      by_cases same : ref.index = actualRef.index
      · have ctorEq : ctor = actualCtor := by
          have selected := Ref.getElem?_index ref
          rw [same, Ref.getElem?_index actualRef] at selected
          exact (Option.some.inj selected).symm
        subst actualCtor
        have refs : ref = actualRef :=
          eq_of_heq (Ref.heq_of_index_eq ref actualRef same)
        subst actualRef
        exact ⟨fun _ => test_ctor ref args,
          fun _ => test_ctor ref (args.encode base)⟩
      · constructor
        · intro selected
          exact False.elim (test_ne ref actualRef same _ selected)
        · intro selected
          exact False.elim (test_ne ref actualRef same _ selected)

mutual
  /-- Encoding always produces a structurally guarded datatype value. -/
  theorem Val.encode_wf {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) {data : DataRef block}
      (value : Val block Source data) :
      (value.encode base).WF (fun sort => (base sort).guard) := by
    cases value with
    | ctor ctor args => exact args.encode_wf base

  /-- Encoded constructor arguments satisfy the recursive guard. -/
  theorem Args.encode_wf {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) {fields : List (FieldDecl arity)}
      (args : Args block Source fields) :
      (args.encode base).WF (fun sort => (base sort).guard) := by
    cases args with
    | nil => exact trivial
    | base value rest => exact ⟨(base _).encode_guard value, rest.encode_wf base⟩
    | data value rest => exact ⟨value.encode_wf base, rest.encode_wf base⟩
end

mutual
  /-- Decode one well-formed target datatype value. -/
  def Val.decode {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) :
      {data : DataRef block} → (value : Val block Target data) →
      value.WF (fun sort => (base sort).guard) → Val block Source data
    | _, .ctor ctor args, wellFormed =>
        .ctor ctor (args.decode base wellFormed)

  /-- Decode one structurally well-formed constructor telescope. -/
  def Args.decode {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) :
      {fields : List (FieldDecl arity)} → (args : Args block Target fields) →
      args.WF (fun sort => (base sort).guard) → Args block Source fields
    | _, .nil, _ => .nil
    | _, .base value rest, wellFormed =>
        .base ((base _).decode value wellFormed.1)
          (rest.decode base wellFormed.2)
    | _, .data value rest, wellFormed =>
        .data (value.decode base wellFormed.1)
          (rest.decode base wellFormed.2)
end

/-- Decode one guarded field, using the external carrier relation at base
fields and structural datatype decoding at recursive fields. -/
def FieldDecl.decode {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type u} {Target : BaseSort → Type v}
    (base : BaseRepresentations Source Target) (field : FieldDecl arity)
    (value : field.Denote block Target)
    (wellFormed : field.WF (fun sort => (base sort).guard) value) :
    field.Denote block Source :=
  match field with
  | ⟨_, .base sort⟩ => (base sort).decode value wellFormed
  | ⟨_, .data _⟩ => value.decode base wellFormed

/-- Decoding a constructor telescope commutes with typed field lookup. -/
theorem Args.get_decode {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type u} {Target : BaseSort → Type v}
    (base : BaseRepresentations Source Target)
    {fields : List (FieldDecl arity)} (args : Args block Target fields)
    {field : FieldDecl arity} (ref : Ref fields field)
    (wellFormed : args.WF (fun sort => (base sort).guard)) :
    (args.decode base wellFormed).get ref =
      field.decode base (args.get ref) (args.get_wf _ ref wellFormed) := by
  induction ref with
  | here => cases args <;> rfl
  | there ref ih =>
      cases args with
      | base value rest | data value rest => exact ih rest wellFormed.2

mutual
  /-- Decoding an encoded datatype value is the identity. -/
  theorem Val.decode_encode {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) {data : DataRef block}
      (value : Val block Source data) :
      (value.encode base).decode base (value.encode_wf base) = value := by
    cases value with
    | ctor ctor args => simp [Val.encode, Val.decode, args.decode_encode base]

  /-- Decoding encoded constructor arguments is the identity. -/
  theorem Args.decode_encode {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) {fields : List (FieldDecl arity)}
      (args : Args block Source fields) :
      (args.encode base).decode base (args.encode_wf base) = args := by
    cases args with
    | nil => rfl
    | base value rest =>
        simp [Args.encode, Args.decode, SubsetRepresentation.decode_encode,
          rest.decode_encode base]
    | data value rest =>
        simp [Args.encode, Args.decode, value.decode_encode base,
          rest.decode_encode base]
end

mutual
  /-- Every guarded target datatype value is recovered exactly after decoding. -/
  theorem Val.encode_decode {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) {data : DataRef block}
      (value : Val block Target data)
      (wellFormed : value.WF (fun sort => (base sort).guard)) :
      (value.decode base wellFormed).encode base = value := by
    cases value with
    | ctor ctor args =>
        simp [Val.decode, Val.encode, args.encode_decode base wellFormed]

  /-- Every guarded target telescope is recovered exactly after decoding. -/
  theorem Args.encode_decode {arity : Nat} {block : Block arity}
      {Source : BaseSort → Type u} {Target : BaseSort → Type v}
      (base : BaseRepresentations Source Target) {fields : List (FieldDecl arity)}
      (args : Args block Target fields)
      (wellFormed : args.WF (fun sort => (base sort).guard)) :
      (args.decode base wellFormed).encode base = args := by
    cases args with
    | nil => rfl
    | base value rest =>
        simp [Args.decode, Args.encode, SubsetRepresentation.encode_decode,
          rest.encode_decode base wellFormed.2]
    | data value rest =>
        simp [Args.decode, Args.encode,
          value.encode_decode base wellFormed.1,
          rest.encode_decode base wellFormed.2]
end

/-- Any productive free datatype lifts a pointwise guarded base representation.
This is the generic semantic counterpart of the Crush translator's recursive `wf_T`
predicate, including mutually recursive blocks. -/
def lift {arity : Nat} {block : Block arity}
    {Source : BaseSort → Type u} {Target : BaseSort → Type v}
    (base : BaseRepresentations Source Target) (productive : Productive block)
    (data : DataRef block) : SubsetRepresentation (Val block Source data) (Val block Target data) where
  sourceNonempty := val_nonempty productive (fun sort => (base sort).sourceNonempty) data
  encode := Val.encode base
  guard := Val.WF (fun sort => (base sort).guard)
  encode_guard := Val.encode_wf base
  decode := Val.decode base
  decode_encode := Val.decode_encode base
  encode_decode := Val.encode_decode base

end Crush.Metatheory.Datatype
