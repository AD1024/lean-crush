import Crush

/-!
Regression tests migrated from another Lean SMT bridge's test corpus, together
with cases derived from bugs reported against it.

Two reasons this file is worth keeping separate from the hand-written tests:

* It is an *independent* corpus. The hand-written tests exercise the paths their
  author was thinking about; these were written by someone else, against a
  different implementation, and so probe places we would not have thought to look.
  Running them found four real gaps (see below).
* Several entries correspond to *reported bugs* in that implementation. Each one is
  a hazard inherent to the Lean→SMT boundary rather than to any particular
  codebase, so they are exactly the cases most worth pinning here.

Gaps this corpus found in `crush`, all now fixed:

1. Named `BitVec.*` functions (`BitVec.not`, `.add`, `.and`, …) were unrecognized —
   only the notation (`~~~`, `+`, `&&&`) was. Lean exposes both, as *different*
   `Expr`s, so the named form silently became an uninterpreted symbol, losing
   every fact about it.
2. Rotations, `BitVec.shiftLeft`/`.ushiftRight`, and the `toInt`/`ofInt` bridges
   were missing entirely.
3. `BitVec.ofNat` with a *symbolic* argument fell through to an uninterpreted
   symbol; only literals worked. It needs `int2bv`.
4. `max`/`min`, `Nat.succ`, `decide`, and the `Nat → Int` coercion (`Nat.cast`)
   were unrecognized.

All four were incompleteness rather than unsoundness — an unrecognized symbol is
uninterpreted, which loses facts but never invents them.
-/

open Crush

set_option crush.trust "trust"
set_option crush.timeout 15

/-! ## Bit-vectors -/

theorem bv_lit_add : (2 : BitVec 7) + (3 : BitVec 7) = (5 : BitVec 7) := by crush
theorem bv_comm' (a b : BitVec 10) : a + b = b + a := by crush
theorem bv_width_one (a b c : BitVec 1) : a = b ∨ b = c ∨ c = a := by crush

-- A `BitVec` of *symbolic* width has no SMT sort, so it degrades to an opaque
-- sort. Reflexivity still holds there, which is the point: degrade, don't crash.
theorem bv_symbolic_width {k : Nat} (a : BitVec k) : a = a := by crush

/-! ### Named function forms

Lean exposes both `x + y` (via the `HAdd` instance) and `BitVec.add x y`, and they
elaborate to different `Expr`s. Recognizing only the notation left the named form
uninterpreted. -/

theorem bv_named_not (x : BitVec 4) : BitVec.not x = ~~~x := by crush
theorem bv_named_and (x y : BitVec 4) : BitVec.and x y = x &&& y := by crush
theorem bv_named_or (x y : BitVec 4) : BitVec.or x y = x ||| y := by crush
theorem bv_named_xor (x y : BitVec 4) : BitVec.xor x y = x ^^^ y := by crush
theorem bv_named_add (x y : BitVec 4) : BitVec.add x y = x + y := by crush
theorem bv_named_sub (x y : BitVec 4) : BitVec.sub x y = x - y := by crush
theorem bv_named_mul (x y : BitVec 4) : BitVec.mul x y = x * y := by crush
theorem bv_named_neg (x : BitVec 4) : BitVec.neg x = -x := by crush
theorem bv_named_shl (x : BitVec 8) : BitVec.shiftLeft x 1 = x <<< (1 : Nat) := by crush
theorem bv_named_shr (x : BitVec 8) : BitVec.ushiftRight x 1 = x >>> (1 : Nat) := by crush

-- The reported `BitVec.not` bug: an arity mismatch made this fail outright there.
theorem bv_not_complement (x : BitVec 4) : x + (BitVec.not x) = 0xF#4 := by crush

/-! ### Rotations

SMT-LIB takes the rotation amount as an identifier *index*, not an operand, so only
literal amounts translate. Both sides reduce the amount modulo the width — verified
on seven cases including amounts far exceeding the width. -/

theorem bv_rotl : (2 : BitVec 7).rotateLeft 3 = (16 : BitVec 7) := by crush
theorem bv_rotr : (2 : BitVec 7).rotateRight 3 = (0x20 : BitVec 7) := by crush
theorem bv_rot_dual (x : BitVec 15) : x.rotateLeft 3 = x.rotateRight 12 := by crush
-- The amount is a closed arithmetic expression, not a bare literal.
theorem bv_rot_arith (x : BitVec 8) : x.rotateLeft (7 - 2 * 2) = x.rotateLeft (1 + 2) := by
  crush
-- 104 = 13 * 8, a whole number of turns at width 8.
theorem bv_rot_full (x : BitVec 8) : x.rotateLeft 104 = x := by crush

/-! ### Shifts, width changes, comparisons -/

theorem bv_shr_lit : 434#8 >>> 4 = 0x0b#8 := by crush
theorem bv_ashr_lit : (434#8).sshiftRight 4 = 0xfb#8 := by crush
theorem bv_shl_bv : 101#32 <<< 2#32 = 404#32 := by crush
theorem bv_setwidth_down : BitVec.setWidth 3 5#10 = 5#3 := by crush
theorem bv_sext_up : BitVec.signExtend 20 645#10 = 1048197#20 := by crush

-- Lean's `<`/`≤` on `BitVec` are the UNSIGNED comparisons. A reported bug had them
-- emitted as uninterpreted functions, which produced a spurious counterexample on
-- `bv_ult_inequality` below.
theorem bv_lt_is_ult (a b : BitVec 6) : (a < b) = (a.ult b) := by crush
theorem bv_le_is_ule (a b : BitVec 6) : (a ≤ b) = (a.ule b) := by crush
theorem bv_lit_lt : (2#6) < (3#6) := by crush

theorem bv_ult_inequality (i j max : BitVec 64)
    (h0 : BitVec.ult i max) (h1 : BitVec.ule j (max - i))
    (h2 : BitVec.ult 0#64 j) : BitVec.ult (max - (i + j)) (max - i) := by crush

/-! ### Bridges to the integers

`toNat` is unsigned (`bv2nat`), `toInt` two's-complement signed (`sbv_to_int`), and
`ofNat`/`ofInt` wrap modulo `2 ^ w` exactly as `int2bv` does. -/

theorem bv_tonat : (3#10).toNat = 3 := by crush
theorem bv_toint_pos : (12#10).toInt = 12 := by crush
theorem bv_toint_neg : (686#10).toInt = -338 := by crush
theorem bv_ofint_neg : BitVec.ofInt 4 (-6) = 10#4 := by crush
theorem bv_ofint_pos : BitVec.ofInt 4 10 = 10#4 := by crush

-- `ofNat` applied to a *symbolic* argument needs `int2bv` rather than a literal.
-- The encoding is now right, but this particular round-trip mixes the bit-vector
-- and integer theories and neither z3 nor cvc5 discharges it — hand-writing the
-- same SMT-LIB times out identically, so it is solver difficulty rather than a
-- translation gap.
--
-- What must hold is only that `crush` does **not close** this goal (a false close
-- would be an unsoundness). Which not-proved *verdict* the solver reports —
-- `unknown` (timeout) or `sat` (a counterexample) — is a heuristic/timing artifact
-- that varies across solver builds, so pinning the exact verdict text is
-- non-portable and flipped on CI's Linux z3. Match only the shared `crush:` failure
-- prefix, which every not-proved outcome carries and a false close (no error) does
-- not — so the test still fails loudly if the goal is ever wrongly closed.
/-- error: crush: -/
#guard_msgs(error, substring := true) in
theorem bv_ofnat_symbolic_solver_limit (x y : BitVec 10) :
    BitVec.ofNat 10 (BitVec.toNat x + BitVec.toNat y) = x + y := by crush

/-! ## Arithmetic, `Bool`, and coercions -/

theorem nat_refl (a : Nat) : a = a := by crush
theorem nat_lit_eq : nat_lit 2 = 2 := by crush

-- SMT-LIB has no `max`/`min`; they expand to an `ite`.
theorem nat_maxmin : max 3 4 = 4 ∧ min 1 2 = 1 := by crush
theorem int_maxmin : max (-3 : Int) 4 = 4 ∧ min 1 (-2 : Int) = -2 := by crush

/-! ### Type-directed overloaded operators

A canonical typeclass instance does not imply an SMT theory carrier. Every
operation below is canonical for `OpaqueArithmetic`, but must remain an
uninterpreted function/relation over that datatype rather than being emitted as
integer syntax. Equality congruence proves the goal without knowing the
operations' definitions. -/

private structure OpaqueArithmetic where
  value : Int

private instance : Add OpaqueArithmetic := ⟨fun a b => ⟨a.value + b.value⟩⟩
private instance : Sub OpaqueArithmetic := ⟨fun a b => ⟨a.value - b.value⟩⟩
private instance : Mul OpaqueArithmetic := ⟨fun a b => ⟨a.value * b.value⟩⟩
private instance : Div OpaqueArithmetic := ⟨fun a _ => a⟩
private instance : Mod OpaqueArithmetic := ⟨fun _ b => b⟩
private instance : Neg OpaqueArithmetic := ⟨fun a => ⟨-a.value⟩⟩
private instance : LT OpaqueArithmetic := ⟨fun a b => a.value < b.value⟩
private instance : LE OpaqueArithmetic := ⟨fun a b => a.value ≤ b.value⟩
private instance : Max OpaqueArithmetic := ⟨fun a _ => a⟩
private instance : Min OpaqueArithmetic := ⟨fun _ b => b⟩

set_option crush.trust "reconstruct" in
theorem generic_lt_substitution {alpha} [LT alpha] {x y : alpha}
    (hxy : x < y) (heq : x = y) (hirr : ¬y < y) : False := by
  crush

set_option crush.trust "reconstruct" in
theorem opaque_overloads_are_uninterpreted (a b c : OpaqueArithmetic) (h : a = b) :
    a + c = b + c ∧
    a - c = b - c ∧
    a * c = b * c ∧
    a / c = b / c ∧
    a % c = b % c ∧
    -a = -b ∧
    (a < c ↔ b < c) ∧
    (a ≤ c ↔ b ≤ c) ∧
    (a > c ↔ b > c) ∧
    (a ≥ c ↔ b ≥ c) ∧
    max a c = max b c ∧
    min a c = min b c := by
  crush

private structure ConcreteMembership where
  contains : Int → Bool

private instance : Membership Int ConcreteMembership where
  mem collection x := collection.contains x = true

theorem concrete_class_projection_reduces (collection : ConcreteMembership) (x : Int)
    (hmem : x ∈ collection) (hfalse : collection.contains x = false) : False := by
  crush

private opaque acceptsDecidableEq {α : Type} : DecidableEq α → Bool

-- Dependent decision procedures have no ordinary first-order arrow sort. The
-- result-indexed lowering maps them to the axiomatized singleton decision sort.
theorem dependent_decision_argument_uses_singleton
    (h : acceptsDecidableEq (fun x y : Int => inferInstance) = true) :
    acceptsDecidableEq (fun x y : Int => inferInstance) = true := by
  crush

theorem decisions_are_subsingleton {p : Prop} (a b : Decidable p) : a = b := by
  crush

theorem dependent_decision_procedures_are_subsingleton {α : Type}
    (a b : DecidableEq α) : a = b := by
  crush

theorem decidable_eq_observes_equality (x y : Int) :
    decide (x = y) = true ↔ x = y := by
  crush

-- The equality semantics come from the proposition indexed by the returned
-- `Decidable`, not from the implementation of a particular procedure.
theorem custom_decidable_eq_observes_equality {α : Type}
    (decEq : DecidableEq α) (x y : α) :
    @decide (x = y) (decEq x y) = true ↔ x = y := by
  crush

private class AliasOrder where
  le : Int → Int → Bool

private axiom aliasOrder : AliasOrder
private noncomputable instance : AliasOrder := aliasOrder

private axiom aliasOrder_antisymm :
  ∀ x y, @AliasOrder.le aliasOrder x y = true →
    @AliasOrder.le aliasOrder y x = true → x = y

-- Data instances are implicit-reducible wrappers. Their projections must share
-- SMT identity with projections from the wrapped witness.
theorem implicit_reducible_instance_alias (x y : Int)
    (hxy : AliasOrder.le x y = true) (hyx : AliasOrder.le y x = true) :
    x = y := by
  crush [aliasOrder_antisymm, *]

-- Constructor-guided synthesis is intentionally one witness deep. Nested
-- existentials proceed to SMT instead of saturating speculative candidate bodies.
theorem nested_existential_uses_solver : ∃ x : Int, ∃ y : Int, x = y := by
  crush

-- The `Nat → Int` coercion is the identity here, since `Nat` is already an `Int`
-- restricted to be non-negative.
theorem nat_cast_int : (2 : Int) = ((nat_lit 2 : Nat) : Int) := by crush

theorem nat_succ_add : Nat.succ 5 = 5 + 1 := by crush
theorem nat_sub_le_zero (a b : Nat) (h : a ≤ b) : a - b = 0 := by crush
theorem bool_decide (a : Bool) : decide a = a := by crush

theorem bool_nested_ite {a b c d : Bool} (h : if (if (2 < 3) then a else b) then c else d) :
    (a → c) ∧ (¬ a → d) := by crush

theorem uf_ignores_extra_args {α β : Type} (f : α → Nat → β → α → Nat) :
    ∀ a b c, f a 1 b c = f a 1 b c := by crush

/-! ## Division and modulus by zero

A reported bug mapped Lean's `/` to truncated division when the default `Int./` is
in fact Euclidean, and left `%` uninterpreted. Lean also pins `x / 0 = 0` and
`x % 0 = x`, where SMT-LIB leaves them underspecified. -/

theorem nat_mod_zero' : (10 : Nat) % 0 = 10 := by crush
theorem int_mod_zero' : (10 : Int) % (0 : Int) = 10 := by crush
theorem int_div_zero' : (10 : Int) / (0 : Int) = 0 := by crush

/-! ## Strings -/

theorem str_len_abc : String.length "abc" = 3 := by crush
theorem str_prefix_abcd : String.isPrefixOf "ab" "abcd" := by crush
theorem str_assoc' (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by crush

-- Literals containing characters that need SMT-LIB escaping. Note `\` is *not* an
-- escape character in SMT-LIB, so it must be emitted literally.
theorem str_escapes : "|,\\|" = "|,\\|" := by crush
theorem str_amp : "&" = "&" := by crush

/-! ## Higher-order

A `∃` over a function type, and a function-valued hypothesis — the shapes that
made the other implementation report "Higher order input?". -/

theorem ho_bool_exists (h : ∃ b, !(!b) ≠ b) : False := by crush

/-! ## Parametric datatypes (via monomorphization)

`Prod`, `Option`, `List`, … take type parameters. A *fully-applied* such type
(`Option Int`, `Int × Int`, `List Bool`) is monomorphized into a real SMT datatype at
that instantiation (see `declareDatatype`/`isSupportedDatatypeApp` in
`Translation/Translate.lean`), so its constructors are injective, distinct, and
exhaustive — not merely uninterpreted. Distinct instantiations get distinct sorts, so
`Option Int` and `Option Bool` never conflate. -/

-- Congruence through a monomorphized constructor.
theorem option_congr (x y : Int) (h : x = y) : Option.some x = Option.some y := by crush
theorem prod_congr (x y : Int) (h : x = y) : (x, 0) = (y, 0) := by crush

-- Constructor *injectivity*: now provable, since `Option Int` is a real datatype.
theorem option_inj (x y : Int) (h : Option.some x = Option.some y) :
    x = y := by crush

-- Constructors are distinct: `none ≠ some x`.
theorem option_distinct (x : Int) : (Option.some x) ≠ Option.none := by crush

private inductive ReducibleAliasState where
  | initial
  | accepted

@[reducible] private def acceptedAlias : ReducibleAliasState :=
  .accepted

-- Reducible term aliases share the constructor's SMT identity rather than
-- becoming unrelated nullary uninterpreted symbols.
theorem reducible_term_alias_is_transparent (state : ReducibleAliasState)
    (h : state = acceptedAlias) : state ≠ .initial := by
  crush

-- A `List Int` instantiation: `cons` is injective in both head and tail.
theorem list_cons_inj (a b : Int) (as bs : List Int)
    (h : a :: as = b :: bs) : a = b ∧ as = bs := by crush

/-! ## Definitionally equal datatype parameters

Generated DSLs often package several types in a signature record and expose
datatype aliases through its projections. The projection and constructor paths
must allocate the same SMT datatype when their type arguments are definitionally
equal but not structurally identical before reduction. -/

private structure PackedTypes where
  Event : Type
  Goto : Type

private abbrev packedTypes : PackedTypes where
  Event := Int
  Goto := Bool

private inductive PackedAction (E G : Type) where
  | event (e : E)
  | goto (g : G)

private structure PackedLabel (E G : Type) where
  action : PackedAction E G

private abbrev PackedTypes.Label (P : PackedTypes) :=
  PackedLabel P.Event P.Goto

theorem datatype_projection_constructor_sort_identity
    (lbl : packedTypes.Label) (x : Int)
    (h : lbl.action =
      PackedAction.event (G := Bool) x) :
    lbl.action ≠ PackedAction.goto (E := Int) false := by
  crush [h]

/-! ## Datatypes -/

theorem unit_eq (x y : Unit) : x = y ∧ x = () := by crush

private inductive Color3 where
  | red
  | green
  | ultraviolet

-- Pigeonhole: four values in a three-constructor enumeration must collide.
theorem enum_pigeonhole (x y z t : Color3) :
    x = y ∨ x = z ∨ x = t ∨ y = z ∨ y = t ∨ z = t := by crush

-- η for pairs: `Prod Int Int` is now a real datatype with selectors, so the
-- projection form equals the original.
theorem prod_eta (x : Int × Int) : x = (Prod.fst x, Prod.snd x) := by crush
