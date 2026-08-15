import Crush

/-!
Theory-correctness tests: `Nat`/`Int` arithmetic, datatypes, bit-vectors, and
strings. Each `theorem` that elaborates without error is a passing test.

Negative tests — goals that are *false* in Lean and must be rejected rather than
closed — are wrapped in `#guard_msgs`, which pins the rejection message. If a
regression ever lets `crush` close one of them, the expected error is not produced
and the build **fails**. `substring := true` matches only the stable prefix of the
message, so the solver-dependent counterexample text does not make the test
brittle.

Several of the negative tests below correspond to bugs that were once live, where
`crush` proved something false. Each is annotated with what went wrong.
-/

open Crush

set_option crush.trust "trust"

/-! ## Nat well-formedness (non-negativity) -/

-- A bare `Nat` variable must carry `≥ 0` in the encoding.
theorem nat_nonneg (n : Nat) : 0 ≤ n := by crush

-- Truncated subtraction: `n - 1 ≤ n` always, and `n - (n+1) = 0`.
theorem nat_sub_le : ∀ n : Nat, n - 1 ≤ n := by crush
theorem nat_sub_trunc : ∀ n : Nat, n - (n + 1) = 0 := by crush

-- Nat-valued uninterpreted function result is non-negative.
theorem nat_fun_nonneg (f : Nat → Nat) (n : Nat) : 0 ≤ f n := by crush

/-! ## Negative cases — must be REJECTED, not closed -/

-- FALSE: n = 0 gives 0 - 1 = 0, so `0 < 0` is false. The pre-fix naive `Int`
-- translation wrongly proved this; the `≥0` guard + truncated `sub` fix it.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_sub : ∀ n : Nat, n - 1 < n := by crush

/-! ## Int arithmetic (signed, no truncation) -/

theorem int_sub_neg : ∀ x : Int, x - (x + 1) = -1 := by crush
theorem int_order (x y : Int) (h : x < y) : x + 1 ≤ y := by crush

/-! ## Int division/mod — Lean's default `Int./`/`%` are Euclidean (remainder
    ≥ 0), matching SMT-LIB `div`/`mod`, so the direct mapping is sound. -/

theorem int_ediv : ((-7 : Int) / 2) = -4 := by crush
theorem int_emod : ((-7 : Int) % 2) = 1 := by crush
theorem int_mod_nonneg : ∀ x : Int, x % 2 ≥ 0 := by crush

-- FALSE under Euclidean division (that would be truncated T-division): rejected.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_tdiv : ((-7 : Int) / 2) = -3 := by crush

/-! ## if-then-else -/

theorem ite_prop (x : Int) : (if x > 0 then x else -x) ≥ 0 := by crush
theorem ite_bool (b : Bool) (x y : Int) (h : b = true) : (if b then x else y) = x := by crush

/-! ## Datatypes: enumerations and structures -/

inductive Color where | red | green | blue

theorem col_distinct : Color.red ≠ Color.green := by crush
theorem col_cases (c : Color) : c = Color.red ∨ c = Color.green ∨ c = Color.blue := by crush

structure Point where
  x : Int
  y : Int

theorem pt_proj (a b : Int) : (Point.mk a b).x = a := by crush
theorem pt_cong (p q : Point) (h : p = q) : p.x = q.x := by crush

/-! ### Constructor-name collisions

Two structures both use the anonymous constructor name `mk`. Before the
`ctorSymbol`/`selSymbol` qualification, both emitted `mk`/`mk_sel0` into one
script, conflating distinct types' constructors and selectors. -/

structure P1 where a : Int
structure P2 where b : Int

theorem no_collide (x y : Int) (h : (P1.mk x).a = x) : (P2.mk y).b = y := by crush

inductive DerivedCollision where
  | node_0
  | node (value : Int)

set_option crush.backend "none" in
theorem derived_role_no_collide (value : Int) :
    DerivedCollision.node value ≠ DerivedCollision.node_0 := by
  crush
  simp

/-! ### `Nat` fields in datatypes — the freely-generated-datatype hole

SMT datatypes are freely generated over their field sorts, so a `Nat` field
(encoded as `Int`) admits *negative* values that no Lean value has. Unguarded,
the **true** hypothesis `∀ p : PN, p.x ≥ 0` becomes UNSAT, from which the solver
derives `False` — a false `unsat`, the dangerous direction. Fixed by emitting a
`wf_T` predicate and guarding every quantifier over `T`. -/

structure PN where
  x : Nat

-- The hypothesis is true in Lean, so `False` must NOT be derivable from it.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_nat_field (h : ∀ p : PN, p.x ≥ 0) : False := by crush

-- The guard must not over-restrict: real facts about `Nat` fields still go through.
theorem pn_field_nonneg (p : PN) : p.x ≥ 0 := by crush
theorem pn_field_cong (p q : PN) (h : p = q) : p.x = q.x := by crush

-- Truncated subtraction stays truncated inside a field, too.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_field_sub : ∀ p : PN, p.x - 1 < p.x := by crush

/-! ### Uninhabited types

Every SMT sort is non-empty, but `Empty` is not: `∀ x : Empty, P` is vacuously
true while its naive SMT image `(forall ((x S)) P)` is not. `crush` refuses the
translation rather than emitting an unsound encoding. -/

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_empty (h : ∀ x : Empty, False) : False := by crush

/-! ### Recursive datatypes

`declare-datatypes` is itself recursive, so self-recursive Lean inductives map
across directly (constructor distinctness and selectors included). -/

inductive IList where
  | nil
  | cons (hd : Int) (tl : IList)

-- Constructor distinctness and injectivity across the recursive occurrence.
-- (A multi-constructor inductive has no projection functions, so the selectors
-- are exercised through constructor equations rather than field notation.)
theorem il_distinct (h : Int) (t : IList) : IList.cons h t ≠ IList.nil := by crush
theorem il_cong (a b : IList) (h : a = b) : IList.cons 1 a = IList.cons 1 b := by crush
theorem il_inj (x y : Int) (s t : IList) (h : IList.cons x s = IList.cons y t) :
    x = y := by crush

/-! ### Recursive datatypes with a *guarded* field

An `Int` field needs no guard, so `IList`'s `wf` is constantly `true` and never
actually recurses. A `Nat` field is the case that produces a genuinely **recursive**
`wf` definition:

```
(define-fun-rec wf_NList ((x NList)) Bool
  (=> ((_ is cons) x) (and (>= (hd x) 0) (wf_NList (tl x)))))
```

Using a recursive definition instead of a quantified defining axiom avoids
quantifier-instantiation loops while preserving the guard through the tail. -/

inductive NList where
  | nil
  | cons (hd : Nat) (tl : NList)

theorem nl_distinct (n : Nat) (t : NList) : NList.cons n t ≠ NList.nil := by crush
theorem nl_deep (a b c : Nat) (t : NList) :
    NList.cons a (NList.cons b (NList.cons c t)) ≠ NList.nil := by crush
-- The recursive guard must propagate into the tail, not just the outermost field.
theorem nl_tail_field (l : NList) (n : Nat) (t : NList) (h : l = NList.cons n t) :
    n ≥ 0 := by crush
-- Quantifying over the recursive type is where the recursive axiom gets exercised.
theorem nl_quant : ∀ l : NList, l = NList.nil ∨ ∃ n t, l = NList.cons n t := by crush
-- A false goal about the guarded field must produce a counterexample, not close.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_not_close_nl_field : ∀ (n : Nat) (t : NList),
    NList.cons n t = NList.cons (n - 1) t := by crush

/-! ### Transitive well-formedness

`wf` must compose through nesting: `Outer` has no `Nat` field of its own, but
reaches one through `Inner`. If `needsWFGuard` stopped at the first level, the
`Nat`-in-datatype hole would reopen one level down. -/

structure Inner where n : Nat
structure Outer where i : Inner

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_nested (h : ∀ o : Outer, o.i.n ≥ 0) : False := by crush
theorem nested_field_nonneg (o : Outer) : o.i.n ≥ 0 := by crush

/-! ## Bit-vectors

`BitVec w` at a statically-known width maps to the indexed sort `(_ BitVec w)`.
Lean's `/` and `%` on `BitVec` are the *unsigned* operations, and Lean's `<`/`≤`
are unsigned comparisons (`(255 : BitVec 8) < 1` is `false`). -/

theorem bv_add0 (x : BitVec 8) : x + 0 = x := by crush
theorem bv_comm (x y : BitVec 8) : x + y = y + x := by crush
theorem bv_wrap : (255 : BitVec 8) + 1 = 0 := by crush
theorem bv_and_idem (x : BitVec 8) : x &&& x = x := by crush
theorem bv_not_not (x : BitVec 8) : ~~~(~~~x) = x := by crush
theorem bv_xor_self (x : BitVec 8) : x ^^^ x = 0 := by crush
theorem bv_neg (x : BitVec 8) : x + (-x) = 0 := by crush

-- `<` on `BitVec` is UNSIGNED, so `255 < 1` is false but `slt 255 1` (i.e.
-- `-1 < 1`) is true. Getting this backwards would be unsound in both directions.
theorem bv_ult : (1 : BitVec 8) < 255 := by crush
theorem bv_unsigned_not_signed : ¬((255 : BitVec 8) < 1) := by crush
theorem bv_slt : BitVec.slt (255 : BitVec 8) 1 = true := by crush

theorem bv_shl : (1 : BitVec 8) <<< (1 : Nat) = 2 := by crush
theorem bv_shr : (4 : BitVec 8) >>> (1 : Nat) = 2 := by crush
theorem bv_ashr : BitVec.sshiftRight (-(4) : BitVec 8) 1 = -2 := by crush

-- `++` puts the left operand in the HIGH bits, matching SMT `concat`.
theorem bv_concat : (4 : BitVec 8) ++ (5 : BitVec 4) = 0x045 := by crush
theorem bv_setwidth_grow : BitVec.setWidth 16 (255 : BitVec 8) = 0x00ff := by crush
theorem bv_setwidth_shrink : BitVec.setWidth 4 (255 : BitVec 8) = 0xf := by crush
theorem bv_signextend : BitVec.signExtend 16 (255 : BitVec 8) = 0xffff := by crush
theorem bv_extract : BitVec.extractLsb' 0 4 (0xAB : BitVec 8) = 0xb := by crush

/-! ### Bit-vector division by zero — a genuine Lean/SMT *disagreement*

Unlike `Int` `div`/`mod` (which SMT leaves *underspecified*, so any Lean value is
admissible), SMT-LIB **fixes** `bvudiv x 0` to all-ones and `bvsdiv x 0` to `±1`,
contradicting Lean's `x / 0 = 0`. Emitting the raw operator therefore lets the
solver prove goals that are false in Lean. `bvDivGuard` rewrites to an `ite`.

`bvurem`/`bvsrem`/`bvsmod` already agree with Lean (all return the dividend). -/

theorem bv_udiv0 (x : BitVec 8) : x / 0 = 0 := by crush
theorem bv_sdiv0 (x : BitVec 8) : BitVec.sdiv x 0 = 0 := by crush
theorem bv_urem0 (x : BitVec 8) : x % 0 = x := by crush
theorem bv_srem0 (x : BitVec 8) : BitVec.srem x 0 = x := by crush
theorem bv_smod0 (x : BitVec 8) : BitVec.smod x 0 = x := by crush

-- FALSE in Lean (`4 / 0 = 0`), but exactly the value raw SMT `bvudiv` returns.
-- If this ever closes, the div-by-zero guard has regressed.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_bv_div_zero : (4 : BitVec 8) / 0 = 255 := by crush

/-! ### Int division by zero

SMT-LIB leaves `(div x 0)` to the model, so this direction was already *sound*
but incomplete; `intDivGuard` pins Lean's values so the encoding is exact. -/

theorem int_div0 (x : Int) : x / 0 = 0 := by crush
theorem int_mod0 (x : Int) : x % 0 = x := by crush
theorem nat_div0 (n : Nat) : n / 0 = 0 := by crush

/-! ## Head-indexed library lowerings -/

theorem int_natAbs_nonneg (x : Int) : 0 ≤ x.natAbs := by crush
theorem int_natAbs_neg (x : Int) : (-x).natAbs = x.natAbs := by crush
theorem int_sign_cases (x : Int) : x.sign = -1 ∨ x.sign = 0 ∨ x.sign = 1 := by crush
theorem int_sign_pos (x : Int) (h : 0 < x) : x.sign = 1 := by crush

theorem int_dvd_iff_mod (a b : Int) : a ∣ b ↔ b % a = 0 := by crush
theorem nat_dvd_iff_mod (a b : Nat) : a ∣ b ↔ b % a = 0 := by crush
theorem int_zero_dvd (b : Int) : 0 ∣ b ↔ b = 0 := by crush
theorem nat_zero_dvd (b : Nat) : 0 ∣ b ↔ b = 0 := by crush
theorem int_one_dvd (b : Int) : 1 ∣ b := by crush
theorem nat_one_dvd (b : Nat) : 1 ∣ b := by crush

-- Assigning canonical arithmetic semantics to this deliberately false instance
-- would let crush prove the false goal `1 ∣ 1`.
@[reducible] def noIntDvd : Dvd Int := ⟨fun _ _ => False⟩

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_custom_dvd : @Dvd.dvd Int noIntDvd 1 1 := by crush

section
local instance (priority := high) : Dvd Int := noIntDvd

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_scoped_dvd : (1 : Int) ∣ 1 := by
  crush
end

-- A local instance must not become its own "canonical" baseline.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_local_add [inst : HAdd Int Int Int] :
    @HAdd.hAdd Int Int Int inst 1 2 = 3 := by
  crush

/-! ## Strings

`str.len` counts codepoints, matching `String.length`. A Lean `\` is emitted as
`\u{5c}` so it cannot begin an SMT-LIB escape; other non-printable characters use
`\u{…}` (see `Crush.SMT.escapeSmtString`). -/

theorem str_append : ("ab" ++ "cd") = "abcd" := by crush
theorem str_len : "ab".length = 2 := by crush
theorem str_len_unicode : "λx".length = 2 := by crush
theorem str_len_quote : "a\"b".length = 3 := by crush
theorem str_prefix : "abc".isPrefixOf "abcd" = true := by crush
theorem str_assoc (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by crush
theorem str_len_nonneg (s : String) : s.length ≥ 0 := by crush
theorem str_cong (a b : String) (h : a = b) : a.length = b.length := by crush
theorem str_beq_reflects_eq (a b : String) (h : a == b) : a = b := by crush
theorem str_startsWith (a b : String) : (a ++ b).startsWith a = true := by crush
theorem str_endsWith (a b : String) : (a ++ b).endsWith b = true := by crush
theorem str_contains_self (s : String) : s.contains s = true := by crush
theorem str_contains_append (a b : String) : (a ++ b).contains a = true := by crush
theorem str_any_append (a b : String) : (a ++ b).any a = true := by crush
theorem str_isEmpty_iff (s : String) : s.isEmpty = true ↔ s = "" := by crush

-- The notation-level lowering must not assign `str.++` semantics to a custom
-- `HAppend String String String` instance.
@[reducible] def constantStringAppend : HAppend String String String :=
  ⟨fun _ _ => "constant"⟩

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_custom_string_append :
    @HAppend.hAppend String String String constantStringAppend "a" "b" = "ab" := by
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_local_string_append [inst : HAppend String String String] :
    @HAppend.hAppend String String String inst "a" "b" = "ab" := by
  crush

section
local instance (priority := high) : HAppend String String String :=
  constantStringAppend

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_scoped_string_append : ("a" ++ "b") = "ab" := by
  crush
end

@[reducible] def falseStringBEq : BEq String :=
  ⟨fun _ _ => false⟩

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_custom_string_beq :
    @BEq.beq String falseStringBEq "a" "a" = true := by
  crush

section
local instance (priority := high) : BEq String := falseStringBEq

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_scoped_string_beq : ("a" == "a") = true := by
  crush
end

@[reducible] def reverseStringLT : LT String :=
  ⟨fun a b => b.toList < a.toList⟩

@[reducible] def falseStringLE : LE String :=
  ⟨fun _ _ => False⟩

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_custom_string_lt :
    @LT.lt String reverseStringLT "a" "b" := by
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_custom_string_le :
    @LE.le String falseStringLE "a" "a" := by
  crush

section
local instance (priority := high) : LT String := reverseStringLT
local instance (priority := high) : LE String := falseStringLE

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_scoped_string_lt : ("a" : String) < "b" := by
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_scoped_string_le : ("a" : String) ≤ "a" := by
  crush
end

@[reducible] def neverMatchesPrefix
    (pattern : String) : String.Slice.Pattern.ForwardPattern pattern where
  skipPrefix? := fun _ => none
  startsWith := fun _ => false

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_custom_string_pattern :
    @String.startsWith String "abc" "a" (neverMatchesPrefix "a") = true := by
  crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_local_string_pattern
    [inst : String.Slice.Pattern.ForwardPattern ("a" : String)] :
    @String.startsWith String "abc" "a" inst = true := by
  crush

section
local instance (priority := high) :
    String.Slice.Pattern.ForwardPattern ("a" : String) :=
  neverMatchesPrefix "a"

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_scoped_string_pattern : "abc".startsWith "a" = true := by
  crush
end

@[reducible] def neverMatchesSuffix
    (pattern : String) : String.Slice.Pattern.BackwardPattern pattern where
  skipSuffix? := fun _ => none
  endsWith := fun _ => false

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_custom_string_suffix_pattern :
    @String.endsWith String "abc" "a" (neverMatchesSuffix "a") = true := by
  crush

-- `contains` has a separate searcher dictionary from `startsWith`. An arbitrary
-- local searcher must remain uninterpreted even though its iterator machinery is
-- the standard `String` implementation.
open String.Slice.Pattern in
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_local_string_searcher
    [inst : ToForwardSearcher ("a" : String) ForwardSliceSearcher] :
    @String.contains String ForwardSliceSearcher
      ForwardSliceSearcher.instIteratorIdSearchStep
      (ForwardSliceSearcher.instIteratorLoopIdSearchStep (m := Id))
      "abc" "a" inst = true := by
  crush

-- SMT-LIB 2.6 strings cannot contain codepoints above U+2FFFF. Consequently,
-- `str.<=` would prove this false statement over SMT's smaller domain: Lean has
-- the one-codepoint counterexample U+30000.
example : ¬ (("𰀀" : String) ≤ "𯿿") := by decide

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_string_order_domain_mismatch (s : String) (h : s.length = 1) :
    s ≤ "𯿿" := by
  crush

-- Lean's empty-pattern replacement is "xax", but SMT `str.replace_all` returns
-- the input unchanged. A direct lowering would prove this false statement.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_smt_replace_empty_semantics :
    "a".replace "" "x" = "a" := by
  crush

-- A literal Lean backslash must not start an SMT-LIB Unicode escape.
theorem str_escape_not_alias : ("\\u{61}" : String) ≠ "a" := by crush

/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_string_escape_alias : ("\\u{61}" : String) = "a" := by crush

-- FALSE: the empty string has length 0.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_str_len : ∀ s : String, s.length > 0 := by crush

/-! ## Type and proof arguments must not become terms

A polymorphic constant's *type* argument and a dependent function's *proof*
argument have no SMT counterpart. Passing them through emitted the type as a term:
`@List.length Int []` became `length(Int_4, nil(Int_4))` where `Int_4` was a
`Bool`-sorted constant fed to an `Int`-returning symbol.

That output is ill-sorted, and worth stressing: **z3 does not reject it**. It
silently reinterprets `(= x true)` for an `Int`-sorted `x`, so nothing surfaces at
the solver boundary — the only symptom is wrong answers. `defaultApp` now drops such
arguments and keys the symbol on the head *together with* its type arguments, so
distinct instantiations stay distinct instead of being conflated. -/

axiom polyConst : {α : Type} → α

-- Two instantiations at different types must get separate, correctly-sorted
-- symbols rather than one symbol applied to a type-as-term.
theorem poly_instantiations_distinct
    (h1 : (polyConst : Int) = 5) (h2 : (polyConst : Bool) = true) :
    (polyConst : Int) = 5 := by crush

theorem type_arg_dropped (h : @List.length Int [] = 0) :
    @List.length Int [] = 0 := by crush

-- A dependent binder over a *proof*. The body mentions the proof, so the binder
-- cannot simply be discarded; introducing a real fvar keeps the body closed. This
-- used to fail with an internal "unexpected bound variable #0", leaking a de Bruijn
-- index out of the translator.
theorem dependent_proof_binder (f : (n : Nat) → n > 0 → Nat) (h5 : (5 : Nat) > 0)
    (hf : ∀ n, ∀ hn : n > 0, f n hn = n) : f 5 h5 = 5 := by crush

/-! ## `Type` is not `Bool`

`Prop` maps to SMT `Bool`, but a larger universe must not: that would put every Lean
type into a two-element set, so three distinct types would be forced to collide.
A type-valued position gets an opaque (uninterpreted) sort instead. -/

-- FALSE for any injective `Nat → Type`, and `crush` proved it when `Type` mapped to
-- `Bool` — with only two inhabitants, pigeonhole forces a collision.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_type_pigeonhole (tyfn : Nat → Type) (a b c : Nat) :
    tyfn a = tyfn b ∨ tyfn a = tyfn c ∨ tyfn b = tyfn c := by crush

-- Reflexivity still goes through with the opaque sort, and `Prop` still maps to
-- `Bool` as it must.
theorem type_refl_ok (tyfn : Nat → Type) (a : Nat) : tyfn a = tyfn a := by crush
theorem prop_still_bool (P : Nat → Prop) (h : ∀ n, P n) : P 5 := by crush

/-! ## Overloaded operators require the *standard* instance

Recognizing `HAdd.hAdd _ _ _ inst a b` as SMT `+` commits to `inst` being the
standard instance. A user may supply another — `⟨fun _ _ => 99⟩` is a perfectly legal
`HAdd Int Int Int` — and then `1 + 2` is `99`. Matching on the head alone therefore
imported arithmetic that does not hold. The recognizers now check the instance
against what synthesis would pick, and fall through to an uninterpreted symbol when
it differs. -/

/-- A non-standard `HAdd Int Int Int` that ignores its operands. -/
@[reducible] def weirdAdd : HAdd Int Int Int := ⟨fun _ _ => 99⟩

-- FALSE: the real value is `99`. `crush` proved this by assuming standard `Int`
-- addition, giving `1 + 2 = 3`.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_nonstandard_add : @HAdd.hAdd Int Int Int weirdAdd 1 2 = 3 := by crush

-- Standard arithmetic must be unaffected by the instance check.
theorem standard_add_still_works : ∀ x : Int, x + 0 = x := by crush
theorem standard_cmp_still_works (x y : Int) (h : x ≤ y) : x < y + 1 := by crush
theorem standard_max_still_works : max (3 : Int) 4 = 4 := by crush

/-! ## `Nat.cast` is the identity only into `Int`

`Nat` is represented as a non-negative `Int`, so `Nat.cast` into `Int` is the
identity. Into *any other* `NatCast` type it is an arbitrary function, which may
collapse distinct values — so treating it as the identity imports `Int`'s
distinctness and lets the solver prove that equal things differ. -/

/-- A `NatCast` instance collapsing every `Nat` to one value. -/
structure Collapsed where val : Int
instance : NatCast Collapsed := ⟨fun _ => ⟨0⟩⟩

-- FALSE: both casts are `⟨0⟩`, so they are equal. `crush` proved them *distinct* by
-- treating the cast as the identity, and `False` followed from that plus `rfl`.
/-- error: crush: could not prove the goal -/
#guard_msgs(error, substring := true) in
theorem must_reject_collapsing_cast :
    ((2 : Nat) : Collapsed) ≠ ((3 : Nat) : Collapsed) := by crush

-- The `Nat → Int` coercion, which *is* the identity here, still works.
theorem nat_cast_int_still_works : (2 : Int) = ((2 : Nat) : Int) := by crush
