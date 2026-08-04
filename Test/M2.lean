import Crush

/-!
Milestone-2 tests: theory correctness, especially the Nat→Int soundness
obligations from `Doc/PLAN.md` §10. Each `example`/`theorem` that elaborates is a
passing test; the negative cases use `first | (crush; done) | sorry` so a
regression (crush wrongly closing a false goal) turns the `sorry` into a *closed*
proof and the file's `sorry` warning disappears — a signal we watch for.
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
theorem must_reject_sub : ∀ n : Nat, n - 1 < n := by
  first | (crush; done) | sorry

/-! ## Int arithmetic (signed, no truncation) -/

theorem int_sub_neg : ∀ x : Int, x - (x + 1) = -1 := by crush
theorem int_order (x y : Int) (h : x < y) : x + 1 ≤ y := by crush

/-! ## Int division/mod — Lean's default `Int./`/`%` are Euclidean (remainder
    ≥ 0), matching SMT-LIB `div`/`mod`, so the direct mapping is sound. -/

theorem int_ediv : ((-7 : Int) / 2) = -4 := by crush
theorem int_emod : ((-7 : Int) % 2) = 1 := by crush
theorem int_mod_nonneg : ∀ x : Int, x % 2 ≥ 0 := by crush

-- FALSE under Euclidean division (that would be truncated T-division): rejected.
theorem must_reject_tdiv : ((-7 : Int) / 2) = -3 := by
  first | (crush; done) | sorry

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

/-! ### `Nat` fields in datatypes — the freely-generated-datatype hole

SMT datatypes are freely generated over their field sorts, so a `Nat` field
(encoded as `Int`) admits *negative* values that no Lean value has. Unguarded,
the **true** hypothesis `∀ p : PN, p.x ≥ 0` becomes UNSAT, from which the solver
derives `False` — a false `unsat`, the dangerous direction. Fixed by emitting a
`wf_T` predicate and guarding every quantifier over `T` (§10 P9). -/

structure PN where
  x : Nat

-- The hypothesis is true in Lean, so `False` must NOT be derivable from it.
theorem must_reject_nat_field (h : ∀ p : PN, p.x ≥ 0) : False := by
  first | (crush; done) | sorry

-- The guard must not over-restrict: real facts about `Nat` fields still go through.
theorem pn_field_nonneg (p : PN) : p.x ≥ 0 := by crush
theorem pn_field_cong (p q : PN) (h : p = q) : p.x = q.x := by crush

-- Truncated subtraction stays truncated inside a field, too.
theorem must_reject_field_sub : ∀ p : PN, p.x - 1 < p.x := by
  first | (crush; done) | sorry

/-! ### Uninhabited types

Every SMT sort is non-empty, but `Empty` is not: `∀ x : Empty, P` is vacuously
true while its naive SMT image `(forall ((x S)) P)` is not. `crush` refuses the
translation rather than emitting an unsound encoding. -/

theorem must_reject_empty (h : ∀ x : Empty, False) : False := by
  first | (crush; done) | sorry

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
theorem must_reject_bv_div_zero : (4 : BitVec 8) / 0 = 255 := by
  first | (crush; done) | sorry

/-! ### Int division by zero

SMT-LIB leaves `(div x 0)` to the model, so this direction was already *sound*
but incomplete; `intDivGuard` pins Lean's values so the encoding is exact. -/

theorem int_div0 (x : Int) : x / 0 = 0 := by crush
theorem int_mod0 (x : Int) : x % 0 = x := by crush
theorem nat_div0 (n : Nat) : n / 0 = 0 := by crush

/-! ## Strings

`str.len` counts codepoints, matching `String.length`. Note that `\` is *not* an
escape character in SMT-LIB, so non-printable characters use `\u{…}` (see
`Crush.SMT.escapeSmtString`). -/

theorem str_append : ("ab" ++ "cd") = "abcd" := by crush
theorem str_len : "ab".length = 2 := by crush
theorem str_len_unicode : "λx".length = 2 := by crush
theorem str_len_quote : "a\"b".length = 3 := by crush
theorem str_prefix : "abc".isPrefixOf "abcd" = true := by crush
theorem str_assoc (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by crush
theorem str_len_nonneg (s : String) : s.length ≥ 0 := by crush
theorem str_cong (a b : String) (h : a = b) : a.length = b.length := by crush

-- FALSE: the empty string has length 0.
theorem must_reject_str_len : ∀ s : String, s.length > 0 := by
  first | (crush; done) | sorry
