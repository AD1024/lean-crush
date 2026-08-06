import Lean
import Crush.SMT.Syntax
import Crush.SMT.Quote
import Crush.Translation.Monad
open Lean Meta

/-!
# Theory helpers: bit-vectors and strings

Non-recursive helpers shared by the translation driver. The interesting content
here is not the symbol tables — it is the **semantic gap analysis** between Lean's
total functions and SMT-LIB's theory operators.

Every entry below was checked empirically against Lean and against `z3` — the
values were measured in both, not read off either specification. Two classes of
gap show up:

* **Underspecified in SMT** (e.g. `Int` `div`/`mod` by zero). SMT-LIB leaves the
  value of `(div x 0)` to the model, so *any* Lean interpretation — including
  Lean's `x / 0 = 0` — is a valid instantiation. An `unsat` therefore still
  implies Lean validity: this direction is **sound but incomplete**. We close the
  gap with an explicit `ite` so the encoding is exact rather than merely safe.

* **Specified and *different*** (e.g. `bvudiv x 0` is all-ones, while Lean's
  `x / 0` is `0`). Here SMT fixes a value that contradicts Lean, so a false goal
  can be *proved*. This is a genuine **unsoundness** and must be guarded. See
  `bvDivGuard`.

Operators verified to agree exactly (no guard needed): `bvurem`/`bvsrem`/`bvsmod`
at a zero divisor (all return the dividend, as Lean does), `bvlshr`/`bvshl`/
`bvashr` for shift amounts ≥ width, `concat` operand order, `extract`,
`zero_extend`/`sign_extend`, the signed/unsigned comparisons, and `str.len`
(codepoints, matching `String.length`).
-/

namespace Crush

open SMT

/-- The value of a `Nat`-valued expression when it is a literal, looking through
`OfNat.ofNat` (numerals elaborate to `@OfNat.ofNat _ (.lit (.natVal k)) _`). -/
def natValue? (e : Expr) : MetaM (Option Nat) := do
  let e' ← whnf e
  match e' with
  | .lit (.natVal n) => return some n
  | _ =>
    match_expr e' with
    | OfNat.ofNat _ n _ =>
      match (← whnf n) with
      | .lit (.natVal k) => return some k
      | _ => return none
    | _ => return none

/-- The statically-known width of a `BitVec w` type. -/
def bvWidthOfType? (ty : Expr) : MetaM (Option Nat) := do
  match_expr (← whnf ty) with
  | BitVec w => natValue? w
  | _ => return none

/-- The width of `e`'s type when `e : BitVec w`. -/
def bvWidthOf? (e : Expr) : MetaM (Option Nat) := do
  bvWidthOfType? (← inferType e)

/-- Whether `ty` whnf's to `String`. -/
def isStringType (ty : Expr) : MetaM Bool := do
  return (← whnf ty).isConstOf ``String

/-- The SMT sort `(_ BitVec w)`. -/
def bvSort (w : Nat) : SSort := .app (.indexed "BitVec" #[.inr w]) #[]

/-- A bit-vector literal for `n` at width `w`, reduced mod `2 ^ w` exactly as
Lean's `BitVec.ofNat`/`OfNat` do (verified: `(300 : BitVec 8) = 0x2c`). -/
def bvLit (w n : Nat) : SMT.Term := .lit (.bitvec w (n % 2 ^ w))

/-- `((_ extract hi lo) x)`. -/
def bvExtract (hi lo : Nat) (x : SMT.Term) : SMT.Term :=
  .app (.indexed "extract" #[.inr hi, .inr lo]) #[x]

/-- `((_ zero_extend by) x)` / `((_ sign_extend by) x)`, identity at `by = 0`. -/
def bvExtend (signed : Bool) (by_ : Nat) (x : SMT.Term) : SMT.Term :=
  if by_ == 0 then x
  else .app (.indexed (if signed then "sign_extend" else "zero_extend") #[.inr by_]) #[x]

/-- Resize `x : BitVec w` to width `target`: truncate low bits when shrinking,
otherwise extend (zero- or sign-, per `signed`).

Matches Lean's `BitVec.setWidth`/`BitVec.signExtend`, both of which *truncate*
when the target is narrower (verified: `signExtend 4 0xAB#8 = 0xb#4`). -/
def bvResize (signed : Bool) (w target : Nat) (x : SMT.Term) : SMT.Term :=
  if target ≤ w then
    if target == 0 then x else bvExtract (target - 1) 0 x
  else bvExtend signed (target - w) x

/-- Guard a division-like operator whose SMT value at a zero divisor *disagrees*
with Lean's, rewriting it to `(ite (= b 0) zeroVal (op a b))`.

Concretely, Lean returns `0` for `x / 0`, `BitVec.udiv x 0`, and `BitVec.sdiv x 0`,
whereas SMT-LIB fixes `bvudiv x 0 = ~0` and `bvsdiv x 0 = ±1`. Emitting the raw
operator would let the solver prove goals that are false in Lean. -/
def bvDivGuard (op : String) (w : Nat) (a b : SMT.Term) : SMT.Term :=
  let zero := bvLit w 0
  let application := SMT.Term.symbApp op #[a, b]
  (smt| (ite (= $b $zero) $zero $application))

/-- Guard an `Int`/`Nat` division-like operator, which SMT-LIB leaves
*underspecified* at a zero divisor. Lean pins `x / 0 = 0` and `x % 0 = x`, so we
emit `(ite (= b 0) zeroVal (op a b))` to make the encoding exact.

Unlike `bvDivGuard` this is a *completeness* fix rather than a soundness one: an
underspecified SMT operator admits Lean's interpretation, so an `unsat` was
already trustworthy — we merely stop losing provable goals. -/
def intDivGuard (op : String) (a b : SMT.Term) : SMT.Term :=
  let zeroVal := if op == "mod" then a else (smt| 0)
  let application := SMT.Term.symbApp op #[a, b]
  (smt| (ite (= $b 0) $zeroVal $application))

end Crush
