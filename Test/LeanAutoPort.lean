import Crush

/-!
Goals ported from **lean-auto**'s `Test/SmtTranslation/` suite — the tool lean-crush
is a redesign of — to demonstrate we handle the same corpus. Each `auto` there
becomes `crush` here; lean-auto's `auto.smt.trust true` maps to `crush.trust "trust"`,
since this file measures *translation + solving* coverage, not reconstruction (that is
`Test/Reconstruct.lean`'s job). `auto`'s `d[f]` definition-unfold hints map to
`crush`'s `u[f]`.

Porting notes worth stating up front:

* lean-auto runs with `autoImplicit` on; this project has it off (`lakefile.lean`), so
  ported goals get explicit `{α : Type}` binders. That is a syntax difference, not a
  capability one.
* Two categories where the behaviours *intentionally differ* are called out in their
  own sections below: the `Empty`-type goals (we are **sound** where lean-auto
  documents itself unsound) and the cases that were translation gaps until this port
  surfaced them.
-/

open Crush

set_option crush.trust "trust"
set_option crush.timeout 10

/-! ## `BoolNatInt` — arithmetic, Bool, coercions, quantified UF -/

example (a : Nat) : a = a := by crush
example : nat_lit 2 = 2 := by crush
example : max 3 4 = 4 ∧ min 1 2 = 1 := by crush
example : (2 : Int) = ((nat_lit 2) : Int) := by crush
example : max (-3) 4 = 4 ∧ min 1 (-2) = -2 := by crush
example {α β : Type} (f : α → Nat → β → α → Nat) :
    ∀ a b c, f a 1 b c = f a 1 b c := by crush
example (a b : Nat) (h : a ≤ b) : a - b = 0 := by crush
example (x : Nat) : Nat.succ x = x + 1 := by crush
example : String.length "abc" = 3 := by crush
example (_ : ∃ b, !(!b) ≠ b) : False := by crush
example {a b c d : Bool} (h : if (if (2 < 3) then a else b) then c else d) :
    (a → c) ∧ (¬ a → d) := by crush
example {a : Bool} : decide a = a := by crush

/-! ## `BitVec` — arithmetic, rotates, shifts, resize, concat, bv↔int

These are the bulk of lean-auto's hardest theory tests. All translate to the SMT
BitVec theory and are discharged. `zeroExtend` and the `extractLsb hi lo` form were
uninterpreted-symbol gaps until this port surfaced them (see the notes below). -/

open BitVec

example : (2 : BitVec 7) + (3 : BitVec 7) = (5 : BitVec 7) := by crush
example (k : Nat) (a : BitVec k) : a = a := by crush
example (a b : BitVec 10) : a + b = b + a := by crush
example (a b c : BitVec 1) : a = b ∨ b = c ∨ c = a := by crush
example : (2 : BitVec 7).rotateLeft 3 = (16 : BitVec 7) := by crush
example (x : BitVec 15) : x.rotateLeft 3 = x.rotateRight 12 := by crush
example (x : BitVec 8) : x.rotateLeft 104 = x := by crush
example : 101#32 <<< 2#32 = 404#32 := by crush
example : (3#10).toNat = 3 := by crush
example : (12#10).toInt = 12 ∧ (686#10).toInt = -338 := by crush
example : BitVec.ofInt 4 (-6) = 10#4 := by crush
example (x : BitVec 4) : x + (BitVec.not x) = 0xF#4 := by crush
example (a b : BitVec 6) : (a < b) = (a.ult b) ∧ (a ≤ b) = (a.ule b) := by crush
example (i j max : BitVec 64)
    (h0 : BitVec.ult i max) (h1 : BitVec.ule j (max - i)) (h2 : BitVec.ult 0#64 j) :
    BitVec.ult (max - (i + j)) (max - i) := by crush

-- `zeroExtend` is definitionally `setWidth` but a distinct declaration, so the
-- `setWidth` translation arm did not fire on it and it fell through to an
-- uninterpreted symbol. Fixed by adding a `zeroExtend` arm.
example : BitVec.zeroExtend 20 5#10 = 5#20 ∧ BitVec.zeroExtend 3 5#10 = 5#3 := by crush

-- `extractLsb hi lo` (inclusive bit bounds) is distinct from the `extractLsb' lo len`
-- we already handled, so `a[127:64] ++ a[63:0] = a` fell through until an
-- `extractLsb` arm (reducing `hi lo` to a length) was added.
example (a : BitVec 128) :
    (BitVec.extractLsb 127 64 a ++ BitVec.extractLsb 63 0 a) = a := by crush

example :
    BitVec.zeroExtend 20 5#10 = 5#20 ∧ BitVec.zeroExtend 3 5#10 = 5#3 ∧
    BitVec.signExtend 20 645#10 = 1048197#20 ∧ BitVec.signExtend 9 645#10 = 133#9 := by
  crush

/-! ## `String` -/

example : "|,\\|" = "|,\\|" := by crush
example : "&" = "&" := by crush
example (a b c : String) : (a ++ b) ++ c = a ++ (b ++ c) := by crush
example : String.length "abc" = 3 := by crush
example : String.isPrefixOf "ab" "abcd" := by crush

/-! ## Inductive — enums, non-recursive datatypes, unfolding -/

example (x y : Unit) : x = y ∧ x = () := by crush

inductive Color where | red | green | ultraviolet
example (x y z t : Color) : x = y ∨ x = z ∨ x = t ∨ y = z ∨ y = t ∨ z = t := by crush

example {α : Type} (x y : α) (_ : Option.some x = Option.some y) : x = y := by crush
example {α β : Type} (x : α × β) : x = (Prod.fst x, Prod.snd x) := by crush
example {α β : Type} (f : α × β → α) (h : f = Prod.fst) (a : α) (b : β) :
    f (a, b) = a := by crush

-- Enum with per-constructor definition unfolding, via `cases` then `crush u[…]`
-- (lean-auto: `cases x <;> auto d[…]`).
inductive Zone where | Z1 | Z2 | Z3 | Z4
def Zone.MinArea1 : Zone → Int | .Z1 => 10000 | .Z2 => 5000 | .Z3 => 3500 | .Z4 => 2500
def Zone.MinArea2 : Zone → Int | .Z1 => 12000 | .Z2 => 7000 | .Z3 => 4000 | .Z4 => 3000
example (x : Zone) : x.MinArea1 ≤ x.MinArea2 := by
  cases x <;> crush u[Zone.MinArea1, Zone.MinArea2]

/-! ## Recursive functions with unfold hints -/

example {α : Type} (x y : α) : [x] ++ [y] = [x, y] := by
  have h : ∀ (x y : List α), x ++ y = x.append y := fun _ _ => rfl
  crush [h] u[List.append]

def List.myGet? {α : Type} : (as : List α) → (i : Nat) → Option α
  | a :: _,  0     => some a
  | _ :: as, n + 1 => myGet? as n
  | _,       _     => none

example {α : Type} (x y : α) : List.myGet? [x, y] 1 = .some y := by
  crush u[List.myGet?]

example {α : Type} (x : α) : List.head? [x] = .some x := by crush u[List.head?]

/-! ## `Empty` — where we are deliberately SOUND and lean-auto is not

`∀ x y : Empty, x = y` is *true* in Lean (vacuously — `Empty` has no values), and
lean-auto **proves** it. But its encoding maps `Empty` to a non-empty SMT sort, which
its own source flags: "the translation to smt solver is unsound. SMT-LIB assume that
all types are inhabited, while in DTT it's not." lean-crush refuses these instead: an
uninhabited domain has no faithful SMT image (soundness obligation 1), so the solver is
free to invent two distinct `Empty` values and reports a **counterexample**. Declining
to prove a true-but-unfaithfully-encodable goal is the sound choice, and these pins it.
`unknown`/`sat` never closes a goal. -/

/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (x y : Empty) : x = y := by crush

/-- error: crush: the goal is not provable -/
#guard_msgs(error, substring := true) in
example (_ : ¬ (∀ x y : Empty, False)) : False := by crush
