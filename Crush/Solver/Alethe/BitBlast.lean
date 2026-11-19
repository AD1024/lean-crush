/-!
# cvc5's bit-blasted adder and multiplier

cvc5's ripple-carry adder (`addSum`) and shift-and-add multiplier (`mulRow`), proved
equal to `BitVec.add` and `BitVec.mul` at every width. `reify_*` turn decoded
certificate bits back into `Bool` formulas.
-/

namespace Crush.Alethe.BitBlast

/-! ## Ripple-carry addition -/

/-- Carry into bit `i`: `c₀ = false`, `cᵢ₊₁ = (aᵢ ∧ bᵢ) ∨ ((aᵢ ⊕ bᵢ) ∧ cᵢ)`.
`Nat.rec` keeps kernel unfolding direct. -/
def addCarry (a b : Nat → Bool) (i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun i carry => a i && b i || (a i ^^ b i) && carry) i

/-- Sum bit `i`: `(aᵢ ⊕ bᵢ) ⊕ cᵢ`. -/
def addSum (a b : Nat → Bool) (i : Nat) : Bool :=
  (a i ^^ b i) ^^ addCarry a b i

theorem addCarry_zero (a b : Nat → Bool) : addCarry a b 0 = false := rfl

theorem addCarry_succ (a b : Nat → Bool) (i : Nat) :
    addCarry a b (i + 1) = (a i && b i || (a i ^^ b i) && addCarry a b i) := rfl

theorem addCarry_congr {a a' b b' : Nat → Bool} {n : Nat}
    (ha : ∀ k, k < n → a k = a' k) (hb : ∀ k, k < n → b k = b' k) :
    ∀ i, i ≤ n → addCarry a b i = addCarry a' b' i
  | 0, _ => rfl
  | i + 1, hi => by
    rw [addCarry_succ, addCarry_succ, ha i (by omega), hb i (by omega),
      addCarry_congr ha hb i (by omega)]

theorem addSum_congr {a a' b b' : Nat → Bool} {n i : Nat}
    (ha : ∀ k, k < n → a k = a' k) (hb : ∀ k, k < n → b k = b' k) (hi : i < n) :
    addSum a b i = addSum a' b' i := by
  unfold addSum
  rw [ha i hi, hb i hi, addCarry_congr ha hb i (Nat.le_of_lt hi)]

theorem atLeastTwo_eq_ripple (a b c : Bool) :
    Bool.atLeastTwo a b c = (a && b || (a ^^ b) && c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem addCarry_eq_carry {w : Nat} (x y : BitVec w) :
    ∀ i, addCarry x.getLsbD y.getLsbD i = BitVec.carry i x y false
  | 0 => by rw [addCarry_zero, BitVec.carry_zero]
  | i + 1 => by
    rw [addCarry_succ, BitVec.carry_succ, addCarry_eq_carry x y i, atLeastTwo_eq_ripple]

theorem getLsbD_add_eq_addSum {w i : Nat} (x y : BitVec w) (h : i < w) :
    (x + y).getLsbD i = addSum x.getLsbD y.getLsbD i := by
  rw [BitVec.getLsbD_add h, addSum, addCarry_eq_carry, Bool.xor_assoc]

/-- Replay lemma for `bv_bitblast_step_bvadd`. -/
theorem add_eq_of_bits {w : Nat} (L R V : BitVec w) (a b : Nat → Bool)
    (ha : ∀ k, k < w → L.getLsbD k = a k) (hb : ∀ k, k < w → R.getLsbD k = b k)
    (hv : ∀ i, i < w → V.getLsbD i = addSum a b i) : BitVec.add L R = V := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hv i hi]
  show (L + R).getLsbD i = _
  rw [getLsbD_add_eq_addSum L R hi]
  exact addSum_congr ha hb hi

/-! ## Shift-and-add multiplication -/

/-- Column `j` after multiplier rows `0 … k`. Row `k + 1` ripple-adds `b_{k+1} ∧ aₘ`
into column `k + 1 + m`. -/
def mulRow (a b : Nat → Bool) (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun j => b 0 && a j)
    (fun k row j => if j < k + 1 then row j
      else addSum (fun m => row (k + 1 + m)) (fun m => b (k + 1) && a m) (j - (k + 1))) k

theorem mulRow_zero (a b : Nat → Bool) (j : Nat) : mulRow a b 0 j = (b 0 && a j) := rfl

theorem mulRow_succ (a b : Nat → Bool) (k j : Nat) :
    mulRow a b (k + 1) j =
      if j < k + 1 then mulRow a b k j
      else addSum (fun m => mulRow a b k (k + 1 + m)) (fun m => b (k + 1) && a m)
        (j - (k + 1)) := rfl

/-- With `b` false below `s`, no carry reaches bit `s`. -/
theorem addCarry_of_low_false {a b : Nat → Bool} {s : Nat}
    (hb : ∀ m, m < s → b m = false) : ∀ i, i ≤ s → addCarry a b i = false
  | 0, _ => rfl
  | i + 1, hi => by
    rw [addCarry_succ, hb i (by omega), addCarry_of_low_false hb i (by omega)]
    cases a i <;> rfl

theorem addSum_of_low_false {a b : Nat → Bool} {s i : Nat}
    (hb : ∀ m, m < s → b m = false) (hi : i < s) : addSum a b i = a i := by
  unfold addSum
  rw [hb i hi, addCarry_of_low_false hb i (Nat.le_of_lt hi)]
  cases a i <;> rfl

theorem addCarry_shift {a b : Nat → Bool} {s : Nat} (hb : ∀ m, m < s → b m = false) :
    ∀ m, addCarry a b (s + m) = addCarry (fun i => a (s + i)) (fun i => b (s + i)) m
  | 0 => by rw [Nat.add_zero, addCarry_of_low_false hb s (Nat.le_refl s), addCarry_zero]
  | m + 1 => by
    rw [← Nat.add_assoc, addCarry_succ, addCarry_succ, addCarry_shift hb m]

theorem addSum_shift {a b : Nat → Bool} {s : Nat} (hb : ∀ m, m < s → b m = false)
    (m : Nat) :
    addSum a b (s + m) = addSum (fun i => a (s + i)) (fun i => b (s + i)) m := by
  unfold addSum
  rw [addCarry_shift hb m]

theorem mulRow_eq_mulRec {w : Nat} (x y : BitVec w) :
    ∀ k j, j < w → mulRow x.getLsbD y.getLsbD k j = (BitVec.mulRec x y k).getLsbD j
  | 0, j, hj => by
    rw [mulRow_zero, BitVec.mulRec_zero_eq]
    cases y.getLsbD 0 <;> simp
  | k + 1, j, hj => by
    rw [mulRow_succ, BitVec.mulRec_succ_eq, getLsbD_add_eq_addSum _ _ hj]
    have hlow : ∀ m, m < k + 1 →
        (if y.getLsbD (k + 1) = true then x <<< (k + 1) else (0 : BitVec w)).getLsbD m
          = false := by
      intro m hm
      cases y.getLsbD (k + 1) <;> simp [BitVec.getLsbD_shiftLeft, hm]
    by_cases hjk : j < k + 1
    · simp only [hjk, ↓reduceIte]
      rw [addSum_of_low_false hlow hjk, mulRow_eq_mulRec x y k j hj]
    · simp only [hjk, ↓reduceIte]
      obtain ⟨m, rfl⟩ : ∃ m, j = k + 1 + m := ⟨j - (k + 1), by omega⟩
      rw [addSum_shift hlow m, Nat.add_sub_cancel_left]
      apply addSum_congr (n := w - (k + 1))
      · intro i hi
        exact mulRow_eq_mulRec x y k (k + 1 + i) (by omega)
      · intro i hi
        have hlt : k + 1 + i < w := by omega
        have hge : ¬(k + 1 + i < k + 1) := by omega
        have hi' : i < w := by omega
        cases y.getLsbD (k + 1) <;>
          simp [hlt, hge, hi', BitVec.getLsbD_eq_getElem]
      · omega

theorem mulRow_congr {a a' b b' : Nat → Bool} {n : Nat}
    (ha : ∀ k, k < n → a k = a' k) (hb : ∀ k, k < n → b k = b' k) :
    ∀ k j, k < n → j < n → mulRow a b k j = mulRow a' b' k j
  | 0, j, hk, hj => by rw [mulRow_zero, mulRow_zero, ha j hj, hb 0 hk]
  | k + 1, j, hk, hj => by
    rw [mulRow_succ, mulRow_succ]
    by_cases hjk : j < k + 1
    · simp only [hjk, ↓reduceIte]
      exact mulRow_congr ha hb k j (by omega) hj
    · simp only [hjk, ↓reduceIte]
      apply addSum_congr (n := n - (k + 1))
      · intro i hi
        exact mulRow_congr ha hb k (k + 1 + i) (by omega) (by omega)
      · intro i hi
        rw [ha i (by omega), hb (k + 1) hk]
      · omega

/-- Replay lemma for `bv_bitblast_step_bvmult`. -/
theorem mul_eq_of_bits {w : Nat} (L R V : BitVec w) (a b : Nat → Bool)
    (ha : ∀ k, k < w → L.getLsbD k = a k) (hb : ∀ k, k < w → R.getLsbD k = b k)
    (hv : ∀ j, j < w → V.getLsbD j = mulRow a b (w - 1) j) : BitVec.mul L R = V := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [hv j hj]
  show (L * R).getLsbD j = _
  rw [BitVec.getLsbD_mul]
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  have hR : R.getLsbD (n + 1) = false := BitVec.getLsbD_of_ge R (n + 1) (Nat.le_refl _)
  have hlast : BitVec.mulRec L R (n + 1) = BitVec.mulRec L R n := by
    rw [BitVec.mulRec_succ_eq, hR]
    simp
  rw [hlast, ← mulRow_eq_mulRec L R n j hj, Nat.add_sub_cancel]
  exact mulRow_congr ha hb n j (by omega) hj

/-! ## Bit-vector equality -/

/-- Replay lemma for `bv_bitblast_step_bvequal`. -/
theorem eq_iff_of_bits {w : Nat} (A B : BitVec w) (a b : Nat → Bool)
    (ha : ∀ k, k < w → A.getLsbD k = a k) (hb : ∀ k, k < w → B.getLsbD k = b k)
    {C : Prop} (hC : C ↔ ∀ k, k < w → a k = b k) : (A = B) ↔ C := by
  rw [hC]
  constructor
  · intro h k hk
    rw [← ha k hk, ← hb k hk, h]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [ha k hk, hb k hk, h k hk]

/-! Conjunctions `c₀ ∧ (c₁ ∧ … cₙ₋₁)` as bounded `∀`. -/

theorem conj_last {c : Prop} {P : Nat → Prop} {i : Nat} (h : c ↔ P i) :
    c ↔ ∀ k, i ≤ k → k < i + 1 → P k := by
  rw [h]
  constructor
  · intro hp k hi hk
    have : k = i := by omega
    exact this ▸ hp
  · intro hall
    exact hall i (Nat.le_refl i) (Nat.lt_succ_self i)

theorem conj_cons {c R : Prop} {P : Nat → Prop} {i n : Nat} (h : c ↔ P i)
    (hR : R ↔ ∀ k, i + 1 ≤ k → k < n → P k) (hin : i < n) :
    (c ∧ R) ↔ ∀ k, i ≤ k → k < n → P k := by
  rw [h, hR]
  constructor
  · intro ⟨hp, hrest⟩ k hi hk
    by_cases e : k = i
    · exact e ▸ hp
    · exact hrest k (by omega) hk
  · intro hall
    exact ⟨hall i (Nat.le_refl i) hin, fun k hi hk => hall k (by omega) hk⟩

theorem conj_all {C : Prop} {P : Nat → Prop} {n : Nat}
    (h : C ↔ ∀ k, 0 ≤ k → k < n → P k) : C ↔ ∀ k, k < n → P k := by
  rw [h]
  exact ⟨fun hall k hk => hall k (Nat.zero_le k) hk, fun hall k _ hk => hall k hk⟩

/-! ## Bounded `∀`, for proofs at a concrete width -/

theorem forall_lt_zero (P : Nat → Prop) : ∀ k, k < 0 → P k :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem forall_lt_succ {P : Nat → Prop} {n : Nat} (h : ∀ k, k < n → P k) (hn : P n) :
    ∀ k, k < n + 1 → P k := fun k hk =>
  (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk)).elim (h k) (fun e => e ▸ hn)

/-! ## Decoded bits as `Bool` formulas: `P ↔ p = true` for a `Prop`, `t = p` for a `Bool` -/

theorem reify_true : True ↔ true = true := iff_of_true trivial rfl

theorem reify_false : False ↔ false = true := iff_of_false id Bool.false_ne_true

theorem reify_eq_true {t v : Bool} (h : t = v) : (t = true) ↔ (v = true) := by rw [h]

theorem reify_and {P Q : Prop} {p q : Bool} (hp : P ↔ p = true) (hq : Q ↔ q = true) :
    (P ∧ Q) ↔ (p && q) = true := by
  rw [hp, hq, Bool.and_eq_true]

theorem reify_or {P Q : Prop} {p q : Bool} (hp : P ↔ p = true) (hq : Q ↔ q = true) :
    (P ∨ Q) ↔ (p || q) = true := by
  rw [hp, hq, Bool.or_eq_true]

theorem reify_not {P : Prop} {p : Bool} (hp : P ↔ p = true) : ¬P ↔ (!p) = true := by
  rw [hp]; cases p <;> simp

theorem reify_xor {P Q : Prop} {p q : Bool} (hp : P ↔ p = true) (hq : Q ↔ q = true) :
    ¬(P ↔ Q) ↔ (p ^^ q) = true := by
  rw [hp, hq]; cases p <;> cases q <;> simp

theorem reify_iff {P Q : Prop} {p q : Bool} (hp : P ↔ p = true) (hq : Q ↔ q = true) :
    (P ↔ Q) ↔ (!(p ^^ q)) = true := by
  rw [hp, hq]; cases p <;> cases q <;> simp

theorem reify_iff_eq {P Q : Prop} {p q : Bool} (hp : P ↔ p = true) (hq : Q ↔ q = true) :
    (P ↔ Q) ↔ p = q := by
  rw [hp, hq]; cases p <;> cases q <;> simp

theorem reify_beq {s t s' t' : Bool} (hs : s = s') (ht : t = t') :
    (s = t) ↔ (s' = t') := by rw [hs, ht]

theorem reify_prop_atom (P : Prop) : P ↔ @decide P (Classical.propDecidable P) = true :=
  (@decide_eq_true_iff P (Classical.propDecidable P)).symm

theorem reify_decide {P : Prop} [Decidable P] {p : Bool} (hp : P ↔ p = true) :
    decide P = p := by
  cases p
  · exact decide_eq_false (fun h => Bool.false_ne_true (hp.mp h))
  · exact decide_eq_true (hp.mpr rfl)

theorem reify_bxor {s t s' t' : Bool} (hs : s = s') (ht : t = t') :
    (s ^^ t) = (s' ^^ t') := by rw [hs, ht]

theorem reify_band {s t s' t' : Bool} (hs : s = s') (ht : t = t') :
    (s && t) = (s' && t') := by rw [hs, ht]

theorem reify_bor {s t s' t' : Bool} (hs : s = s') (ht : t = t') :
    (s || t) = (s' || t') := by rw [hs, ht]

theorem reify_bnot {s s' : Bool} (hs : s = s') : (!s) = (!s') := by rw [hs]

/-! ## Operand bits, with explicit arguments for proof assembly -/

theorem getLsbD_ofBoolListLE' (bs : List Bool) (i : Nat) :
    (BitVec.ofBoolListLE bs).getLsbD i = bs.getD i false := BitVec.getLsbD_ofBoolListLE

theorem getLsbD_xor' {w : Nat} (x y : BitVec w) (i : Nat) :
    (BitVec.xor x y).getLsbD i = (x.getLsbD i ^^ y.getLsbD i) := BitVec.getLsbD_xor

theorem getLsbD_and' {w : Nat} (x y : BitVec w) (i : Nat) :
    (BitVec.and x y).getLsbD i = (x.getLsbD i && y.getLsbD i) := BitVec.getLsbD_and

theorem getLsbD_or' {w : Nat} (x y : BitVec w) (i : Nat) :
    (BitVec.or x y).getLsbD i = (x.getLsbD i || y.getLsbD i) := BitVec.getLsbD_or

theorem getLsbD_not' {w : Nat} (x : BitVec w) (i : Nat) (h : i < w) :
    (BitVec.not x).getLsbD i = !x.getLsbD i := by
  show (~~~x).getLsbD i = _
  simp [h]

end Crush.Alethe.BitBlast
