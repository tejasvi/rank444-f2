import B334.Core.Sym334

/-! # Bit encodings for the pair symmetry: 4×4 matrices, `b·S` and `S⁻¹·c` on masks

Encodings:
- a 4×4 matrix `S` is a 16-bit number, entry `(r, c)` = bit `4r+c` (`toM44`); the identity is `33825 = 0x8421`;
- a second factor `b` (3×4) is a 12-bit number, entry `(j, k)` = bit `4j+k` (`toM34`);
- a third factor `c` (4×3) is a 12-bit number, entry `(k, i)` = bit `3k+i` (`toM43`).

`mul44 u v`, `mulBS b S` and `mulSC S c` compute `u v`, `b S` and `S c` on masks; `toM44_mul44`, `toM34_mulBS` and
`toM43_mulSC` say they are the matrix products. The bit helpers `bitF`, `bf`, `mkB`, `mkB_bit` and `allLT` are ported
from the ⟨3,3,3⟩ release (`RootSound/Bits.lean`, `S5/Elim.lean`, `S5/Base.lean`, `S5/Bit.lean`; Apache-2.0). -/

open Matrix

namespace B334.Core

/-- bit `i` of `v` as an element of `F2` -/
def bitF (v i : Nat) : F2 := if v.testBit i then 1 else 0
/-- a Boolean as an element of `F2` -/
def bf (b : Bool) : F2 := if b then 1 else 0
theorem bitF_bf (v i : Nat) : bitF v i = bf (v.testBit i) := rfl
theorem bf_xor (a b : Bool) : bf (xor a b) = bf a + bf b := by cases a <;> cases b <;> decide
theorem bf_and (a b : Bool) : bf (a && b) = bf a * bf b := by cases a <;> cases b <;> decide

/-- the number with bits `f 0, …, f (k-1)` -/
def mkB (f : Nat → Bool) (k : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun i ih => ih ||| (bif f i then 2 ^ i else 0)) k

theorem mkB_bit (f : Nat → Bool) (k i : Nat) : (mkB f k).testBit i = (decide (i < k) && f i) := by
  induction k with
  | zero => simp [mkB]
  | succ k ih =>
    show (mkB f k ||| (bif f k then 2 ^ k else 0)).testBit i = _
    rw [Nat.testBit_or, ih]
    cases hf : f k
    · simp only [cond_false, Nat.zero_testBit, Bool.or_false]
      by_cases hik : i = k
      · subst hik; simp [hf]
      · have : (i < k + 1) ↔ i < k := by omega
        simp [this]
    · simp only [cond_true, Nat.testBit_two_pow]
      by_cases hik : i = k
      · subst hik; simp [hf]
      · have : (i < k + 1) ↔ i < k := by omega
        have h2 : k ≠ i := fun e => hik e.symm
        simp [this, h2]

theorem mkB_lt (f : Nat → Bool) (k : Nat) : mkB f k < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi; rw [mkB_bit]; simp; omega

/-- `f i` for all `i < n`, as one recursor loop (cheap for the kernel) -/
def allLT (n : Nat) (f : Nat → Bool) : Bool := @Nat.rec (fun _ => Bool) true (fun k ih => f k && ih) n

theorem allLT_spec {n : Nat} {f : Nat → Bool} (h : allLT n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi
    have h' : (f k && allLT k f) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih h'.2 i hlt
    · subst heq; exact h'.1

/-- parity of four bits -/
def x4 (f : Nat → Bool) : Bool := xor (xor (xor (f 0) (f 1)) (f 2)) (f 3)

/-- `u v` for 4×4 matrices (entry `(r, c)` at bit `4r+c`) -/
def mul44 (u v : Nat) : Nat := mkB (fun p => x4 (fun l => u.testBit (4 * (p / 4) + l) && v.testBit (4 * l + p % 4))) 16
/-- `b S` for a 3×4 matrix `b` (bit `4j+k`) and a 4×4 matrix `S` -/
def mulBS (b S : Nat) : Nat := mkB (fun p => x4 (fun l => b.testBit (4 * (p / 4) + l) && S.testBit (4 * l + p % 4))) 12
/-- `S c` for a 4×4 matrix `S` and a 4×3 matrix `c` (bit `3k+i`) -/
def mulSC (S c : Nat) : Nat := mkB (fun p => x4 (fun l => S.testBit (4 * (p / 3) + l) && c.testBit (3 * l + p % 3))) 12

def toM44 (u : Nat) : Matrix (Fin 4) (Fin 4) F2 := fun r c => bitF u (4 * r.val + c.val)
def toM34 (b : Nat) : M34 := fun j k => bitF b (4 * j.val + k.val)
def toM43 (c : Nat) : M43 := fun k i => bitF c (3 * k.val + i.val)

theorem bitF_mul44 (u v p : Nat) (hp : p < 16) :
    bitF (mul44 u v) p = ∑ l : Fin 4, bitF u (4 * (p / 4) + l.val) * bitF v (4 * l.val + p % 4) := by
  rw [bitF_bf, mul44, mkB_bit]
  simp only [hp, decide_true, Bool.true_and, x4, bf_xor, bf_and, Fin.sum_univ_four, bitF_bf]
  simp

theorem bitF_mulBS (b S p : Nat) (hp : p < 12) :
    bitF (mulBS b S) p = ∑ l : Fin 4, bitF b (4 * (p / 4) + l.val) * bitF S (4 * l.val + p % 4) := by
  rw [bitF_bf, mulBS, mkB_bit]
  simp only [hp, decide_true, Bool.true_and, x4, bf_xor, bf_and, Fin.sum_univ_four, bitF_bf]
  simp

theorem bitF_mulSC (S c p : Nat) (hp : p < 12) :
    bitF (mulSC S c) p = ∑ l : Fin 4, bitF S (4 * (p / 3) + l.val) * bitF c (3 * l.val + p % 3) := by
  rw [bitF_bf, mulSC, mkB_bit]
  simp only [hp, decide_true, Bool.true_and, x4, bf_xor, bf_and, Fin.sum_univ_four, bitF_bf]
  simp

theorem toM44_mul44 (u v : Nat) : toM44 (mul44 u v) = toM44 u * toM44 v := by
  ext i j
  simp only [toM44, Matrix.mul_apply]
  rw [bitF_mul44 u v _ (by omega)]
  have e1 : (4 * i.val + j.val) / 4 = i.val := by omega
  have e2 : (4 * i.val + j.val) % 4 = j.val := by omega
  rw [e1, e2]

theorem toM34_mulBS (b S : Nat) : toM34 (mulBS b S) = toM34 b * toM44 S := by
  ext j k
  simp only [toM34, toM44, Matrix.mul_apply]
  rw [bitF_mulBS b S _ (by omega)]
  have e1 : (4 * j.val + k.val) / 4 = j.val := by omega
  have e2 : (4 * j.val + k.val) % 4 = k.val := by omega
  rw [e1, e2]

theorem toM43_mulSC (S c : Nat) : toM43 (mulSC S c) = toM44 S * toM43 c := by
  ext k i
  simp only [toM43, toM44, Matrix.mul_apply]
  rw [bitF_mulSC S c _ (by omega)]
  have e1 : (3 * k.val + i.val) / 3 = k.val := by omega
  have e2 : (3 * k.val + i.val) % 3 = i.val := by omega
  rw [e1, e2]

/-- the identity matrix is `0x8421` -/
theorem toM44_one : toM44 33825 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- `vecB (toM34 b)` is the bit vector of `b` -/
theorem vecB_toM34 (b : Nat) (y : Fin 12) : vecB (toM34 b) y = bitF b y.val := by
  simp only [vecB, toM34, hiB, loB]
  congr 1; omega

/-- `vecC (toM43 c)` is the bit vector of `c` -/
theorem vecC_toM43 (c : Nat) (z : Fin 12) : vecC (toM43 c) z = bitF c z.val := by
  simp only [vecC, toM43, hiC, loC]
  congr 1; omega

/-- a mask table entry with `mul44 S Si = 0x8421` gives an inverse pair, in the order `sym_sum334` needs -/
theorem inv_of_mul44 {S Si : Nat} (h : mul44 S Si = 33825) : toM44 Si * toM44 S = 1 := by
  have h1 : toM44 S * toM44 Si = 1 := by rw [← toM44_mul44, h, toM44_one]
  exact Matrix.mul_eq_one_comm.mp h1

end B334.Core
