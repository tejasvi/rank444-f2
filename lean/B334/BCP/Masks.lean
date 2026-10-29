import B334.BCP.Elim
import B334.BCP.Perp

/-! # Bit semantics of the checker's masks and folds: `gather`, `lmC`, `kerM`, `xof`, `gof`, the 12-bit duality

Port of `S5/Masks.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to BranchCheck334: 24-bit
slots, 12 pivots, 4096-bit masks (`perp_bit` from `BCP/Perp`), and the 12-bit duality `par12`. -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core Matrix

theorem bf_par12 (u v : Nat) : bf (par12 (u &&& v)) = ∑ i ∈ Finset.range 12, bf (u.testBit i) * bf (v.testBit i) := by
  show bf (xorBits (u &&& v) 12) = _
  rw [bf_xorBits]
  apply Finset.sum_congr rfl; intro i _
  rw [Nat.testBit_and, bf_and]

/-- the 12-bit duality as a dot product -/
theorem dot_nv12 (u v : Nat) : nv u ⬝ᵥ nv v = bf (par12 (u &&& v)) := by
  rw [bf_par12, ← Fin.sum_univ_eq_sum_range (fun i => bf (u.testBit i) * bf (v.testBit i))]
  simp only [dotProduct, nv, bitF_bf]

theorem par12_comm (u v : Nat) : par12 (u &&& v) = par12 (v &&& u) := by rw [Nat.and_comm]

theorem testBit_4095 (j : Nat) : Nat.testBit 4095 j = decide (j < 12) := by
  rw [show (4095 : Nat) = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one]

/-! ## `gather`, `lmC`, `kerM` -/

/-- `gather` without the shift -/
def gcore (x : Nat) : Nat := Nat.land (Nat.shiftRight (Nat.mul x MAGIC24) 253) 4095

theorem gather_eq (P j : Nat) : gather P j = gcore ((P >>> j) &&& REP24) := rfl

theorem gcore_fact : allLT 4096 (fun k => gcore (spr24 k) == k) = true := by decide +kernel

theorem gather_spec (P j : Nat) : gather P j = mkB (fun h => P.testBit (24 * h + j)) 12 := by
  rw [gather_eq]
  have hlt : mkB (fun h => P.testBit (24 * h + j)) 12 < 4096 :=
    lt_of_lt_of_eq (mkB_lt _ 12) (by norm_num)
  have e : (P >>> j) &&& REP24 = spr24 (mkB (fun h => P.testBit (24 * h + j)) 12) := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [cand_bit, spr24_bit _ hlt, mkB_bit]
    by_cases h : i % 24 = 0 ∧ i < 288
    · have e1 : j + i = 24 * (i / 24) + j := by omega
      have e2 : i / 24 < 12 := by omega
      simp [h, e1, e2]
    · simp [h]
  rw [e]
  have := allLT_spec gcore_fact _ hlt
  simpa using this

theorem gather_bit (P j h : Nat) : (gather P j).testBit h = (decide (h < 12) && P.testBit (24 * h + j)) := by
  rw [gather_spec, mkB_bit]

theorem gather_lt (P j : Nat) : gather P j < 4096 := by
  rw [gather_spec]; exact lt_of_lt_of_eq (mkB_lt _ 12) (by norm_num)

theorem lmC_mem (P PM w : Nat) (hw : w < 4096)
    (h : ∀ j, j < 12 → PM.testBit j = false → par12 ((gather P j ||| 2 ^ j) &&& w) = false) :
    (lmC P PM).testBit w = true := by
  have key : ∀ k, k ≤ 12 → ∀ acc, acc.testBit w = true → (lmCAux P PM k acc).testBit w = true := by
    intro k
    induction k with
    | zero => intro _ acc hacc; exact hacc
    | succ k ih =>
      intro hk acc hacc
      show Nat.testBit (lmCAux P PM k (cond (bit PM k) acc
        (Nat.land acc (perp (Nat.lor (gather P k) (Nat.shiftLeft 1 k)))))) w = true
      apply ih (by omega)
      rw [bit_eq]
      cases hb : PM.testBit k
      · show (acc &&& perp (gather P k ||| 1 <<< k)).testBit w = true
        have hlt : gather P k ||| 2 ^ k < 4096 := by
          have h1 : gather P k < 2 ^ 12 := lt_of_lt_of_eq (gather_lt P k) (by norm_num)
          have h2 : 2 ^ k < 2 ^ 12 := Nat.pow_lt_pow_right (by norm_num) (by omega)
          have := Nat.or_lt_two_pow h1 h2
          simpa using this
        rw [Nat.testBit_and, hacc, Nat.one_shiftLeft, perp_bit _ w hlt hw, h k (by omega) hb]; rfl
      · exact hacc
  exact key 12 le_rfl M4096 (by rw [m4096_eq, Nat.testBit_two_pow_sub_one]; simpa using hw)

theorem rgt_lt (M z : Nat) : ((M >>> (24 * z)) &&& M24) >>> 12 < 4096 := by
  rw [Nat.shiftRight_eq_div_pow]
  have := land_m24_lt (M >>> (24 * z))
  apply Nat.div_lt_of_lt_mul; norm_num at this ⊢; omega

theorem kerM_mem (M w : Nat) (hw : w < 4096)
    (h : ∀ z, z < 12 → par12 ((((M >>> (24 * z)) &&& M24) >>> 12) &&& w) = false) : (kerM M).testBit w = true := by
  have key : ∀ k, k ≤ 12 → ∀ acc, acc.testBit w = true → (kerMAux M k acc).testBit w = true := by
    intro k
    induction k with
    | zero => intro _ acc hacc; exact hacc
    | succ k ih =>
      intro hk acc hacc
      show (kerMAux M k (cond (Nat.beq (Nat.land (Nat.shiftRight M (Nat.mul 24 k)) M24) 0) acc
        (Nat.land acc (perp (Nat.shiftRight (Nat.land (Nat.shiftRight M (Nat.mul 24 k)) M24) 12))))).testBit w = true
      apply ih (by omega)
      cases Nat.beq (Nat.land (Nat.shiftRight M (Nat.mul 24 k)) M24) 0
      · show (acc &&& perp (((M >>> (24 * k)) &&& M24) >>> 12)).testBit w = true
        rw [Nat.testBit_and, hacc, perp_bit _ w (rgt_lt M k) hw, h k (by omega)]; rfl
      · exact hacc
  exact key 12 le_rfl M4096 (by rw [m4096_eq, Nat.testBit_two_pow_sub_one]; simpa using hw)

theorem rgt_bit (M z j : Nat) (hj : j < 12) :
    (((M >>> (24 * z)) &&& M24) >>> 12).testBit j = M.testBit (24 * z + (12 + j)) := by
  rw [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_shiftRight, m24_eq, Nat.testBit_two_pow_sub_one]
  simp [show 12 + j < 24 by omega]

/-! ## The folds `xof`, `gof` -/

theorem sprRH_bit (b i : Nat) (hb : b < 4096) :
    (spr24 b * RH12).testBit i = (decide (12 ≤ i % 24 ∧ i < 288) && b.testBit (i / 24)) := by
  rw [testBit_sparse_mul (by norm_num) _ RH12 (by decide) (spr24_sparse b hb), spr24_bit b hb, rh12_bit]
  have e1 : 24 * (i / 24) % 24 = 0 := by omega
  have e2 : (24 * (i / 24) < 288) ↔ i < 288 := by omega
  have e3 : 24 * (i / 24) / 24 = i / 24 := by omega
  have e4 : i % 24 < 24 := by omega
  simp only [e1, e2, e3, e4, true_and, and_true]
  by_cases h1 : 12 ≤ i % 24 <;> by_cases h2 : i < 288 <;> simp [h1, h2]

theorem xof_bf (P b j : Nat) (hb : b < 4096) (hj : j < 12) :
    bf ((xof P b).testBit j) = ∑ h ∈ Finset.range 12, bf (b.testBit h) * bf (P.testBit (24 * h + (12 + j))) := by
  unfold xof
  simp only [Nat.land_eq, Nat.xor_eq, Nat.shiftRight_eq', Nat.mul_eq, Nat.testBit_and, Nat.testBit_xor,
    Nat.testBit_shiftRight, testBit_4095, sprRH_bit b _ hb]
  interval_cases j <;> simp [Finset.sum_range_succ, bf_xor, bf_and, bf_false, bf_true] <;> ring

theorem xof_lt (P b : Nat) : xof P b < 4096 := by
  show Nat.land _ 4095 < 4096
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem cREPR_bit (c i : Nat) (hc : c < 4096) :
    (c * REPR24).testBit i = (decide (12 ≤ i % 24 ∧ i < 288) && c.testBit (i % 24 - 12)) := by
  have e : c * REPR24 = REP24 * (c * 2 ^ 12) := by
    rw [show REPR24 = REP24 * 2 ^ 12 by decide +kernel]; ring
  rw [e, testBit_sparse_mul (by norm_num) _ _ (by omega) rep24_sparse, rep24_bit, Nat.testBit_mul_two_pow]
  have e1 : 24 * (i / 24) % 24 = 0 := by omega
  have e2 : (24 * (i / 24) < 288) ↔ i < 288 := by omega
  simp only [e1, e2, true_and]
  cases c.testBit (i % 24 - 12) <;> by_cases h1 : 12 ≤ i % 24 <;> simp [h1]

theorem gof_bf (P c h : Nat) (hc : c < 4096) (hh : h < 12) :
    bf ((gof P c).testBit h) = ∑ j ∈ Finset.range 12, bf (c.testBit j) * bf (P.testBit (24 * h + (12 + j))) := by
  unfold gof
  rw [gather_bit]
  simp only [Nat.land_eq, Nat.xor_eq, Nat.shiftRight_eq', Nat.mul_eq, Nat.testBit_and, Nat.testBit_xor,
    Nat.testBit_shiftRight, cREPR_bit c _ hc]
  interval_cases h <;> simp [Finset.sum_range_succ, bf_xor, bf_and, bf_false, bf_true] <;> ring

theorem gof_lt (P c : Nat) : gof P c < 4096 := gather_lt _ _

/-- `b · g(c) = c · x(b)` -/
theorem par_gof_xof (P bb cc : Nat) (hb : bb < 4096) (hc : cc < 4096) :
    par12 (bb &&& gof P cc) = par12 (cc &&& xof P bb) := by
  apply bf_inj
  rw [bf_par12, bf_par12]
  have hg : ∀ h ∈ Finset.range 12, bf (bb.testBit h) * bf ((gof P cc).testBit h) =
      ∑ j ∈ Finset.range 12, bf (bb.testBit h) * (bf (cc.testBit j) * bf (P.testBit (24 * h + (12 + j)))) := by
    intro h hh; rw [gof_bf P cc h hc (Finset.mem_range.mp hh), Finset.mul_sum]
  have hx : ∀ j ∈ Finset.range 12, bf (cc.testBit j) * bf ((xof P bb).testBit j) =
      ∑ h ∈ Finset.range 12, bf (cc.testBit j) * (bf (bb.testBit h) * bf (P.testBit (24 * h + (12 + j)))) := by
    intro j hj; rw [xof_bf P bb j hb (Finset.mem_range.mp hj), Finset.mul_sum]
  rw [Finset.sum_congr rfl hg, Finset.sum_congr rfl hx, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro h _; ring

end B334.BCP
