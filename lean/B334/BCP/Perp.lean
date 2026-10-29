import B334.BCP.Bit
import B334.BCP.PerpTab

/-! # `nperp v` is the mask of `{w : ⟨v, w⟩ = 1}` (the doubling lemma, then the table by a kernel check)

`nperpAux` doubles the mask: from the mask `N` of `{w < 2^k : parity(v &&& w) = 1}` it builds the mask for
`w < 2^(k+1)` as `N ||| ((N ^^^ [v_k]·(2^(2^k) - 1)) <<< 2^k)`, because for `w = 2^k + w'` (`w' < 2^k`) the parity
of `v &&& w` is that of `v &&& w'` plus `v_k`. Twelve steps give the 4096-bit masks of the checker:
`nperpD_bit`, `perpD_bit`. The checker reads tables (`nperp`, `perp`); `BCP/PerpTab` checks them equal to the
doubling definitions below 4096, which gives `nperp_bit` and `perp_bit`. -/

namespace B334.BCP

open B334.BC B334.BCT

theorem xorBits_succ (x k : Nat) : xorBits x (k + 1) = xor (xorBits x k) (x.testBit k) := rfl

theorem xorBits_congr (x y : Nat) : ∀ k, (∀ i < k, x.testBit i = y.testBit i) → xorBits x k = xorBits y k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [xorBits_succ, xorBits_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

/-- the invariant of the doubling loop: `N` is the indicator of `{w < 2^k : parity of the low k bits of v &&& w = 1}` -/
def NPInv (v k N : Nat) : Prop := ∀ w, N.testBit w = (decide (w < 2 ^ k) && xorBits (v &&& w) k)

theorem bit01 (v k : Nat) : Nat.land (Nat.shiftRight v k) 1 = if v.testBit k then 1 else 0 := by
  show (v >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with h | h
  · have : v.testBit k = false := by rw [Nat.testBit_eq_decide_div_mod_eq, h]; rfl
    rw [h, this]; rfl
  · have : v.testBit k = true := by rw [Nat.testBit_eq_decide_div_mod_eq, h]; rfl
    rw [h, this]; rfl

theorem npinv_step (v k N : Nat) (h : NPInv v k N) :
    NPInv v (k + 1) (Nat.lor N (Nat.shiftLeft (Nat.xor N (Nat.mul (Nat.land (Nat.shiftRight v k) 1)
      (Nat.pred (Nat.shiftLeft 1 (Nat.shiftLeft 1 k))))) (Nat.shiftLeft 1 k))) := by
  have e1 : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k
  have e2 : Nat.pred (Nat.shiftLeft 1 (Nat.shiftLeft 1 k)) = 2 ^ 2 ^ k - 1 := by
    rw [e1]; show (1 <<< 2 ^ k) - 1 = _; rw [Nat.one_shiftLeft]
  rw [e2, e1, bit01]
  intro w
  have hpk : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  -- the masked mask: bits below 2^k of N, flipped when v_k = 1
  have hY : ∀ i, (Nat.xor N ((if v.testBit k then 1 else 0) * (2 ^ 2 ^ k - 1))).testBit i =
      (decide (i < 2 ^ k) && xor (xorBits (v &&& i) k) (v.testBit k)) := by
    intro i
    show (N ^^^ ((if v.testBit k then 1 else 0) * (2 ^ 2 ^ k - 1))).testBit i = _
    rw [Nat.testBit_xor, h i]
    cases hv : v.testBit k
    · simp
    · simp only [if_true, Nat.one_mul, Nat.testBit_two_pow_sub_one]
      cases decide (i < 2 ^ k) <;> simp
  show (N ||| ((Nat.xor N ((if v.testBit k then 1 else 0) * (2 ^ 2 ^ k - 1))) <<< 2 ^ k)).testBit w = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, h w]
  by_cases hw : w < 2 ^ k
  · -- low half: only N contributes, and bit k of v &&& w is 0
    have hge : ¬ (w ≥ 2 ^ k) := by omega
    have hwk : w.testBit k = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (le_refl _))
    rw [xorBits_succ, Nat.testBit_and, hwk, Bool.and_false, Bool.xor_false]
    simp [hw, hge, show w < 2 ^ (k + 1) by omega]
  · by_cases hw2 : w < 2 ^ (k + 1)
    · -- high half: w = 2^k + w'
      set w' := w - 2 ^ k with hw'
      have hw'lt : w' < 2 ^ k := by omega
      have hweq : w = 2 ^ k + w' := by omega
      have hlow : ∀ i < k, (v &&& w).testBit i = (v &&& w').testBit i := by
        intro i hi
        rw [Nat.testBit_and, Nat.testBit_and, hweq, Nat.testBit_two_pow_add_gt hi]
      have hk : (v &&& w).testBit k = v.testBit k := by
        rw [Nat.testBit_and, hweq, Nat.testBit_two_pow_add_eq,
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hw'lt (le_refl _))]
        simp
      rw [xorBits_succ, xorBits_congr _ _ k hlow, hk, hY w']
      simp [hw, show w ≥ 2 ^ k by omega, hw2, hw'lt]
    · -- above: nothing
      have hY0 : (Nat.xor N ((if v.testBit k then 1 else 0) * (2 ^ 2 ^ k - 1))).testBit (w - 2 ^ k) = false := by
        rw [hY]; simp [show ¬ (w - 2 ^ k < 2 ^ k) by omega]
      rw [hY0]
      simp [hw, hw2]

theorem npinv_aux (v : Nat) : ∀ fuel k N, NPInv v k N → NPInv v (k + fuel) (nperpAux v fuel k N) := by
  intro fuel
  induction fuel with
  | zero => intro k N h; exact h
  | succ fuel ih =>
    intro k N h
    have e : nperpAux v (fuel + 1) k N = nperpAux v fuel (Nat.succ k)
        (Nat.lor N (Nat.shiftLeft (Nat.xor N (Nat.mul (Nat.land (Nat.shiftRight v k) 1)
          (Nat.pred (Nat.shiftLeft 1 (Nat.shiftLeft 1 k))))) (Nat.shiftLeft 1 k))) := rfl
    rw [e, show k + (fuel + 1) = Nat.succ k + fuel by omega]
    exact ih _ _ (npinv_step v k N h)

theorem npinv_zero (v : Nat) : NPInv v 0 0 := by
  intro w; rw [Nat.zero_testBit]
  show false = (decide (w < 2 ^ 0) && false)
  rw [Bool.and_false]

/-- **The doubling definition.** `nperpD v` has bit `w` iff `⟨v, w⟩ = 1` (`w < 4096`) -/
theorem nperpD_bit (v w : Nat) (hw : w < 4096) : (nperpD v).testBit w = par12 (v &&& w) := by
  have h := npinv_aux v 12 0 0 (npinv_zero v) w
  rw [show (0 : Nat) + 12 = 12 by rfl] at h
  show (nperpAux v 12 0 0).testBit w = xorBits (v &&& w) 12
  rw [h]; simp [hw]

theorem nperpD_lt (v : Nat) : nperpD v < 2 ^ 4096 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have h := npinv_aux v 12 0 0 (npinv_zero v) i
  rw [show (0 : Nat) + 12 = 12 by rfl] at h
  show (nperpAux v 12 0 0).testBit i = false
  have hi' : ¬ i < 4096 := by omega
  rw [h]; simp [hi']

/-- `perpD v` has bit `w` iff `⟨v, w⟩ = 0` (`w < 4096`) -/
theorem perpD_bit (v w : Nat) (hw : w < 4096) : (perpD v).testBit w = !par12 (v &&& w) := by
  show (M4096 ^^^ nperpD v).testBit w = _
  rw [Nat.testBit_xor, m4096_eq, Nat.testBit_two_pow_sub_one, nperpD_bit v w hw]
  simp [hw]

/-- the checker's table `nperp` (equal to `nperpD` below 4096, `nperp_eq`) -/
theorem nperp_bit (v w : Nat) (hv : v < 4096) (hw : w < 4096) : (nperp v).testBit w = par12 (v &&& w) := by
  rw [nperp_eq v hv]; exact nperpD_bit v w hw

/-- the checker's table `perp` (equal to `perpD` below 4096, `perp_eq`) -/
theorem perp_bit (v w : Nat) (hv : v < 4096) (hw : w < 4096) : (perp v).testBit w = !par12 (v &&& w) := by
  rw [perp_eq v hv]; exact perpD_bit v w hw

end B334.BCP
