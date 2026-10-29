import B334.BCP.Sem
import B334.Core.Sym334
import B334.Tables.SymFacts

/-! # The GL₄ pair step

Port of `S5/Sym.lean` and `S7/Corb.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0), without the rank bookkeeping
of Lemma G (dropped in v5c-334). `(a, b, c) ↦ (a, b S, S⁻¹ c)` for `S ∈ GL₄(F₂)` fixes every first factor and maps
decompositions of `T(X)` to decompositions (`sym_sum334`), so at the root one may assume, for the term branched
first, `b_t ∈ ORBM` (`wb_exists`) and then, by an element of `Stab(b_t)`, `c_t ∈ CORB[b_t]` (`wc_exists`,
by the witness tables `WC`). Both moves keep every factor nonzero: `sym_move`, `sym_transform334`. -/

namespace B334.BCP

open B334.Core B334.BC B334.Tab Matrix

theorem nv_eq_vecB (b : Nat) : nv b = vecB (toM34 b) := by funext y; rw [vecB_toM34]; rfl
theorem nv_eq_vecC (c : Nat) : nv c = vecC (toM43 c) := by funext z; rw [vecC_toM43]; rfl
theorem vm_eq (b c : Nat) : vecMulVec (nv b) (nv c) = vecMulVec (vecB (toM34 b)) (vecC (toM43 c)) := by
  rw [nv_eq_vecB, nv_eq_vecC]

theorem mulBS_lt (b S : Nat) : mulBS b S < 4096 := lt_of_lt_of_eq (mkB_lt _ 12) (by norm_num)
theorem mulSC_lt (S c : Nat) : mulSC S c < 4096 := lt_of_lt_of_eq (mkB_lt _ 12) (by norm_num)

theorem lt4096_bit (v j : Nat) (hv : v < 4096) (hj : 12 ≤ j) : v.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))

theorem eq_zero_of_toM34 (v : Nat) (hv : v < 4096) (h : toM34 v = 0) : v = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < 12
  · have := congrFun (congrFun h ⟨i / 4, by omega⟩) ⟨i % 4, by omega⟩
    simp only [toM34, bitF, Matrix.zero_apply] at this
    rw [show 4 * (i / 4) + i % 4 = i by omega] at this
    cases e : v.testBit i
    · rfl
    · rw [e] at this; exact absurd this (by decide)
  · exact lt4096_bit v i hv (by omega)

theorem eq_zero_of_toM43 (v : Nat) (hv : v < 4096) (h : toM43 v = 0) : v = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < 12
  · have := congrFun (congrFun h ⟨i / 3, by omega⟩) ⟨i % 3, by omega⟩
    simp only [toM43, bitF, Matrix.zero_apply] at this
    rw [show 3 * (i / 3) + i % 3 = i by omega] at this
    cases e : v.testBit i
    · rfl
    · rw [e] at this; exact absurd this (by decide)
  · exact lt4096_bit v i hv (by omega)

theorem toM34_zero : toM34 0 = 0 := by ext i j; simp [toM34, bitF]
theorem toM43_zero : toM43 0 = 0 := by ext i j; simp [toM43, bitF]

/-- one GL₄ move `(b, c) ↦ (b S, S⁻¹ c)` keeps nonzero factors and the root residual identity -/
theorem sym_move {T n dom ACT : Nat} {b c : Nat → Nat} (hbc : BC n b c) (hd : HD T n dom b c ACT []) (S Si : Nat)
    (hinv : toM44 Si * toM44 S = 1) :
    BC n (fun u => mulBS (b u) S) (fun u => mulSC Si (c u)) ∧
      HD T n dom (fun u => mulBS (b u) S) (fun u => mulSC Si (c u)) ACT [] := by
  have hSS' : toM44 S * toM44 Si = 1 := mul_eq_one_comm.mp hinv
  refine ⟨fun u hu => ?_, fun X hX hdom => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hbc u hu
    refine ⟨Nat.pos_of_ne_zero (fun e => ?_), mulBS_lt _ _, Nat.pos_of_ne_zero (fun e => ?_), mulSC_lt _ _⟩
    · have h0 : toM34 (b u) * toM44 S = 0 := by rw [← toM34_mulBS]; simp only at e; rw [e, toM34_zero]
      have : toM34 (b u) = 0 := by
        rw [← Matrix.mul_one (toM34 (b u)), ← hSS', ← Matrix.mul_assoc, h0, Matrix.zero_mul]
      have := eq_zero_of_toM34 _ h2 this; omega
    · have h0 : toM44 Si * toM43 (c u) = 0 := by rw [← toM43_mulSC]; simp only at e; rw [e, toM43_zero]
      have : toM43 (c u) = 0 := by
        rw [← Matrix.one_mul (toM43 (c u)), ← hSS', Matrix.mul_assoc, h0, Matrix.mul_zero]
      have := eq_zero_of_toM43 _ h4 this; omega
  · have h := hd X hX hdom
    rw [resM_nil] at h ⊢
    simp only [vm_eq] at h ⊢
    simp only [toM34_mulBS, toM43_mulSC]
    exact sym_sum334 (toM3 X) _ (fun u => toM34 (b u)) (fun u => toM43 (c u)) (toM44 S) (toM44 Si) hinv h

/-- **GL₄ pair step.** At the root, any decomposition can be moved so that `b_t ∈ ORBM` and
`c_t ∈ CORB[b_t]`, keeping every factor nonzero and the residual identity. -/
theorem sym_transform334 {T n dom ACT : Nat} {b c : Nat → Nat} (hbc : BC n b c) (hd : HD T n dom b c ACT []) (t : Nat)
    (ht : t < n) : ∃ b' c' : Nat → Nat, BC n b' c' ∧ HD T n dom b' c' ACT [] ∧ b' t ∈ ORBL ∧
      (CORB (b' t)).testBit (c' t) = true := by
  obtain ⟨hb0, hbl, _, _⟩ := hbc t ht
  obtain ⟨S1, Si1, hinv1, horb⟩ := wb_exists (b t) hbl (Nat.pos_iff_ne_zero.mp hb0)
  obtain ⟨hbc1, hd1⟩ := sym_move hbc hd S1 Si1 hinv1
  obtain ⟨_, _, hc10, hc1l⟩ := hbc1 t ht
  obtain ⟨S2, Si2, hinv2, hfix, hcorb⟩ :=
    wc_exists (mulBS (b t) S1) horb (mulSC Si1 (c t)) hc1l (Nat.pos_iff_ne_zero.mp hc10)
  obtain ⟨hbc2, hd2⟩ := sym_move hbc1 hd1 S2 Si2 hinv2
  refine ⟨_, _, hbc2, hd2, ?_, ?_⟩
  · show mulBS (mulBS (b t) S1) S2 ∈ ORBL
    rw [hfix]; exact horb
  · show (CORB (mulBS (mulBS (b t) S1) S2)).testBit (mulSC Si2 (mulSC Si1 (c t))) = true
    rw [hfix]; exact hcorb

end B334.BCP
