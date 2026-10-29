import B334.BCP.ElimLA
import B334.BCP.Sym

/-! # The packed residuals: `resC`/`resR` pack `R(X)` with the identity half

Port of the packed part of `S5/Sem.lean` and of `S5/FactsTX.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to
BranchCheck334. `txc24 X` holds `T(X)` by columns (slot `z` = column `z`: bit `24z + y` = entry `(y, z)`), `txr24 X`
by rows; both facts are kernel checks over all 512 `X`. `resC X asg` is the column-packed `R(X)` with the identity in
the right halves (`resC_sem`), `resR` the row-packed one (`resR_sem`), and with no assigned term hit by `X` they are
the root tables (`noasg_spec`). -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core Matrix

/-- bit `i = 24z + y` of `txc24 X`: entry `(y, z)` of `T(X)` -/
def txcSpec (X i : Nat) : Bool :=
  decide (i % 24 < 12) && decide (i % 24 % 4 = i / 24 / 3) && X.testBit (3 * (i / 24 % 3) + i % 24 / 4)
/-- bit `i = 24y + z` of `txr24 X`: entry `(y, z)` of `T(X)` -/
def txrSpec (X i : Nat) : Bool :=
  decide (i % 24 < 12) && decide (i / 24 % 4 = i % 24 / 3) && X.testBit (3 * (i % 24 % 3) + i / 24 / 4)

theorem txc_fact : allLT 512 (fun X => allLT 288 (fun i => (txc24 X).testBit i == txcSpec X i)) = true := by
  decide +kernel
theorem txr_fact : allLT 512 (fun X => allLT 288 (fun i => (txr24 X).testBit i == txrSpec X i)) = true := by
  decide +kernel

theorem txc_bit (X i : Nat) (hX : X < 512) (hi : i < 288) : (txc24 X).testBit i = txcSpec X i := by
  have := allLT_spec (allLT_spec txc_fact X hX) i hi; simpa using this
theorem txr_bit (X i : Nat) (hX : X < 512) (hi : i < 288) : (txr24 X).testBit i = txrSpec X i := by
  have := allLT_spec (allLT_spec txr_fact X hX) i hi; simpa using this

theorem tx_entry (X y z : Nat) (hy : y < 12) (hz : z < 12) :
    bf (decide (y % 4 = z / 3) && X.testBit (3 * (z % 3) + y / 4)) =
      TX (toM3 X) ⟨y, hy⟩ ⟨z, hz⟩ := by
  unfold TX
  have e : (loB ⟨y, hy⟩ = hiC ⟨z, hz⟩) ↔ y % 4 = z / 3 := by
    simp only [loB, hiC, Fin.ext_iff]
  by_cases h : y % 4 = z / 3
  · rw [if_pos (e.mpr h)]; simp [h, toM3, bitF, loC, hiB, bf]
  · rw [if_neg (fun x => h (e.mp x))]; simp [h, bf]

/-- the right halves of a packed residual are the identity -/
theorem id24_right (z j : Nat) (hz : z < 12) (hj : j < 12) : ID24.testBit (24 * z + (12 + j)) = decide (j = z) := by
  rw [id24_bit]
  have e1 : (24 * z + (12 + j)) % 24 = 12 + j := by omega
  have e2 : (24 * z + (12 + j)) / 24 = z := by omega
  rw [e1, e2, decide_eq_decide]
  omega

theorem id24_left (z y : Nat) (hy : y < 12) : ID24.testBit (24 * z + y) = false := by
  rw [id24_bit]; simp only [decide_eq_false_iff_not]; omega

theorem term_left (b c z y : Nat) (hb : b < 4096) (hc : c < 4096) (hy : y < 24) :
    (spr24 c * b).testBit (24 * z + y) = (decide (z < 12) && c.testBit z && b.testBit y) := by
  rw [sparse24_slot (spr24_sparse c hc) (by omega) z y hy, spr24_bit c hc]
  have e : (24 * z % 24 = 0 ∧ 24 * z < 288) ↔ z < 12 := by omega
  rw [show 24 * z / 24 = z by omega]; simp only [e]

theorem resC_nil (X : Nat) (hX : X < 512) : amat (resC X []) = resM X [] ∧ RightId (resC X []) := by
  constructor
  · funext y z
    show bitF (Nat.xor (txc24 X) ID24) (24 * z.val + y.val) =
      (TX (toM3 X) + ([] : List (Matrix (Fin 12) (Fin 12) F2)).sum) y z
    rw [List.sum_nil, add_zero, bitF_bf, show Nat.xor (txc24 X) ID24 = txc24 X ^^^ ID24 from rfl, Nat.testBit_xor,
      txc_bit X _ hX (by omega), id24_left _ _ y.isLt, Bool.xor_false, txcSpec,
      ← tx_entry X y.val z.val y.isLt z.isLt]
    have e1 : (24 * z.val + y.val) % 24 = y.val := by omega
    have e2 : (24 * z.val + y.val) / 24 = z.val := by omega
    rw [e1, e2]; simp [y.isLt]
  · intro z j hz hj
    show (Nat.xor (txc24 X) ID24).testBit _ = _
    have hf : txcSpec X (24 * z + (12 + j)) = false := by
      unfold txcSpec
      rw [decide_eq_false (by omega : ¬ ((24 * z + (12 + j)) % 24 < 12))]
      rfl
    rw [show Nat.xor (txc24 X) ID24 = txc24 X ^^^ ID24 from rfl, Nat.testBit_xor, txc_bit X _ hX (by omega),
      id24_right z j hz hj, hf, Bool.false_xor]

theorem resC_step (X : Nat) (asg : Asg) (e : Nat × Nat × Nat) (hb : e.2.1 < 4096) (hc : e.2.2 < 4096)
    (ih1 : amat (resC X asg) = resM X asg) (ih2 : RightId (resC X asg)) :
    amat (spr24 e.2.2 * e.2.1 ^^^ resC X asg) = resM X asg + vecMulVec (nv e.2.1) (nv e.2.2) ∧
      RightId (spr24 e.2.2 * e.2.1 ^^^ resC X asg) := by
  constructor
  · funext y z
    rw [← ih1]
    show bitF (spr24 e.2.2 * e.2.1 ^^^ resC X asg) (24 * z.val + y.val) =
      bitF (resC X asg) (24 * z.val + y.val) + nv e.2.1 y * nv e.2.2 z
    rw [bitF_bf, bitF_bf, Nat.testBit_xor, term_left _ _ _ _ hb hc (by omega), bf_xor]
    simp only [z.isLt, decide_true, Bool.true_and, bf_and, nv, bitF_bf]
    ring
  · intro z j hz hj
    rw [Nat.testBit_xor, term_left _ _ _ _ hb hc (by omega), lt4096_bit _ _ hb (by omega), ih2 z j hz hj]
    simp

/-- `resC X asg` packs `R(X)` by columns -/
theorem resC_sem (X : Nat) (hX : X < 512) : ∀ asg : Asg, (∀ e ∈ asg, e.2.1 < 4096 ∧ e.2.2 < 4096) →
    amat (resC X asg) = resM X asg ∧ RightId (resC X asg) := by
  intro asg
  induction asg with
  | nil => intro _; exact resC_nil X hX
  | cons e asg ih =>
    intro hasg
    obtain ⟨ih1, ih2⟩ := ih (fun e' he' => hasg e' (List.mem_cons_of_mem _ he'))
    obtain ⟨hb, hc⟩ := hasg e List.mem_cons_self
    have hR : resC X (e :: asg) = cond (par (e.1 &&& X)) ((spr24 e.2.2 * e.2.1) ^^^ resC X asg) (resC X asg) := rfl
    rw [hR, resM_cons]
    cases hp : par (e.1 &&& X)
    · rw [cond_false, if_neg (by decide), add_zero]
      exact ⟨ih1, ih2⟩
    · rw [cond_true, if_pos rfl]
      exact resC_step X asg e hb hc ih1 ih2

theorem resR_nil (X : Nat) (hX : X < 512) : amat (resR X []) = (resM X [])ᵀ ∧ RightId (resR X []) := by
  constructor
  · funext z y
    show bitF (Nat.xor (txr24 X) ID24) (24 * y.val + z.val) =
      (TX (toM3 X) + ([] : List (Matrix (Fin 12) (Fin 12) F2)).sum) y z
    rw [List.sum_nil, add_zero, bitF_bf, show Nat.xor (txr24 X) ID24 = txr24 X ^^^ ID24 from rfl, Nat.testBit_xor,
      txr_bit X _ hX (by omega), id24_left _ _ z.isLt, Bool.xor_false, txrSpec,
      ← tx_entry X y.val z.val y.isLt z.isLt]
    have e1 : (24 * y.val + z.val) % 24 = z.val := by omega
    have e2 : (24 * y.val + z.val) / 24 = y.val := by omega
    rw [e1, e2]; simp [z.isLt]
  · intro z j hz hj
    show (Nat.xor (txr24 X) ID24).testBit _ = _
    have hf : txrSpec X (24 * z + (12 + j)) = false := by
      unfold txrSpec
      rw [decide_eq_false (by omega : ¬ ((24 * z + (12 + j)) % 24 < 12))]
      rfl
    rw [show Nat.xor (txr24 X) ID24 = txr24 X ^^^ ID24 from rfl, Nat.testBit_xor, txr_bit X _ hX (by omega),
      id24_right z j hz hj, hf, Bool.false_xor]

theorem resR_step (X : Nat) (asg : Asg) (e : Nat × Nat × Nat) (hb : e.2.1 < 4096) (hc : e.2.2 < 4096)
    (ih1 : amat (resR X asg) = (resM X asg)ᵀ) (ih2 : RightId (resR X asg)) :
    amat (spr24 e.2.1 * e.2.2 ^^^ resR X asg) = (resM X asg + vecMulVec (nv e.2.1) (nv e.2.2))ᵀ ∧
      RightId (spr24 e.2.1 * e.2.2 ^^^ resR X asg) := by
  constructor
  · funext z y
    rw [Matrix.transpose_add, Matrix.add_apply, ← ih1]
    show bitF (spr24 e.2.1 * e.2.2 ^^^ resR X asg) (24 * y.val + z.val) =
      bitF (resR X asg) (24 * y.val + z.val) + nv e.2.1 y * nv e.2.2 z
    rw [bitF_bf, bitF_bf, Nat.testBit_xor, term_left _ _ _ _ hc hb (by omega), bf_xor]
    simp only [y.isLt, decide_true, Bool.true_and, bf_and, nv, bitF_bf]
    ring
  · intro z j hz hj
    rw [Nat.testBit_xor, term_left _ _ _ _ hc hb (by omega), lt4096_bit _ _ hc (by omega), ih2 z j hz hj]
    simp

/-- `resR X asg` packs `R(X)` by rows -/
theorem resR_sem (X : Nat) (hX : X < 512) : ∀ asg : Asg, (∀ e ∈ asg, e.2.1 < 4096 ∧ e.2.2 < 4096) →
    amat (resR X asg) = (resM X asg)ᵀ ∧ RightId (resR X asg) := by
  intro asg
  induction asg with
  | nil => intro _; exact resR_nil X hX
  | cons e asg ih =>
    intro hasg
    obtain ⟨ih1, ih2⟩ := ih (fun e' he' => hasg e' (List.mem_cons_of_mem _ he'))
    obtain ⟨hb, hc⟩ := hasg e List.mem_cons_self
    have hR : resR X (e :: asg) = cond (par (e.1 &&& X)) ((spr24 e.2.1 * e.2.2) ^^^ resR X asg) (resR X asg) := rfl
    rw [hR, resM_cons]
    cases hp : par (e.1 &&& X)
    · rw [cond_false, if_neg (by decide), add_zero]
      exact ⟨ih1, ih2⟩
    · rw [cond_true, if_pos rfl]
      exact resR_step X asg e hb hc ih1 ih2

theorem noasg_spec (X : Nat) : ∀ asg : Asg, noasg X asg = true →
    resC X asg = Nat.xor (txc24 X) ID24 ∧ resR X asg = Nat.xor (txr24 X) ID24 ∧ resM X asg = TX (toM3 X) := by
  intro asg
  induction asg with
  | nil => intro _; exact ⟨rfl, rfl, by simp [resM]⟩
  | cons e asg ih =>
    intro h
    have h' : (!(par (Nat.land e.1 X)) && noasg X asg) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨h1, h2, h3⟩ := ih h'.2
    have hp : par (e.1 &&& X) = false := by
      have := h'.1; revert this; cases par (Nat.land e.1 X) <;> simp
    refine ⟨?_, ?_, ?_⟩
    · show cond (par (e.1 &&& X)) _ (resC X asg) = _; rw [hp, cond_false]; exact h1
    · show cond (par (e.1 &&& X)) _ (resR X asg) = _; rw [hp, cond_false]; exact h2
    · rw [resM_cons, hp, h3, if_neg (by decide), add_zero]

end B334.BCP
