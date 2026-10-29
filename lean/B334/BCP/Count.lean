import B334.BCP.Bit
import B334.BCP.Sem

/-! # Hit counts: `par`, `hx`, `pop32`, `ucnt`, the packed hit table `mkSSP`

Port of the counting parts of `S5/Masks.lean`, `S5/Sem.lean` and `S5/Facts.lean` (⟨3,3,3⟩ release `rank333-f2`,
Apache-2.0). First factors and functionals stay 9-bit, so the code (`par`, `dep32`, `hx`, `pop32`, `ucnt`, `mkSSP`) and
the proofs are the 333 ones; only `rank_sum_le` moves to 12×12 matrices. Also `pair_par`: the pairing `X(a)` of
`B334.Core` is the checker's `par (a &&& X)`. -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core Matrix

/-- number of set bits among `0 … k-1` -/
def cntB (x k : Nat) : Nat := @Nat.rec (fun _ => Nat) 0 (fun i ih => ih + (x.testBit i).toNat) k

theorem par_fact : allLT 512 (fun v => par v == xorBits v 9) = true := by decide +kernel
theorem pop11_fact : allLT 2048 (fun x => pop11 x == cntB x 11) = true := by decide +kernel

theorem bf_false : bf false = 0 := rfl
theorem bf_true : bf true = 1 := rfl

theorem par_eq (v : Nat) (hv : v < 512) : par v = xorBits v 9 := by
  have := allLT_spec par_fact v hv; simpa using this

theorem bf_xorBits (v k : Nat) : bf (xorBits v k) = ∑ i ∈ Finset.range k, bf (v.testBit i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show bf (xor (xorBits v k) (v.testBit k)) = _
    rw [bf_xor, ih, Finset.sum_range_succ]

theorem bf_inj {a b : Bool} (h : bf a = bf b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem testBit_M32 (j : Nat) : M32.testBit j = decide (j < 32) := by
  rw [m32_eq, Nat.testBit_two_pow_sub_one]

theorem depM32_bit (X i : Nat) (hX : X < 512) :
    (dep32 X * M32).testBit i = (decide (i < 288) && X.testBit (i / 32)) := by
  have hs : ∀ j, (dep32 X).testBit j = true → j % 32 = 0 := by
    intro j hj; rw [dep32_bit X hX] at hj; simp at hj; omega
  rw [testBit_sparse_mul (by norm_num) _ M32 (by rw [m32_eq]; omega) hs, dep32_bit X hX, testBit_M32]
  have e1 : 32 * (i / 32) % 32 = 0 := by omega
  have e2 : (32 * (i / 32) < 288) ↔ i < 288 := by omega
  have e3 : 32 * (i / 32) / 32 = i / 32 := by omega
  have e4 : i % 32 < 32 := by omega
  simp [e1, e2, e3, e4]

theorem hx_bf (SS X s : Nat) (hX : X < 512) (hs : s < 32) :
    bf ((hx SS X).testBit s) = ∑ k ∈ Finset.range 9, bf (X.testBit k) * bf (SS.testBit (32 * k + s)) := by
  unfold hx
  simp only [Nat.land_eq, Nat.xor_eq, Nat.shiftRight_eq', Nat.mul_eq, Nat.testBit_and, Nat.testBit_xor,
    Nat.testBit_shiftRight, testBit_M32, depM32_bit X _ hX]
  interval_cases s <;> simp [Finset.sum_range_succ, bf_xor, bf_and, bf_false, bf_true] <;> ring

theorem hx_lt (SS X : Nat) : hx SS X < 2 ^ 32 := by
  show Nat.land _ M32 < 2 ^ 32
  rw [m32_eq]; exact Nat.and_lt_two_pow _ (by omega)

theorem pop11_eq (x : Nat) (hx : x < 2048) : pop11 x = cntB x 11 := by
  have := allLT_spec pop11_fact x hx; simpa using this

theorem cntB_congr (x y k : Nat) (h : ∀ i, i < k → x.testBit i = y.testBit i) : cntB x k = cntB y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show cntB x k + (x.testBit k).toNat = cntB y k + (y.testBit k).toNat
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem cntB_split (x a b : Nat) : cntB x (a + b) = cntB x a + cntB (x >>> a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show cntB x (a + b) + (x.testBit (a + b)).toNat = cntB x a + (cntB (x >>> a) b + ((x >>> a).testBit b).toNat)
    rw [ih, Nat.testBit_shiftRight]; omega

theorem pop32_eq (x : Nat) (hx : x < 2 ^ 32) : pop32 x = cntB x 32 := by
  show pop11 (x &&& 2047) + (pop11 ((x >>> 11) &&& 2047) + pop11 (x >>> 22)) = cntB x 32
  have h2047 : (2047 : Nat) = 2 ^ 11 - 1 := by norm_num
  have hlt : ∀ y, y &&& 2047 < 2048 := fun y => lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have h22 : x >>> 22 < 2048 := by
    rw [Nat.shiftRight_eq_div_pow]; apply Nat.div_lt_of_lt_mul; norm_num at hx ⊢; omega
  rw [pop11_eq _ (hlt x), pop11_eq _ (hlt _), pop11_eq _ h22]
  have c1 : cntB (x &&& 2047) 11 = cntB x 11 := cntB_congr _ _ _ (fun i hi => by
    rw [Nat.testBit_and, h2047, Nat.testBit_two_pow_sub_one]; simp [hi])
  have c2 : cntB ((x >>> 11) &&& 2047) 11 = cntB (x >>> 11) 11 := cntB_congr _ _ _ (fun i hi => by
    rw [Nat.testBit_and, h2047, Nat.testBit_two_pow_sub_one]; simp [hi])
  have c3 : cntB (x >>> 22) 11 = cntB (x >>> 22) 10 := by
    show cntB (x >>> 22) 10 + ((x >>> 22).testBit 10).toNat = _
    rw [Nat.testBit_shiftRight, Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (by norm_num))]; rfl
  have e : x >>> 11 >>> 11 = x >>> 22 := by rw [← Nat.shiftRight_add]
  rw [c1, c2, c3, show (32 : Nat) = 11 + (11 + 10) by norm_num, cntB_split, cntB_split, e]

theorem cntB_sum (x k : Nat) : cntB x k = ∑ i ∈ Finset.range k, (x.testBit i).toNat := by
  induction k with
  | zero => rfl
  | succ k ih => show cntB x k + _ = _; rw [ih, Finset.sum_range_succ]

theorem cntB_card (x k : Nat) : cntB x k = ((Finset.range k).filter (fun i => x.testBit i = true)).card := by
  rw [cntB_sum, Finset.card_filter]
  apply Finset.sum_congr rfl; intro i _; cases x.testBit i <;> rfl

/-- `bf` of the 9-bit parity of `a &&& X` is the sum of the products of the bits -/
theorem bf_par_and (a X : Nat) (ha : a < 512) :
    bf (par (a &&& X)) = ∑ k ∈ Finset.range 9, bf (a.testBit k) * bf (X.testBit k) := by
  rw [par_eq _ (lt_of_le_of_lt Nat.and_le_left ha), bf_xorBits]
  apply Finset.sum_congr rfl; intro k _
  rw [Nat.testBit_and, bf_and]

theorem mkSSP_bit (T k s : Nat) (hk : k < 9) (hs : s < 32) : ∀ n, n ≤ 32 →
    (mkSSP T n).testBit (32 * k + s) = (decide (s < n) && (aT T s).testBit k) := by
  intro n
  induction n with
  | zero => intro _; simp [mkSSP]
  | succ n ih =>
    intro hn
    show (mkSSP T n ||| (dep32 (aT T n) <<< n)).testBit (32 * k + s) = _
    rw [Nat.testBit_or, ih (by omega), Nat.testBit_shiftLeft, dep32_bit _ (aT_lt T n)]
    by_cases e : s = n
    · subst e
      have e0 : 32 * k + s - s = 32 * k := by omega
      have e1 : 32 * k % 32 = 0 ∧ 32 * k < 288 := by omega
      have e2 : 32 * k / 32 = k := by omega
      rw [e0, e2, decide_eq_true e1]
      simp
    · have e1 : ¬ (32 * k + s ≥ n ∧ (32 * k + s - n) % 32 = 0 ∧ 32 * k + s - n < 288) := by omega
      have e3 : (s < n + 1) ↔ s < n := by omega
      by_cases e2 : 32 * k + s ≥ n
      · have e4 : ¬ ((32 * k + s - n) % 32 = 0 ∧ 32 * k + s - n < 288) := fun x => e1 ⟨e2, x⟩
        simp [e2, e3, e4]
      · simp [e2, e3]

/-- `SS` holds bit `k` of first factor `s` at bit `32k + s` (for the `n` terms) -/
def SSok (T n SS : Nat) : Prop :=
  ∀ k s, k < 9 → s < 32 → SS.testBit (32 * k + s) = (decide (s < n) && (aT T s).testBit k)

theorem mkSSP_ok (T n : Nat) (hn : n ≤ 32) : SSok T n (mkSSP T n) :=
  fun k s hk hs => mkSSP_bit T k s hk hs n hn

theorem hx_SS (T n X s SS : Nat) (hSS : SSok T n SS) (hX : X < 512) (hs : s < 32) :
    (hx SS X).testBit s = (decide (s < n) && par (aT T s &&& X)) := by
  apply bf_inj
  rw [hx_bf _ X s hX hs]
  rw [Finset.sum_congr rfl (fun k hk => by rw [hSS k s (Finset.mem_range.mp hk) hs])]
  by_cases hsn : s < n
  · simp only [hsn, decide_true, Bool.true_and]
    rw [bf_par_and _ X (aT_lt T s)]
    apply Finset.sum_congr rfl; intro k _; ring
  · simp [hsn, bf]

theorem ucnt_eq' (T n ACT X SS : Nat) (hSS : SSok T n SS) (hn : n ≤ 32) (hX : X < 512)
    (hact : ∀ t, ACT.testBit t = true → t < n) : ucnt SS ACT X = (hitS T n ACT X).card := by
  show pop32 (hx SS X &&& ACT) = _
  rw [pop32_eq _ (lt_of_le_of_lt Nat.and_le_left (hx_lt _ _)), cntB_card]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_and, hitS, Bool.and_eq_true]
  constructor
  · rintro ⟨hs, h1, h2⟩
    rw [hx_SS T n X s SS hSS hX hs] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨h1.1, h2, h1.2⟩
  · rintro ⟨hs, h2, h1⟩
    refine ⟨by omega, ?_, h2⟩
    rw [hx_SS T n X s SS hSS hX (by omega)]
    simp [hs, h1]

theorem ucnt_eq (T n ACT X : Nat) (hn : n ≤ 32) (hX : X < 512) (hact : ∀ t, ACT.testBit t = true → t < n) :
    ucnt (mkSSP T n) ACT X = (hitS T n ACT X).card :=
  ucnt_eq' T n ACT X _ (mkSSP_ok T n hn) hn hX hact

theorem rank_sum_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (β γ : ι → Fin 12 → F2) :
    (∑ s ∈ S, vecMulVec (β s) (γ s)).rank ≤ S.card := by
  rw [sum_vecMulVec_eq]
  calc (facB S β * (facB S γ)ᵀ).rank ≤ (facB S β).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card ↥S := Matrix.rank_le_card_width _
    _ = S.card := Fintype.card_coe _

/-- the pairing `X(a)` (`B334.Core.pair`) is the checker's 9-bit parity -/
theorem pair_par (X a : Nat) (hX : X < 512) (ha : a < 512) : pair (toM3 X) (toM3 a) = bf (par (a &&& X)) := by
  rw [bf_par_and a X ha]
  simp only [pair, toM3, Fin.sum_univ_three, Finset.sum_range_succ, Finset.sum_range_zero, bitF_bf]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

end B334.BCP
