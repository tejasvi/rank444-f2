import B334.BCP.Base

/-! # Bit-level lemmas: sparse products, constant masks, the lowest set bit

Port of `S5/Bit.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to the 24-bit slots of BranchCheck334:
twelve slots of 24 bits (12 data bits, then the identity half), constants `REP24`, `LEFT12`, `ID24`, `HM12`, `REPR24`,
`RH12`, `C23`; 4096-bit masks (`ALLNZ`, `M4096`); the 9-bit hit-table constants `C31`, `M32B`, `M32` are unchanged.
`mkB`, `mkB_bit`, `mkB_lt` are `B334.Core`'s. -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core

/-- **Sparse product.** If `m` has bits only at multiples of `w` and `v < 2^w`, the copies `v · 2^(w k)` do not
overlap: bit `i` of `m * v` is bit `i mod w` of `v` when bit `w ⌊i/w⌋` of `m` is set. -/
theorem testBit_sparse_mul {w : Nat} (hw : 0 < w) (m : Nat) : ∀ (v : Nat), v < 2 ^ w →
    (∀ i, m.testBit i = true → i % w = 0) →
    ∀ i, (m * v).testBit i = (m.testBit (w * (i / w)) && v.testBit (i % w)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro v hv hm i
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  have hr2 : m % 2 ^ w < 2 := by
    have : m % 2 ^ w < 2 ^ 1 := by
      apply Nat.lt_pow_two_of_testBit
      intro j hj
      rw [Nat.testBit_mod_two_pow]
      cases hjm : m.testBit j
      · simp
      · have := hm j hjm
        by_cases hjw : j < w
        · rw [Nat.mod_eq_of_lt hjw] at this; omega
        · simp [hjw]
    simpa using this
  have hb0 : (m % 2 ^ w).testBit 0 = m.testBit 0 := by
    rw [Nat.testBit_mod_two_pow]; simp [hw]
  have hr0 : m % 2 ^ w = (m.testBit 0).toNat := by
    rcases (by omega : m % 2 ^ w = 0 ∨ m % 2 ^ w = 1) with h | h
    · rw [h] at hb0 ⊢; rw [← hb0]; rfl
    · rw [h] at hb0 ⊢; rw [← hb0]; rfl
  have hrv : m % 2 ^ w * v < 2 ^ w := by
    rcases (by omega : m % 2 ^ w = 0 ∨ m % 2 ^ w = 1) with h | h
    · rw [h, Nat.zero_mul]; exact Nat.two_pow_pos w
    · rw [h, Nat.one_mul]; exact hv
  have hmv : m * v = 2 ^ w * (m / 2 ^ w * v) + m % 2 ^ w * v := by
    have := Nat.div_add_mod m (2 ^ w)
    calc m * v = (2 ^ w * (m / 2 ^ w) + m % 2 ^ w) * v := by rw [this]
      _ = 2 ^ w * (m / 2 ^ w * v) + m % 2 ^ w * v := by ring
  rw [hmv, Nat.testBit_two_pow_mul_add (m / 2 ^ w * v) hrv i]
  by_cases hiw : i < w
  · simp only [hiw, if_true]
    rw [Nat.div_eq_of_lt hiw, Nat.mod_eq_of_lt hiw, Nat.mul_zero, hr0]
    cases m.testBit 0 <;> simp
  · simp only [hiw, if_false]
    have h12 : 1 < 2 ^ w :=
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
    have hqm : m / 2 ^ w < m := Nat.div_lt_self hpos h12
    have hqs : ∀ j, (m / 2 ^ w).testBit j = true → j % w = 0 := by
      intro j hj
      rw [Nat.testBit_div_two_pow] at hj
      have := hm _ hj
      rwa [Nat.add_mod_right] at this
    rw [ih _ hqm v hv hqs (i - w)]
    obtain ⟨k, rfl⟩ : ∃ k, i = k + w := ⟨i - w, by omega⟩
    rw [Nat.add_sub_cancel, Nat.testBit_div_two_pow, Nat.add_div_right k hw, Nat.add_mod_right, Nat.mul_add,
      Nat.mul_one]

/-- a constant's bits from a kernel check below `2^N` -/
theorem testBit_const {K N : Nat} (f : Nat → Bool) (hK : K < 2 ^ N)
    (hlow : allLT N (fun i => K.testBit i == f i) = true) (hhigh : ∀ i, N ≤ i → f i = false) :
    ∀ i, K.testBit i = f i := by
  intro i
  by_cases hi : i < N
  · have := allLT_spec hlow i hi
    simpa using this
  · rw [hhigh i (by omega), Nat.testBit_lt_two_pow (lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem rep24_bit : ∀ i, REP24.testBit i = decide (i % 24 = 0 ∧ i < 288) :=
  testBit_const (N := 288) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem left12_bit : ∀ i, LEFT12.testBit i = decide (i % 24 < 12 ∧ i < 288) :=
  testBit_const (N := 288) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem id24_bit : ∀ i, ID24.testBit i = decide (i < 288 ∧ 12 ≤ i % 24 ∧ i % 24 - 12 = i / 24) :=
  testBit_const (N := 288) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem hm12_bit : ∀ i, HM12.testBit i = decide (i < 288 ∧ i % 24 < 12 ∧ i / 24 < i % 24) :=
  testBit_const (N := 288) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem allnz_bit : ∀ i, ALLNZ.testBit i = decide (0 < i ∧ i < 4096) :=
  testBit_const (N := 4096) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem c23_bit : ∀ i, C23.testBit i = decide (i % 23 = 0 ∧ i < 276) :=
  testBit_const (N := 276) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem c31_bit : ∀ i, C31.testBit i = decide (i % 31 = 0 ∧ i < 279) :=
  testBit_const (N := 279) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem m32b_bit : ∀ i, M32B.testBit i = decide (i % 32 = 0 ∧ i < 288) :=
  testBit_const (N := 288) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem repr24_bit : ∀ i, REPR24.testBit i = decide (i % 24 = 12 ∧ i < 288) :=
  testBit_const (N := 288) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)
theorem rh12_bit : ∀ i, RH12.testBit i = decide (12 ≤ i ∧ i < 24) :=
  testBit_const (N := 24) _ (by decide +kernel) (by decide +kernel) (by intro i hi; simp; omega)

theorem m24_eq : M24 = 2 ^ 24 - 1 := by decide +kernel
theorem m288_eq : M288 = 2 ^ 288 - 1 := by decide +kernel
theorem m512_eq : M512 = 2 ^ 512 - 1 := by decide +kernel
theorem m32_eq : M32 = 2 ^ 32 - 1 := by decide +kernel
theorem m4096_eq : M4096 = 2 ^ 4096 - 1 := by decide +kernel

theorem rep24_sparse : ∀ i, REP24.testBit i = true → i % 24 = 0 := by
  intro i h; rw [rep24_bit] at h; simp at h; omega

/-- `spr24 c = ∑_{z ∈ c} 2^(24z)` -/
theorem spr24_bit (c : Nat) (hc : c < 4096) (i : Nat) :
    (spr24 c).testBit i = (decide (i % 24 = 0 ∧ i < 288) && c.testBit (i / 24)) := by
  show (c * C23 &&& REP24).testBit i = _
  rw [Nat.testBit_and, Nat.mul_comm, testBit_sparse_mul (w := 23) (by norm_num) C23 c (by omega)
    (fun j hj => by rw [c23_bit] at hj; simp at hj; omega) i, c23_bit, rep24_bit]
  by_cases h : i % 24 = 0 ∧ i < 288
  · have e1 : i % 23 = i / 24 := by omega
    have e2 : 23 * (i / 23) % 23 = 0 ∧ 23 * (i / 23) < 276 := by omega
    simp [h, e1, e2]
  · simp [h]

theorem spr24_sparse (c : Nat) (hc : c < 4096) : ∀ i, (spr24 c).testBit i = true → i % 24 = 0 := by
  intro i h; rw [spr24_bit c hc] at h; simp at h; omega

/-- `dep32 x = ∑_{i ∈ x} 2^(32i)` -/
theorem dep32_bit (x : Nat) (hx : x < 512) (i : Nat) :
    (dep32 x).testBit i = (decide (i % 32 = 0 ∧ i < 288) && x.testBit (i / 32)) := by
  show (x * C31 &&& M32B).testBit i = _
  rw [Nat.testBit_and, Nat.mul_comm, testBit_sparse_mul (w := 31) (by norm_num) C31 x (by omega)
    (fun j hj => by rw [c31_bit] at hj; simp at hj; omega) i, c31_bit, m32b_bit]
  by_cases h : i % 32 = 0 ∧ i < 288
  · have e1 : i % 31 = i / 32 := by omega
    have e2 : 31 * (i / 31) % 31 = 0 ∧ 31 * (i / 31) < 279 := by omega
    simp [h, e1, e2]
  · simp [h]

theorem low_bit_exists {m : Nat} (hm : m ≠ 0) : ∃ k, m.testBit k = true ∧ ∀ i < k, m.testBit i = false := by
  have hex : ∃ i, m.testBit i = true := by
    by_contra hne
    apply hm
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    cases e : m.testBit i
    · rfl
    · exact absurd ⟨i, e⟩ hne
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_⟩
  have := Nat.find_min hex hi
  simpa using this

/-- **Lowest set bit.** `m &&& (m - 1)` clears it and `m ^^^ (m &&& (m - 1))` is it (333 `lowbit_spec`). -/
theorem low_bit_spec {m k : Nat} (hk : m.testBit k = true) (hlow : ∀ i < k, m.testBit i = false) :
    (∀ i, (m &&& (m - 1)).testBit i = (m.testBit i && decide (i ≠ k))) ∧ m ^^^ (m &&& (m - 1)) = 2 ^ k := by
  have hmod : m % 2 ^ (k + 1) = 2 ^ k := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    rcases lt_trichotomy i k with h | h | h
    · rw [hlow i h]; simp; omega
    · subst h; simp [hk]
    · have h1 : ¬ i < k + 1 := by omega
      have h2 : k ≠ i := by omega
      simp [h1, h2]
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdec : m = 2 ^ (k + 1) * (m / 2 ^ (k + 1)) + 2 ^ k := by
    have := Nat.div_add_mod m (2 ^ (k + 1)); rw [hmod] at this; omega
  have hm1 : m - 1 = 2 ^ (k + 1) * (m / 2 ^ (k + 1)) + (2 ^ k - 1) := by omega
  have hlt1 : 2 ^ k - 1 < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have hlt2 : 2 ^ k < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have bm1 : ∀ i, (m - 1).testBit i =
      if i < k + 1 then decide (i < k) else (m / 2 ^ (k + 1)).testBit (i - (k + 1)) := by
    intro i; rw [hm1, Nat.testBit_two_pow_mul_add _ hlt1, Nat.testBit_two_pow_sub_one]
  have bm : ∀ i, m.testBit i =
      if i < k + 1 then decide (k = i) else (m / 2 ^ (k + 1)).testBit (i - (k + 1)) := by
    intro i; conv_lhs => rw [hdec]
    rw [Nat.testBit_two_pow_mul_add _ hlt2, Nat.testBit_two_pow]
  have h1 : ∀ i, (m &&& (m - 1)).testBit i = (m.testBit i && decide (i ≠ k)) := by
    intro i; rw [Nat.testBit_and, bm1 i, bm i]
    rcases lt_trichotomy i k with h | h | h
    · have h' : k ≠ i := by omega
      simp [show i < k + 1 by omega, h']
    · subst h; simp
    · have h' : ¬ i < k + 1 := by omega
      have h'' : i ≠ k := by omega
      simp [h', h'']
  refine ⟨h1, ?_⟩
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, h1 i, Nat.testBit_two_pow]
  by_cases h : i = k
  · subst h; simp [hk]
  · have h' : k ≠ i := fun e => h e.symm
    cases m.testBit i <;> simp [h, h']

theorem lt_of_land_mask {x k : Nat} : x &&& (2 ^ k - 1) < 2 ^ k := by
  rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos k)

end B334.BCP
