import B334.MethodK.Flat
import B334.MethodK.Quot
import B334.Core.SymBits

/-! # Method K: the certificate layer

* masks as vectors and matrices over `ZMod 2` (`mvec`, `mmat`) and the parity form of their products (`dotMV`);
* the witness check K-W on packed masks (`kwOK`) and its meaning (`kw_right`, `kw_left`);
* K-F1 (`linIndep_of_inv`), K-π (`ker_of_basis`);
* the flattenings as linear maps, and the per-row assembly `rowValid_of_K`: from K-π, K-U, K-F1, K-M, K-W and K-L to
  `RowValid basis lb`. -/

namespace B334.MethodK

open Finset Matrix

/-! ## Masks -/

/-- a Boolean in `ZMod 2` -/
def zb (b : Bool) : ZMod 2 := if b then 1 else 0
/-- bit `i` of `v` in `ZMod 2` -/
def zbit (v i : ℕ) : ZMod 2 := zb (v.testBit i)

theorem zb_xor (a b : Bool) : zb (xor a b) = zb a + zb b := by cases a <;> cases b <;> decide
theorem zb_and (a b : Bool) : zb (a && b) = zb a * zb b := by cases a <;> cases b <;> decide
theorem zb_true : zb true = 1 := rfl
theorem zb_false : zb false = 0 := rfl
theorem zmod2_cases' : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- XOR of `g 0, …, g (n-1)` (one recursor loop) -/
def xorFold (n : ℕ) (g : ℕ → Bool) : Bool := @Nat.rec (fun _ => Bool) false (fun i ih => xor ih (g i)) n

theorem zb_xorFold (n : ℕ) (g : ℕ → Bool) : zb (xorFold n g) = ∑ i ∈ Finset.range n, zb (g i) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show zb (xor (xorFold k g) (g k)) = _
    rw [zb_xor, ih, Finset.sum_range_succ]

/-- a mask as a vector of length `w` -/
def mvec (w v : ℕ) : Fin w → ZMod 2 := fun j => zbit v j.val
/-- row masks as an `nR × w` matrix -/
def mmat (nR w : ℕ) (rows : ℕ → ℕ) : Matrix (Fin nR) (Fin w) (ZMod 2) := fun r j => zbit (rows r.val) j.val

theorem dot_mvec (w u v : ℕ) : mvec w u ⬝ᵥ mvec w v = zb (xorFold w (fun j => (u &&& v).testBit j)) := by
  rw [zb_xorFold, ← Fin.sum_univ_eq_sum_range (fun j => zb ((u &&& v).testBit j))]
  simp only [dotProduct, mvec, zbit, Nat.testBit_and, zb_and]

/-- the XOR of the rows `rows r` (`r < nR`) selected by the bits of `u` -/
def xorRows (u : ℕ) (rows : ℕ → ℕ) (nR : ℕ) : ℕ :=
  @Nat.rec (fun _ => ℕ) 0 (fun r acc => acc ^^^ (bif u.testBit r then rows r else 0)) nR

theorem testBit_xorRows (u : ℕ) (rows : ℕ → ℕ) (nR j : ℕ) :
    zb ((xorRows u rows nR).testBit j) = ∑ r ∈ Finset.range nR, zb (u.testBit r) * zb ((rows r).testBit j) := by
  induction nR with
  | zero => simp [xorRows, zb]
  | succ k ih =>
    show zb ((xorRows u rows k ^^^ (bif u.testBit k then rows k else 0)).testBit j) = _
    rw [Nat.testBit_xor, zb_xor, ih, Finset.sum_range_succ]
    cases u.testBit k <;> simp [zb]

/-- `u ⬝ (M v)`: the parity of `(the XOR of the rows selected by u) &&& v` (one parity per product, so the kernel
evaluates `nR + w` terms instead of `nR · w`; leanK2 measured the old row-by-row form above 8 GB per chunk) -/
def dotMV (u v : ℕ) (rows : ℕ → ℕ) (nR w : ℕ) : Bool :=
  xorFold w (fun j => (xorRows u rows nR &&& v).testBit j)

theorem zb_dotMV (u v : ℕ) (rows : ℕ → ℕ) (nR w : ℕ) :
    zb (dotMV u v rows nR w) = mvec nR u ⬝ᵥ (mmat nR w rows).mulVec (mvec w v) := by
  rw [dotMV, zb_xorFold, ← Fin.sum_univ_eq_sum_range (fun j => zb ((xorRows u rows nR &&& v).testBit j))]
  simp only [dotProduct, Matrix.mulVec, mvec, mmat, zbit, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.testBit_and, zb_and, testBit_xorRows, Finset.sum_mul,
    ← Fin.sum_univ_eq_sum_range (fun r => zb (u.testBit r) * zb ((rows r).testBit j) * zb (v.testBit j))]
  exact Finset.sum_congr rfl (fun r _ => by ring)

/-- the mask of a vector -/
def maskOf {w : ℕ} (z : Fin w → ZMod 2) : ℕ :=
  B334.Core.mkB (fun j => if h : j < w then decide (z ⟨j, h⟩ = 1) else false) w

theorem mvec_maskOf {w : ℕ} (z : Fin w → ZMod 2) : mvec w (maskOf z) = z := by
  funext j
  simp only [mvec, zbit, maskOf, B334.Core.mkB_bit, j.isLt, decide_true, Bool.true_and, dif_pos, Fin.eta]
  rcases zmod2_cases' (z j) with h | h <;> simp [h, zb]

theorem maskOf_lt {w : ℕ} (z : Fin w → ZMod 2) : maskOf z < 2 ^ w := B334.Core.mkB_lt _ w

theorem maskOf_ne_zero {w : ℕ} (z : Fin w → ZMod 2) (hz : z ≠ 0) : maskOf z ≠ 0 := by
  intro h
  apply hz
  rw [← mvec_maskOf z, h]
  funext j; simp [mvec, zbit, zb]

/-! ## K-W -/

/-- the witness check: for every nonzero mask `z < 2 ^ need`, the witness `Y z` satisfies L-K5's two conditions
against `M0` and every `N m` (`m < nm`). Right form: `u = Y z` (rows), `v = z` (columns); left form: `u = z`, `v = Y z`. -/
def kwOK (M0 : ℕ → ℕ) (N : ℕ → ℕ → ℕ) (nm : ℕ) (Y : ℕ → ℕ) (nR nC need : ℕ) (right : Bool) : Bool :=
  B334.Core.allLT (2 ^ need) (fun z => z == 0 ||
    ((if right then dotMV (Y z) z M0 nR nC else dotMV z (Y z) M0 nR nC) &&
     B334.Core.allLT nm (fun m => !(if right then dotMV (Y z) z (N m) nR nC else dotMV z (Y z) (N m) nR nC))))

/-- the K-W condition at one mask `z` (the body of `kwOK`) -/
def kwAt (M0 : ℕ → ℕ) (N : ℕ → ℕ → ℕ) (nm : ℕ) (Y : ℕ → ℕ) (nR nC : ℕ) (right : Bool) (z : ℕ) : Bool :=
  z == 0 ||
    ((if right then dotMV (Y z) z M0 nR nC else dotMV z (Y z) M0 nR nC) &&
     B334.Core.allLT nm (fun m => !(if right then dotMV (Y z) z (N m) nR nC else dotMV z (Y z) (N m) nR nC)))

theorem allLT_of_forall {n : ℕ} {g : ℕ → Bool} (h : ∀ i < n, g i = true) : B334.Core.allLT n g = true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (g k && B334.Core.allLT k g) = true
    rw [Bool.and_eq_true]
    exact ⟨h k (Nat.lt_succ_self k), ih (fun i hi => h i (Nat.lt_succ_of_lt hi))⟩

/-- K-W from chunk facts: `K` chunks of `C` masks each cover `0 … 2 ^ need - 1` -/
theorem kwOK_of_chunks {M0 : ℕ → ℕ} {N : ℕ → ℕ → ℕ} {nm : ℕ} {Y : ℕ → ℕ} {nR nC need : ℕ} {right : Bool}
    (C K : ℕ) (hn : 2 ^ need ≤ K * C) (h : ∀ k < K, ∀ i < C, kwAt M0 N nm Y nR nC right (k * C + i) = true) :
    kwOK M0 N nm Y nR nC need right = true := by
  apply allLT_of_forall
  intro z hz
  have hC : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · subst h0; simp at hn
    · exact h0
  have hk : z / C < K := by
    rw [Nat.div_lt_iff_lt_mul hC]; omega
  have := h (z / C) hk (z % C) (Nat.mod_lt z hC)
  rw [Nat.div_add_mod' z C] at this
  exact this

/-- the index `m = s·f + l` of `N` stays below `nr·f` -/
theorem idx_lt {nr f : ℕ} (s : Fin nr) (l : Fin f) : s.val * f + l.val < nr * f := by
  have h1 := s.isLt; have h2 := l.isLt
  calc s.val * f + l.val < s.val * f + f := by omega
    _ = (s.val + 1) * f := by ring
    _ ≤ nr * f := Nat.mul_le_mul_right _ h1

theorem kw_right {M0 : ℕ → ℕ} {N : ℕ → ℕ → ℕ} {nm : ℕ} {Y : ℕ → ℕ} {nR nC : ℕ}
    (h : kwOK M0 N nm Y nR nC nC true = true) (z : Fin nC → ZMod 2) (hz : z ≠ 0) :
    ∃ y : Fin nR → ZMod 2, y ⬝ᵥ (mmat nR nC M0).mulVec z = 1 ∧
      ∀ m < nm, y ⬝ᵥ (mmat nR nC (N m)).mulVec z = 0 := by
  have hk := B334.Core.allLT_spec h (maskOf z) (maskOf_lt z)
  have hne : (maskOf z == 0) = false := by simp [maskOf_ne_zero z hz]
  simp only [hne, Bool.false_or, Bool.and_eq_true, ↓reduceIte] at hk
  obtain ⟨h1, h2⟩ := hk
  refine ⟨mvec nR (Y (maskOf z)), ?_, fun m hm => ?_⟩
  · have := zb_dotMV (Y (maskOf z)) (maskOf z) M0 nR nC
    rw [h1, mvec_maskOf] at this
    exact this.symm
  · have h3 := B334.Core.allLT_spec h2 m hm
    have := zb_dotMV (Y (maskOf z)) (maskOf z) (N m) nR nC
    rw [mvec_maskOf] at this
    rw [← this]
    simp only [Bool.not_eq_true', ↓reduceIte] at h3
    rw [h3]; rfl

theorem kw_left {M0 : ℕ → ℕ} {N : ℕ → ℕ → ℕ} {nm : ℕ} {Y : ℕ → ℕ} {nR nC : ℕ}
    (h : kwOK M0 N nm Y nR nC nR false = true) (z : Fin nR → ZMod 2) (hz : z ≠ 0) :
    ∃ y : Fin nC → ZMod 2, z ⬝ᵥ (mmat nR nC M0).mulVec y = 1 ∧
      ∀ m < nm, z ⬝ᵥ (mmat nR nC (N m)).mulVec y = 0 := by
  have hk := B334.Core.allLT_spec h (maskOf z) (maskOf_lt z)
  have hne : (maskOf z == 0) = false := by simp [maskOf_ne_zero z hz]
  simp only [hne, Bool.false_or, Bool.and_eq_true, Bool.false_eq_true, ↓reduceIte] at hk
  obtain ⟨h1, h2⟩ := hk
  refine ⟨mvec nC (Y (maskOf z)), ?_, fun m hm => ?_⟩
  · have := zb_dotMV (maskOf z) (Y (maskOf z)) M0 nR nC
    rw [h1, mvec_maskOf] at this
    exact this.symm
  · have h3 := B334.Core.allLT_spec h2 m hm
    have := zb_dotMV (maskOf z) (Y (maskOf z)) (N m) nR nC
    rw [mvec_maskOf] at this
    rw [← this]
    simp only [Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte] at h3
    rw [h3]; rfl

/-- K-W in the form `rank_ge_right` takes, with `N` indexed by `m = s·f + l` -/
theorem hW_right {M0 : ℕ → ℕ} {N : ℕ → ℕ → ℕ} {Y : ℕ → ℕ} {nR nC nr f : ℕ}
    (h : kwOK M0 N (nr * f) Y nR nC nC true = true) :
    ∀ z : Fin nC → ZMod 2, z ≠ 0 → ∃ y : Fin nR → ZMod 2, y ⬝ᵥ (mmat nR nC M0).mulVec z = 1 ∧
      ∀ (s : Fin nr) (l : Fin f), y ⬝ᵥ (mmat nR nC (N (s.val * f + l.val))).mulVec z = 0 := by
  intro z hz
  obtain ⟨y, h1, h2⟩ := kw_right h z hz
  exact ⟨y, h1, fun s l => h2 _ (idx_lt s l)⟩

/-- K-W in the form `rank_ge_left` takes -/
theorem hW_left {M0 : ℕ → ℕ} {N : ℕ → ℕ → ℕ} {Y : ℕ → ℕ} {nR nC nr f : ℕ}
    (h : kwOK M0 N (nr * f) Y nR nC nR false = true) :
    ∀ z : Fin nR → ZMod 2, z ≠ 0 → ∃ y : Fin nC → ZMod 2, z ⬝ᵥ (mmat nR nC M0).mulVec y = 1 ∧
      ∀ (s : Fin nr) (l : Fin f), z ⬝ᵥ (mmat nR nC (N (s.val * f + l.val))).mulVec y = 0 := by
  intro z hz
  obtain ⟨y, h1, h2⟩ := kw_left h z hz
  exact ⟨y, h1, fun s l => h2 _ (idx_lt s l)⟩

/-! ## K-F1 and K-π -/

/-- **K-F1.** Values of the forced slices at `f` positions, `H l j = U (Fi l) (Pu j) (Pv j)`, with a left inverse `G`,
make the forced slices linearly independent. -/
theorem linIndep_of_inv {n0 m1 m2 f : ℕ} (U : Fin n0 → Fin m1 → Fin m2 → ZMod 2) (Fi : Fin f → Fin n0)
    (Pu : Fin f → Fin m1) (Pv : Fin f → Fin m2) (G : Matrix (Fin f) (Fin f) (ZMod 2))
    (hG : G * (Matrix.of fun l j => U (Fi l) (Pu j) (Pv j)) = 1) :
    LinearIndependent (ZMod 2) (fun l => U (Fi l)) := by
  set H : Matrix (Fin f) (Fin f) (ZMod 2) := Matrix.of fun l j => U (Fi l) (Pu j) (Pv j) with hH
  have hHG : H * G = 1 := Matrix.mul_eq_one_comm.mp hG
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hv : Matrix.vecMul g H = 0 := by
    funext j
    have := congrFun (congrFun hg (Pu j)) (Pv j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.vecMul, dotProduct, hH, Matrix.of_apply, Pi.zero_apply]
    exact this
  have : g = 0 := by
    have h1 : Matrix.vecMul (Matrix.vecMul g H) G = g := by
      rw [Matrix.vecMul_vecMul, hHG, Matrix.vecMul_one]
    rw [← h1, hv, Matrix.zero_vecMul]
  intro l; rw [this]; rfl

/-- **K-π.** If π kills every basis mask, it kills their span. -/
theorem ker_of_basis {na : ℕ} (π : Matrix (Fin na) (Fin (3 * 3)) (ZMod 2)) (basis : List ℕ)
    (h : ∀ b ∈ basis, π.mulVec (vecOfMask (3 * 3) b) = 0) : ∀ v ∈ spanMasks basis, π.mulVec v = 0 := by
  intro v hv
  have hle : spanMasks basis ≤ LinearMap.ker π.mulVecLin := by
    unfold spanMasks
    rw [Submodule.span_le]
    rintro w ⟨m, hm, rfl⟩
    simpa using h m hm
  have := hle hv
  simpa using this

/-! ## The flattenings as linear maps -/

section flatlin

variable {nr m1 m2 : ℕ}

def flatAL : (Fin nr → Fin m1 → Fin m2 → ZMod 2) →ₗ[ZMod 2] Matrix (Fin nr) (Fin m1 × Fin m2) (ZMod 2) where
  toFun := flatA
  map_add' := flatA_add
  map_smul' := flatA_smul
def flatBL : (Fin nr → Fin m1 → Fin m2 → ZMod 2) →ₗ[ZMod 2] Matrix (Fin m1) (Fin nr × Fin m2) (ZMod 2) where
  toFun := flatB
  map_add' := flatB_add
  map_smul' := flatB_smul
def flatCL : (Fin nr → Fin m1 → Fin m2 → ZMod 2) →ₗ[ZMod 2] Matrix (Fin m2) (Fin nr × Fin m1) (ZMod 2) where
  toFun := flatC
  map_add' := flatC_add
  map_smul' := flatC_smul

theorem flatAL_rank (V : Fin nr → Fin m1 → Fin m2 → ZMod 2) (r : ℕ) (h : RankLE V r) : (flatAL V).rank ≤ r :=
  (rank_flat_le V r h).1
theorem flatBL_rank (V : Fin nr → Fin m1 → Fin m2 → ZMod 2) (r : ℕ) (h : RankLE V r) : (flatBL V).rank ≤ r :=
  (rank_flat_le V r h).2.1
theorem flatCL_rank (V : Fin nr → Fin m1 → Fin m2 → ZMod 2) (r : ℕ) (h : RankLE V r) : (flatCL V).rank ≤ r :=
  (rank_flat_le V r h).2.2

end flatlin

/-! ## L-K4 + L-K5 with the data, and the per-row assembly -/

section assembly

variable {n0 m1 m2 f nr : ℕ} {ρ γ : Type*} [Fintype ρ] [Fintype γ] [DecidableEq ρ] [DecidableEq γ]

/-- the restricted affine family `(Φ (usub α))[Rp, Cp] = M0 + ∑ α s l • N s l` -/
theorem sub_usub (U : Fin n0 → Fin m1 → Fin m2 → ZMod 2) (Fi : Fin f → Fin n0) (Ri : Fin nr → Fin n0)
    (Φ : (Fin nr → Fin m1 → Fin m2 → ZMod 2) →ₗ[ZMod 2] Matrix ρ γ (ZMod 2)) {nR nC : ℕ} (Rp : Fin nR → ρ)
    (Cp : Fin nC → γ) (α : Fin nr → Fin f → ZMod 2) :
    (Φ (usub U Fi Ri α)).submatrix Rp Cp =
      (Φ (usub U Fi Ri 0)).submatrix Rp Cp + ∑ s, ∑ l, α s l • (Φ (eslice U Fi s l)).submatrix Rp Cp := by
  rw [usub_eq_affine, map_add, map_sum]
  ext r j
  simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.sum_apply, Finset.sum_apply, map_sum, map_smul]

/-- L-K5 with witnesses, right form -/
theorem rank_ge_right (U : Fin n0 → Fin m1 → Fin m2 → ZMod 2) (Fi : Fin f → Fin n0) (Ri : Fin nr → Fin n0)
    (Φ : (Fin nr → Fin m1 → Fin m2 → ZMod 2) →ₗ[ZMod 2] Matrix ρ γ (ZMod 2)) {nR need : ℕ} (Rp : Fin nR → ρ)
    (Cp : Fin need → γ) (M0 : Matrix (Fin nR) (Fin need) (ZMod 2))
    (N : Fin nr → Fin f → Matrix (Fin nR) (Fin need) (ZMod 2))
    (hM0 : (Φ (usub U Fi Ri 0)).submatrix Rp Cp = M0) (hN : ∀ s l, (Φ (eslice U Fi s l)).submatrix Rp Cp = N s l)
    (hW : ∀ z : Fin need → ZMod 2, z ≠ 0 → ∃ y : Fin nR → ZMod 2, y ⬝ᵥ M0.mulVec z = 1 ∧
      ∀ s l, y ⬝ᵥ (N s l).mulVec z = 0) (α : Fin nr → Fin f → ZMod 2) :
    need ≤ (Φ (usub U Fi Ri α)).rank := by
  apply rank_ge_of_ker_trivial _ Rp Cp
  intro z hz
  obtain ⟨y, hy1, hy0⟩ := hW z hz
  apply mulVec_ne_zero_of_witness _ z y
  rw [sub_usub, hM0]
  simp only [hN, Matrix.add_mulVec, dotProduct_add, hy1, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
    dotProduct_smul, hy0, smul_zero, Finset.sum_const_zero, add_zero]

/-- L-K5 with witnesses, left form -/
theorem rank_ge_left (U : Fin n0 → Fin m1 → Fin m2 → ZMod 2) (Fi : Fin f → Fin n0) (Ri : Fin nr → Fin n0)
    (Φ : (Fin nr → Fin m1 → Fin m2 → ZMod 2) →ₗ[ZMod 2] Matrix ρ γ (ZMod 2)) {need nC : ℕ} (Rp : Fin need → ρ)
    (Cp : Fin nC → γ) (M0 : Matrix (Fin need) (Fin nC) (ZMod 2))
    (N : Fin nr → Fin f → Matrix (Fin need) (Fin nC) (ZMod 2))
    (hM0 : (Φ (usub U Fi Ri 0)).submatrix Rp Cp = M0) (hN : ∀ s l, (Φ (eslice U Fi s l)).submatrix Rp Cp = N s l)
    (hW : ∀ z : Fin need → ZMod 2, z ≠ 0 → ∃ y : Fin nC → ZMod 2, z ⬝ᵥ M0.mulVec y = 1 ∧
      ∀ s l, z ⬝ᵥ (N s l).mulVec y = 0) (α : Fin nr → Fin f → ZMod 2) :
    need ≤ (Φ (usub U Fi Ri α)).rank := by
  apply rank_ge_of_coker_trivial _ Rp Cp
  intro z hz hzero
  obtain ⟨y, hy1, hy0⟩ := hW z hz
  have hdot : z ⬝ᵥ ((Φ (usub U Fi Ri α)).submatrix Rp Cp).mulVec y = 1 := by
    rw [sub_usub, hM0]
    simp only [hN, Matrix.add_mulVec, dotProduct_add, hy1, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
      dotProduct_smul, hy0, smul_zero, Finset.sum_const_zero, add_zero]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hzero] at hdot
  simp at hdot

/-- **The per-row assembly.** From K-π (`hS`), K-U (`hU`, with `U` the chosen permutation of `qproj π T334`), K-F1
(`hli`), the rank bound of the flattening (`hΦ`), the witness consequence (`hwit`) and K-L (`hL`). -/
theorem rowValid_of_K {na : ℕ} (basis : List ℕ) (lb : ℕ) (π : Matrix (Fin na) (Fin (3 * 3)) (ZMod 2))
    (hS : ∀ v ∈ spanMasks basis, π.mulVec v = 0)
    (U : Fin n0 → Fin m1 → Fin m2 → ZMod 2)
    (hU : ∀ r, RankLE (qproj π T334) r → RankLE U r)
    (Fi : Fin f → Fin n0) (Ri : Fin nr → Fin n0) (hli : LinearIndependent (ZMod 2) (fun l => U (Fi l)))
    (Φ : (Fin nr → Fin m1 → Fin m2 → ZMod 2) →ₗ[ZMod 2] Matrix ρ γ (ZMod 2))
    (hΦ : ∀ V r, RankLE V r → (Φ V).rank ≤ r) {need : ℕ}
    (hwit : ∀ α, need ≤ (Φ (usub U Fi Ri α)).rank) (hL : lb ≤ f + need) : RowValid basis lb := by
  apply quotLB_of_proj T334 (spanMasks basis) π hS lb
  intro r hr
  obtain ⟨hf, α, hα⟩ := subst f r U Fi Ri hli (hU r hr)
  have h1 := hΦ _ _ hα
  have h2 := hwit α
  omega

end assembly

end B334.MethodK
