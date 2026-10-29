import B334.MethodK.Subst
import B334.Core.LinAlg

/-! # Method K, L-K3–L-K5: flattenings, their affine form, and the rank from witnesses

* `flatA`, `flatB`, `flatC`: the three flattenings of an `nr × m1 × m2` tensor (with product indices).
* L-K3 `rank_flat_le`: a decomposition with `r` terms bounds the rank of each flattening by `r`.
* L-K4 `flat*_usub`: `φ(U′(α)) = φ(U′(0)) + ∑_{s,l} α s l • φ(E s l)`.
* L-K5 `rank_ge_of_ker_trivial` (right form) and `rank_ge_of_coker_trivial` (left form): if a submatrix with `need`
  columns (rows) has no nonzero kernel (cokernel) vector, the matrix has rank at least `need`. -/

namespace B334.MethodK

open Finset Matrix

variable {K : Type*} [Field K]

section flat

variable {nr m1 m2 : ℕ}

/-- (a): row `s`, column `(u, v)` -/
def flatA (V : Fin nr → Fin m1 → Fin m2 → K) : Matrix (Fin nr) (Fin m1 × Fin m2) K := fun s p => V s p.1 p.2
/-- (b): row `u`, column `(s, v)` -/
def flatB (V : Fin nr → Fin m1 → Fin m2 → K) : Matrix (Fin m1) (Fin nr × Fin m2) K := fun u p => V p.1 u p.2
/-- (c): row `v`, column `(s, u)` -/
def flatC (V : Fin nr → Fin m1 → Fin m2 → K) : Matrix (Fin m2) (Fin nr × Fin m1) K := fun v p => V p.1 p.2 v

theorem rank_sum_vecMulVec_le {ι m n : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [Fintype n]
    (β : ι → m → K) (γ : ι → n → K) : (∑ t, vecMulVec (β t) (γ t)).rank ≤ Fintype.card ι := by
  rw [B334.Core.sum_vecMulVec_eq]
  calc (B334.Core.facB Finset.univ β * (B334.Core.facB Finset.univ γ)ᵀ).rank
      ≤ (B334.Core.facB Finset.univ β).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card ↥(Finset.univ : Finset ι) := Matrix.rank_le_card_width _
    _ = Fintype.card ι := by simp

/-- **L-K3.** -/
theorem rank_flat_le (V : Fin nr → Fin m1 → Fin m2 → K) (r : ℕ) (h : RankLE V r) :
    (flatA V).rank ≤ r ∧ (flatB V).rank ≤ r ∧ (flatC V).rank ≤ r := by
  obtain ⟨x, y, z, hxyz⟩ := h
  have hA : flatA V = ∑ t, vecMulVec (x t) (fun p : Fin m1 × Fin m2 => y t p.1 * z t p.2) := by
    ext s p; simp [flatA, hxyz, outer3, Finset.sum_apply, Matrix.sum_apply, vecMulVec_apply, mul_assoc]
  have hB : flatB V = ∑ t, vecMulVec (y t) (fun p : Fin nr × Fin m2 => x t p.1 * z t p.2) := by
    ext u p; simp only [flatB, hxyz, outer3, Finset.sum_apply, Matrix.sum_apply, vecMulVec_apply]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have hC : flatC V = ∑ t, vecMulVec (z t) (fun p : Fin nr × Fin m1 => x t p.1 * y t p.2) := by
    ext v p; simp only [flatC, hxyz, outer3, Finset.sum_apply, Matrix.sum_apply, vecMulVec_apply]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]; simpa using rank_sum_vecMulVec_le (fun t => x t) (fun t (p : Fin m1 × Fin m2) => y t p.1 * z t p.2)
  · rw [hB]; simpa using rank_sum_vecMulVec_le (fun t => y t) (fun t (p : Fin nr × Fin m2) => x t p.1 * z t p.2)
  · rw [hC]; simpa using rank_sum_vecMulVec_le (fun t => z t) (fun t (p : Fin nr × Fin m1) => x t p.1 * y t p.2)

end flat

section affine

variable {n0 m1 m2 f nr : ℕ}

/-- `E s l`: slice `s` is the forced slice `U (Fi l)`, the other slices are zero -/
def eslice (U : Fin n0 → Fin m1 → Fin m2 → K) (Fi : Fin f → Fin n0) (s : Fin nr) (l : Fin f) :
    Fin nr → Fin m1 → Fin m2 → K :=
  fun s' u v => if s' = s then U (Fi l) u v else 0

theorem usub_eq_affine (U : Fin n0 → Fin m1 → Fin m2 → K) (Fi : Fin f → Fin n0) (Ri : Fin nr → Fin n0)
    (α : Fin nr → Fin f → K) :
    usub U Fi Ri α = usub U Fi Ri 0 + ∑ s, ∑ l, α s l • eslice U Fi s l := by
  funext s' u v
  simp only [usub, eslice, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, mul_ite, mul_zero]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp [Finset.sum_ite_eq]

/-- **L-K4** for each flattening: linearity. -/
theorem flatA_add (V W : Fin nr → Fin m1 → Fin m2 → K) : flatA (V + W) = flatA V + flatA W := by
  ext; simp [flatA]
theorem flatB_add (V W : Fin nr → Fin m1 → Fin m2 → K) : flatB (V + W) = flatB V + flatB W := by
  ext; simp [flatB]
theorem flatC_add (V W : Fin nr → Fin m1 → Fin m2 → K) : flatC (V + W) = flatC V + flatC W := by
  ext; simp [flatC]
theorem flatA_smul (c : K) (V : Fin nr → Fin m1 → Fin m2 → K) : flatA (c • V) = c • flatA V := by
  ext; simp [flatA]
theorem flatB_smul (c : K) (V : Fin nr → Fin m1 → Fin m2 → K) : flatB (c • V) = c • flatB V := by
  ext; simp [flatB]
theorem flatC_smul (c : K) (V : Fin nr → Fin m1 → Fin m2 → K) : flatC (c • V) = c • flatC V := by
  ext; simp [flatC]
theorem flatA_sum {ι : Type*} (S : Finset ι) (V : ι → Fin nr → Fin m1 → Fin m2 → K) :
    flatA (∑ i ∈ S, V i) = ∑ i ∈ S, flatA (V i) := by
  ext; simp [flatA, Finset.sum_apply, Matrix.sum_apply]
theorem flatB_sum {ι : Type*} (S : Finset ι) (V : ι → Fin nr → Fin m1 → Fin m2 → K) :
    flatB (∑ i ∈ S, V i) = ∑ i ∈ S, flatB (V i) := by
  ext; simp [flatB, Finset.sum_apply, Matrix.sum_apply]
theorem flatC_sum {ι : Type*} (S : Finset ι) (V : ι → Fin nr → Fin m1 → Fin m2 → K) :
    flatC (∑ i ∈ S, V i) = ∑ i ∈ S, flatC (V i) := by
  ext; simp [flatC, Finset.sum_apply, Matrix.sum_apply]

end affine

section witness

variable {ρ γ : Type*} [Fintype ρ] [Fintype γ] [DecidableEq ρ] [DecidableEq γ]

/-- a row-and-column selection is a product with 0/1 selection matrices -/
theorem submatrix_eq_mul {nR nC : ℕ} (M : Matrix ρ γ K) (R : Fin nR → ρ) (C : Fin nC → γ) :
    M.submatrix R C = (Matrix.of fun i r => if R i = r then (1 : K) else 0) * M *
      (Matrix.of fun g j => if C j = g then (1 : K) else 0) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_ite_eq]

theorem rank_submatrix_le' {nR nC : ℕ} (M : Matrix ρ γ K) (R : Fin nR → ρ) (C : Fin nC → γ) :
    (M.submatrix R C).rank ≤ M.rank := by
  rw [submatrix_eq_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- a matrix whose `mulVec` has trivial kernel has full column rank -/
theorem rank_eq_of_mulVec_inj {nR nC : ℕ} (A : Matrix (Fin nR) (Fin nC) K)
    (h : ∀ z : Fin nC → K, z ≠ 0 → A.mulVec z ≠ 0) : A.rank = nC := by
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    by_contra hne
    exact h z hne hz
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at hrn
  unfold Matrix.rank
  exact hrn

/-- **L-K5, right form.** -/
theorem rank_ge_of_ker_trivial {nR need : ℕ} (M : Matrix ρ γ K) (R : Fin nR → ρ) (C : Fin need → γ)
    (h : ∀ z : Fin need → K, z ≠ 0 → (M.submatrix R C).mulVec z ≠ 0) : need ≤ M.rank := by
  rw [← rank_eq_of_mulVec_inj _ h]
  exact rank_submatrix_le' M R C

/-- **L-K5, left form.** -/
theorem rank_ge_of_coker_trivial {need nC : ℕ} (M : Matrix ρ γ K) (R : Fin need → ρ) (C : Fin nC → γ)
    (h : ∀ z : Fin need → K, z ≠ 0 → (M.submatrix R C)ᵀ.mulVec z ≠ 0) : need ≤ M.rank := by
  rw [← Matrix.rank_transpose M]
  have h' : ∀ z : Fin need → K, z ≠ 0 → (Mᵀ.submatrix C R).mulVec z ≠ 0 := by
    intro z hz; have := h z hz; rwa [Matrix.transpose_submatrix] at this
  exact rank_ge_of_ker_trivial Mᵀ C R h'

/-- a witness `y` with `y ⬝ (A z) = 1` shows `A z ≠ 0` -/
theorem mulVec_ne_zero_of_witness {nR nC : ℕ} (A : Matrix (Fin nR) (Fin nC) K) (z : Fin nC → K)
    (y : Fin nR → K) (hy : y ⬝ᵥ A.mulVec z = 1) : A.mulVec z ≠ 0 := by
  intro h0; rw [h0, dotProduct_zero] at hy; exact zero_ne_one hy

end witness

end B334.MethodK
