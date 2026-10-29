import B334.Bind.Sym

/-! # L1: the split flattening of ⟨3,3,4⟩ (`B334/Statement.lean` `SplitFlattening334`)

* `splitF X`: the 36×36 matrix with rows `(i, y)` and columns `(j, z)`, entry `X (3i+j) y z` (the first factor's row
  index paired with the second factor, its column index with the third).
* `splitF_T334`: `splitF T334` is the identity matrix with its columns permuted by `colRow : (j, 3k+i) ↦ (i, 4j+k)`,
  so its rank is 36 (`rank_splitF_T334`).
* `splitF_outer3`: `splitF (a ⊗ b ⊗ c) = liftM b · mat3 a · (liftM c)ᵀ`, so a term contributes rank at most `rk(a)`.
* `rank_add_le`, `rank_sum_le`: matrix rank is subadditive.
* `split_flattening`: `36 = rank (splitF T334) ≤ ∑ₛ rank (splitF termₛ) ≤ ∑ₛ rk(aₛ)`. -/

namespace B334.Lem

open B334 Finset
open scoped Matrix

/-- the split flattening: rows `(i, y)`, columns `(j, z)` -/
def splitF (X : Fin (3 * 3) → Fin (3 * 4) → Fin (4 * 3) → ZMod 2) :
    Matrix (Fin 3 × Fin (3 * 4)) (Fin 3 × Fin (4 * 3)) (ZMod 2) :=
  Matrix.of fun p q => X (finProdFinEquiv (p.1, q.1)) p.2 q.2

theorem splitF_sum {r : ℕ} (X : Fin r → Fin (3 * 3) → Fin (3 * 4) → Fin (4 * 3) → ZMod 2) :
    splitF (∑ s, X s) = ∑ s, splitF (X s) := by
  ext p q
  simp [splitF, Finset.sum_apply, Matrix.sum_apply]

/-- a vector `b` placed in block `i'` of the rows `(i, y)` -/
def liftM {n : ℕ} (b : Fin n → ZMod 2) : Matrix (Fin 3 × Fin n) (Fin 3) (ZMod 2) :=
  Matrix.of fun p i' => if p.1 = i' then b p.2 else 0

theorem splitF_outer3 (a : Fin (3 * 3) → ZMod 2) (b : Fin (3 * 4) → ZMod 2) (c : Fin (4 * 3) → ZMod 2) :
    splitF (outer3 a b c) = liftM b * mat3 a * (liftM c)ᵀ := by
  ext ⟨i, y⟩ ⟨j, z⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp only [splitF, outer3, liftM, mat3, Matrix.of_apply, Matrix.transpose_apply, if_true]
      ring
    · intro i' _ hi'
      simp [liftM, Ne.symm hi']
    · simp
  · intro j' _ hj'
    simp [liftM, Matrix.transpose_apply, Ne.symm hj']
  · simp

theorem rank_splitF_outer3_le (a : Fin (3 * 3) → ZMod 2) (b : Fin (3 * 4) → ZMod 2) (c : Fin (4 * 3) → ZMod 2) :
    (splitF (outer3 a b c)).rank ≤ (mat3 a).rank := by
  rw [splitF_outer3]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem rank_add_le {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_sum_le {ι m n : Type*} [Fintype m] [Fintype n] (s : Finset ι) (M : ι → Matrix m n (ZMod 2)) :
    (∑ t ∈ s, M t).rank ≤ ∑ t ∈ s, (M t).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- the column `(j, z = 3k+i)` of `splitF T334` has its 1 in the row `(i, y = 4j+k)` -/
def colRow : Fin 3 × Fin (4 * 3) ≃ Fin 3 × Fin (3 * 4) where
  toFun q := ((finProdFinEquiv.symm q.2).2, finProdFinEquiv (q.1, (finProdFinEquiv.symm q.2).1))
  invFun p := ((finProdFinEquiv.symm p.2).1, finProdFinEquiv ((finProdFinEquiv.symm p.2).2, p.1))
  left_inv q := by simp
  right_inv p := by simp

theorem colRow_apply (j : Fin 3) (k : Fin 4) (i : Fin 3) :
    colRow (j, finProdFinEquiv (k, i)) = (i, finProdFinEquiv (j, k)) := by
  simp [colRow]

theorem splitF_T334 :
    splitF T334 = (1 : Matrix (Fin 3 × Fin (3 * 4)) (Fin 3 × Fin (3 * 4)) (ZMod 2)).submatrix (Equiv.refl _) colRow := by
  ext ⟨i, y⟩ ⟨j, z⟩
  obtain ⟨⟨j', k⟩, rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨k', i'⟩, rfl⟩ := finProdFinEquiv.surjective z
  rw [Matrix.submatrix_apply, colRow_apply, Equiv.refl_apply, Matrix.one_apply]
  simp only [splitF, Matrix.of_apply]
  rw [T334_apply]
  apply if_congr _ rfl rfl
  rw [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3.symm, h1.symm, h2⟩
  · rintro ⟨g1, g2, g3⟩
    exact ⟨g2.symm, g3, g1.symm⟩

theorem rank_splitF_T334 : (splitF T334).rank = 36 := by
  rw [splitF_T334, Matrix.rank_submatrix, Matrix.rank_one]
  simp

/-- **L1** (`split_flattening`). -/
theorem split_flattening : SplitFlattening334 := by
  intro r a b c hT
  have h1 : splitF T334 = ∑ s, splitF (outer3 (a s) (b s) (c s)) := by rw [hT, splitF_sum]
  calc 36 = (splitF T334).rank := rank_splitF_T334.symm
    _ = (∑ s, splitF (outer3 (a s) (b s) (c s))).rank := by rw [h1]
    _ ≤ ∑ s, (splitF (outer3 (a s) (b s) (c s))).rank := rank_sum_le _ _
    _ ≤ ∑ s, (mat3 (a s)).rank := Finset.sum_le_sum (fun s _ => rank_splitF_outer3_le _ _ _)

end B334.Lem
