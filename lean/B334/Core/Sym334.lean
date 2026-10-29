import B334.Core.Tensor334

/-! # The pair symmetry of ⟨3,3,4⟩: `(a, b, c) ↦ (a, b S, S⁻¹ c)` for `S ∈ GL₄(F₂)`

`T(X)` is invariant under the pair action, so the moved terms still decompose `T(X)` for every functional `X`:
`∑ (b S)(S⁻¹ c)ᵀ = T(X)` because `tr(X b S S⁻¹ c) = tr(X b c)`. This is a general algebraic proof, which is used
instead of a `decide` on generators. It is stated for any `S`, `Si` with `Si * S = 1`.

Port of the matrix part of `S5/Sym.lean` (`sym_sum`) from the ⟨3,3,3⟩ release (`rank333-f2`, Apache-2.0); there the
moving matrix is 3×3 (the middle index has 3 values), here it is 4×4. The bit-level wrappers (`nv`, the 16-bit matrix
encoding, the witness tables `WB` and `WC`) come with the bit layer. -/

open Matrix

set_option linter.unusedSectionVars false

namespace B334.Core

/-- the second-factor coordinate `y = 4j+k` -/
def ixB (j : Fin 3) (k : Fin 4) : Fin 12 := ⟨4 * j.val + k.val, by have := j.isLt; have := k.isLt; omega⟩
/-- the third-factor coordinate `z = 3k+i` -/
def ixC (k : Fin 4) (i : Fin 3) : Fin 12 := ⟨3 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩

theorem hiB_ixB (j : Fin 3) (k : Fin 4) : hiB (ixB j k) = j := by
  apply Fin.ext; simp only [hiB, ixB]; omega
theorem loB_ixB (j : Fin 3) (k : Fin 4) : loB (ixB j k) = k := by
  apply Fin.ext; simp only [loB, ixB]; omega
theorem hiC_ixC (k : Fin 4) (i : Fin 3) : hiC (ixC k i) = k := by
  apply Fin.ext; simp only [hiC, ixC]; omega
theorem loC_ixC (k : Fin 4) (i : Fin 3) : loC (ixC k i) = i := by
  apply Fin.ext; simp only [loC, ixC]; omega

theorem vecB_ixB (b : M34) (j : Fin 3) (k : Fin 4) : vecB b (ixB j k) = b j k := by
  simp only [vecB, hiB_ixB, loB_ixB]
theorem vecC_ixC (c : M43) (k : Fin 4) (i : Fin 3) : vecC c (ixC k i) = c k i := by
  simp only [vecC, hiC_ixC, loC_ixC]

theorem TX_ix (X : M3) (j : Fin 3) (m n : Fin 4) (i : Fin 3) :
    TX X (ixB j m) (ixC n i) = if m = n then X i j else 0 := by
  unfold TX; rw [loB_ixB, hiC_ixC, loC_ixC, hiB_ixB]

theorem vecB_mul (b : M34) (S : Matrix (Fin 4) (Fin 4) F2) (y : Fin 12) :
    vecB (b * S) y = ∑ m : Fin 4, vecB b (ixB (hiB y) m) * S m (loB y) := by
  simp only [vecB, Matrix.mul_apply, hiB_ixB, loB_ixB]

theorem vecC_mul (Si : Matrix (Fin 4) (Fin 4) F2) (c : M43) (z : Fin 12) :
    vecC (Si * c) z = ∑ n : Fin 4, Si (hiC z) n * vecC c (ixC n (loC z)) := by
  simp only [vecC, Matrix.mul_apply, hiC_ixC, loC_ixC]

/-- **Pair symmetry.** The transformed terms still decompose `T(X)`. -/
theorem sym_sum334 {ι : Type*} (X : M3) (H : Finset ι) (β : ι → M34) (γ : ι → M43)
    (S Si : Matrix (Fin 4) (Fin 4) F2) (hSS : Si * S = 1)
    (hd : TX X = ∑ t ∈ H, vecMulVec (vecB (β t)) (vecC (γ t))) :
    TX X = ∑ t ∈ H, vecMulVec (vecB (β t * S)) (vecC (Si * γ t)) := by
  ext y z
  rw [Matrix.sum_apply]
  simp only [vecMulVec_apply, vecB_mul, vecC_mul]
  have key : ∀ t, (∑ m : Fin 4, vecB (β t) (ixB (hiB y) m) * S m (loB y)) *
      (∑ n : Fin 4, Si (hiC z) n * vecC (γ t) (ixC n (loC z))) =
      ∑ m : Fin 4, ∑ n : Fin 4, (S m (loB y) * Si (hiC z) n) *
        (vecB (β t) (ixB (hiB y) m) * vecC (γ t) (ixC n (loC z))) := by
    intro t; rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro n _; ring
  rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_comm]
  have inner : ∀ m n : Fin 4, ∑ t ∈ H, vecB (β t) (ixB (hiB y) m) * vecC (γ t) (ixC n (loC z)) =
      if m = n then X (loC z) (hiB y) else 0 := by
    intro m n
    have := congrFun (congrFun hd (ixB (hiB y) m)) (ixC n (loC z))
    rw [Matrix.sum_apply] at this
    simp only [vecMulVec_apply] at this
    rw [← this, TX_ix]
  have step : ∀ m : Fin 4, ∑ t ∈ H, ∑ n : Fin 4, (S m (loB y) * Si (hiC z) n) *
      (vecB (β t) (ixB (hiB y) m) * vecC (γ t) (ixC n (loC z))) =
      Si (hiC z) m * S m (loB y) * X (loC z) (hiB y) := by
    intro m
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, inner]
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl]; ring
    · intro n _ hn; rw [if_neg (fun e => hn e.symm)]; ring
    · simp
  rw [Finset.sum_congr rfl (fun m _ => step m), ← Finset.sum_mul]
  have hone : ∑ m : Fin 4, Si (hiC z) m * S m (loB y) = (1 : Matrix (Fin 4) (Fin 4) F2) (hiC z) (loB y) := by
    rw [← hSS, Matrix.mul_apply]
  rw [hone, Matrix.one_apply]
  unfold TX
  by_cases e : loB y = hiC z
  · rw [if_pos e, if_pos e.symm, one_mul]
  · rw [if_neg e, if_neg (fun x => e x.symm), zero_mul]

end B334.Core
