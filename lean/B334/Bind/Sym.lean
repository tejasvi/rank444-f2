import B334.Statement

/-! # L3a: the symmetry group G₀ = GL₃ × GL₃ of ⟨3,3,4⟩ (`B334/Statement.lean` `Sym334`)

`(a, b, c) ↦ (P a Q, Q⁻¹ b, c P⁻¹)` maps decompositions of T334 to decompositions: entrywise,
`∑_s (P A_s Q)_{ij} (Qi B_s)_{j'k} (C_s Pi)_{k'i'} = ∑ P_{iα} Q_{βj} Qi_{j'γ} Pi_{ζi'} [β = γ ∧ k = k' ∧ ζ = α]
= [k = k'] (Qi Q)_{j'j} (P Pi)_{ii'}`.  The proof decodes the flat indices with `finProdFinEquiv`. -/

namespace B334

open Finset

/-- the entries of T334 in matrix indices -/
theorem T334_apply (i j j' : Fin 3) (k k' : Fin 4) (i' : Fin 3) :
    T334 (finProdFinEquiv (i, j)) (finProdFinEquiv (j', k)) (finProdFinEquiv (k', i')) =
      if j = j' ∧ k = k' ∧ i' = i then 1 else 0 := by
  simp only [T334, mmT, finProdFinEquiv_apply_val]
  have hx0 : (↑j + 3 * ↑i : ℕ) % 3 = j := by omega
  have hx1 : (↑j + 3 * ↑i : ℕ) / 3 = i := by omega
  have hy1 : (↑k + 4 * ↑j' : ℕ) / 4 = j' := by omega
  have hy2 : (↑k + 4 * ↑j' : ℕ) % 4 = k := by omega
  have hz1 : (↑i' + 3 * ↑k' : ℕ) / 3 = k' := by omega
  have hz2 : (↑i' + 3 * ↑k' : ℕ) % 3 = i' := by omega
  simp only [hx0, hx1, hy1, hy2, hz1, hz2, Fin.val_inj]

/-- a decomposition of T334, read in matrix indices -/
theorem entry_of_decomp {r : ℕ} {a : Fin r → Fin (3 * 3) → ZMod 2} {b : Fin r → Fin (3 * 4) → ZMod 2}
    {c : Fin r → Fin (4 * 3) → ZMod 2} (hT : T334 = ∑ s, outer3 (a s) (b s) (c s))
    (i j j' : Fin 3) (k k' : Fin 4) (i' : Fin 3) :
    ∑ s, mat3 (a s) i j * mat34 (b s) j' k * mat43 (c s) k' i' = if j = j' ∧ k = k' ∧ i' = i then 1 else 0 := by
  rw [← T334_apply, hT]
  simp [outer3, mat3, mat34, mat43, Finset.sum_apply]

/-- **L3a** (`sym334`). -/
theorem sym334 : Sym334 := by
  intro P Q Pi Qi hP hQ r a b c hT
  have hQ' : Qi * Q = 1 := mul_eq_one_comm.mp hQ
  funext x y z
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j', k⟩, rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨k', i'⟩, rfl⟩ := finProdFinEquiv.surjective z
  rw [T334_apply]
  simp only [outer3, Finset.sum_apply, actA, actB, actC, Equiv.symm_apply_apply]
  -- expand the three matrix products, term by term
  have expand : ∀ s, (P * mat3 (a s) * Q) i j * (Qi * mat34 (b s)) j' k * (mat43 (c s) * Pi) k' i' =
      ∑ α : Fin 3, ∑ β : Fin 3, ∑ γ : Fin 3, ∑ ζ : Fin 3,
        (P i α * Q β j * Qi j' γ * Pi ζ i') * (mat3 (a s) α β * mat34 (b s) γ k * mat43 (c s) k' ζ) := by
    intro s
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [Finset.sum_congr rfl (fun s _ => expand s)]
  -- bring the sum over the terms innermost
  have swap : ∀ F : Fin r → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ZMod 2,
      ∑ s, ∑ α, ∑ β, ∑ γ, ∑ ζ, F s α β γ ζ = ∑ α, ∑ β, ∑ γ, ∑ ζ, ∑ s, F s α β γ ζ := by
    intro F
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Finset.sum_comm]
  rw [swap]
  simp only [← Finset.mul_sum, entry_of_decomp hT]
  by_cases hk : k = k'
  · subst hk
    simp only [eq_self_iff_true, true_and, and_true]
    have hz : ∀ α β γ : Fin 3, ∑ ζ : Fin 3, (P i α * Q β j * Qi j' γ * Pi ζ i') *
        (if β = γ ∧ ζ = α then (1 : ZMod 2) else 0) = if β = γ then P i α * Q β j * Qi j' γ * Pi α i' else 0 := by
      intro α β γ
      by_cases h : β = γ
      · simp [h, Finset.sum_ite_eq']
      · simp [h]
    simp only [hz, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hQQ : ∑ β : Fin 3, Qi j' β * Q β j = if j' = j then 1 else 0 := by
      rw [← Matrix.mul_apply, hQ', Matrix.one_apply]
    have hPP : ∑ α : Fin 3, P i α * Pi α i' = if i = i' then 1 else 0 := by
      rw [← Matrix.mul_apply, hP, Matrix.one_apply]
    have hsplit : ∑ α : Fin 3, ∑ β : Fin 3, P i α * Q β j * Qi j' β * Pi α i' =
        (∑ α : Fin 3, P i α * Pi α i') * (∑ β : Fin 3, Qi j' β * Q β j) := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => by ring))
    rw [hsplit, hQQ, hPP]
    by_cases hj : j = j'
    · by_cases hi : i' = i
      · subst hj; subst hi; simp
      · have hi' : ¬ i = i' := fun h => hi h.symm
        simp [hj, hi, hi']
    · have hj' : ¬ j' = j := fun h => hj h.symm
      simp [hj, hj']
  · simp [hk]

end B334
