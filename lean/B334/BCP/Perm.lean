import B334.BCP.Leaf

/-! # `NoDecomp` does not depend on the order of the terms

A certificate refers to its leaf's terms by index, so a leaf record keeps the term order of the certificate generator.
The E1 side builds the same leaf with its own order. `noDecomp_perm`: if two packed term lists agree up to a
permutation `σ` of the indices, `NoDecomp` for one gives it for the other (same `n`, same domain). -/

namespace B334.BCP

open B334.BC B334.Core Matrix

theorem sum_filter_range_eq_fin {α : Type*} [AddCommMonoid α] (n : Nat) (p : Nat → Prop) [DecidablePred p]
    (f : Nat → α) : ∑ t ∈ (Finset.range n).filter p, f t = ∑ t : Fin n, if p t.val then f t.val else 0 := by
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range (fun t => if p t then f t else 0)]

theorem noDecomp_perm {T T' n dom : Nat} (σ : Fin n ≃ Fin n) (hσ : ∀ s : Fin n, aT T' s.val = aT T (σ s).val)
    (h : NoDecomp T n dom) : NoDecomp T' n dom := by
  rintro ⟨b', c', hbc', hd'⟩
  apply h
  let b : Nat → Nat := fun t => if ht : t < n then b' (σ.symm ⟨t, ht⟩).val else 1
  let c : Nat → Nat := fun t => if ht : t < n then c' (σ.symm ⟨t, ht⟩).val else 1
  refine ⟨b, c, fun t ht => ?_, fun X hX hdom => ?_⟩
  · simp only [b, c, dif_pos ht]
    exact hbc' _ (σ.symm ⟨t, ht⟩).isLt
  · rw [hd' X hX hdom, sum_filter_range_eq_fin, sum_filter_range_eq_fin]
    rw [← Equiv.sum_comp σ (fun t : Fin n => if par (aT T t.val &&& X) = true then
      vecMulVec (nv (b t.val)) (nv (c t.val)) else 0)]
    apply Finset.sum_congr rfl
    intro s _
    have e1 : b (σ s).val = b' s.val := by
      simp only [b, dif_pos (σ s).isLt, Fin.eta, Equiv.symm_apply_apply]
    have e2 : c (σ s).val = c' s.val := by
      simp only [c, dif_pos (σ s).isLt, Fin.eta, Equiv.symm_apply_apply]
    rw [e1, e2, hσ s]

end B334.BCP
