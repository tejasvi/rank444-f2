import B334.Statement

/-! # L-CC: the capacity bound with single-coset rows (row 44)

Let `S` be a subspace and `Sc i` (`i < N`) subspaces containing `S` such that every vector outside `S` lies in exactly
one of them (for row 44: the `N = 7` spaces `S ⊕ ⟨c⟩` over the nonzero cosets `c` of `S`, `dim A/S = 3`). If
`QuotLB T (Sc i) (lbc i)` for every `i`, then every decomposition has `r` outside terms with `(N - 1) · r ≥ ∑ lbc i`;
so `QuotLB T S k` whenever `(N - 1)(k - 1) < ∑ lbc i`. -/

namespace B334.MethodK

open Finset

theorem quotLB_coset_count {n0 n1 n2 : ℕ} (T : Fin n0 → Fin n1 → Fin n2 → ZMod 2)
    (S : Submodule (ZMod 2) (Fin n0 → ZMod 2)) {N : ℕ} (Sc : Fin N → Submodule (ZMod 2) (Fin n0 → ZMod 2))
    (lbc : Fin N → ℕ) (hc : ∀ i, QuotLB T (Sc i) (lbc i)) (hsub : ∀ i, S ≤ Sc i)
    (hone : ∀ v, v ∉ S → ∃! i, v ∈ Sc i) (k : ℕ) (hk : (N - 1) * (k - 1) < ∑ i, lbc i) : QuotLB T S k := by
  classical
  intro r a b c hT
  -- the bound for each Sc i, as a filter count
  have hi : ∀ i, lbc i ≤ (Finset.univ.filter (fun t => a t ∉ Sc i)).card := by
    intro i
    have := hc i r a b c hT
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  -- a vector outside S lies outside exactly N - 1 of the Sc i
  have hcount : ∀ v, v ∉ S → (Finset.univ.filter (fun i => v ∉ Sc i)).card = N - 1 := by
    intro v hv
    obtain ⟨i0, hi0, huniq⟩ := hone v hv
    have hset : Finset.univ.filter (fun i => v ∉ Sc i) = Finset.univ.erase i0 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro h e; subst e; exact h hi0
      · intro h hin; exact h (huniq i hin)
    rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- double counting
  have hdouble : ∑ i, (Finset.univ.filter (fun t => a t ∉ Sc i)).card =
      (N - 1) * (Finset.univ.filter (fun t => a t ∉ S)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hS : a t ∈ S
    · have h0 : ∀ i, a t ∈ Sc i := fun i => hsub i hS
      simp [hS, h0]
    · have := hcount (a t) hS
      rw [Finset.card_filter] at this
      rw [if_pos hS, mul_one]
      exact this
  have hsum : ∑ i, lbc i ≤ (N - 1) * (Finset.univ.filter (fun t => a t ∉ S)).card := by
    rw [← hdouble]
    exact Finset.sum_le_sum (fun i _ => hi i)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_contra hlt
  rw [not_le] at hlt
  have : (N - 1) * (Finset.univ.filter (fun t => a t ∉ S)).card ≤ (N - 1) * (k - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end B334.MethodK
