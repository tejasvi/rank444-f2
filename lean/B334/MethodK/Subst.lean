import B334.Statement

/-! # Method K, L-K2: the substitution lemma (Hopcroft–Kerr style)

For a tensor `U` with mode-0 slices `U i`, a family of linearly independent slices `U (Fi l)` (`l < f`) and any
residual selection `Ri`, every decomposition of `U` with `r` terms gives `f ≤ r` and, for some `α`, a decomposition with
`r - f` terms of the substituted tensor `usub U Fi Ri α`, whose slice `s` is `U (Ri s) + ∑_l α s l • U (Fi l)`.

The proof is the iterated form: one nonzero forced slice kills one term (`subst_step`); the remaining forced slices
stay independent after the step; the coefficients recombine (`Fin.cons`). Only linear independence of the forced slices
is used (no rank-1 condition). The same lemma is
the substitution step of the chain lemmas, with an arbitrary residual selection. -/

namespace B334.MethodK

open Finset

variable {K : Type*} [Field K]

/-- the substituted tensor `U′(α)`: slice `s` is `U (Ri s) + ∑_l α s l • U (Fi l)` -/
def usub {n0 m1 m2 f nr : ℕ} (U : Fin n0 → Fin m1 → Fin m2 → K) (Fi : Fin f → Fin n0) (Ri : Fin nr → Fin n0)
    (α : Fin nr → Fin f → K) : Fin nr → Fin m1 → Fin m2 → K :=
  fun s u v => U (Ri s) u v + ∑ l, α s l * U (Fi l) u v

theorem tensor_apply_of_decomp {n0 m1 m2 r : ℕ} {U : Fin n0 → Fin m1 → Fin m2 → K} {x : Fin r → Fin n0 → K}
    {y : Fin r → Fin m1 → K} {z : Fin r → Fin m2 → K} (h : U = ∑ t, outer3 (x t) (y t) (z t)) (i : Fin n0)
    (u : Fin m1) (v : Fin m2) : U i u v = ∑ t, x t i * y t u * z t v := by
  rw [h]; simp [outer3, Finset.sum_apply]

/-- **One substitution step.** A nonzero slice `i0` lets one term go: for some `β`, the tensor with slices
`U i + β i • U i0` has a decomposition with `r - 1` terms (and `r ≥ 1`). -/
theorem subst_step {n0 m1 m2 r : ℕ} (U : Fin n0 → Fin m1 → Fin m2 → K) (i0 : Fin n0) (h0 : U i0 ≠ 0)
    (hU : RankLE U r) :
    1 ≤ r ∧ ∃ β : Fin n0 → K, RankLE (fun i u v => U i u v + β i * U i0 u v) (r - 1) := by
  obtain ⟨x, y, z, hxyz⟩ := hU
  have hex : ∃ t0, x t0 i0 ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply h0
    funext u v
    rw [tensor_apply_of_decomp hxyz]
    simp [hno]
  obtain ⟨t0, ht0⟩ := hex
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (fun e => by subst e; exact t0.elim0)
  refine ⟨hr, fun i => -(x t0 i) / x t0 i0, ?_⟩
  show RankLE (fun i u v => U i u v + (-(x t0 i) / x t0 i0) * U i0 u v) (r - 1)
  -- the new first factors; term t0 becomes zero
  set x' : Fin r → Fin n0 → K := fun t i => x t i + (-(x t0 i) / x t0 i0) * x t i0 with hx'
  have hx't0 : x' t0 = 0 := by
    funext i
    simp only [hx', Pi.zero_apply]
    rw [div_mul_cancel₀ _ ht0]
    ring
  have hsum : (fun i u v => U i u v + (-(x t0 i) / x t0 i0) * U i0 u v) = ∑ t, outer3 (x' t) (y t) (z t) := by
    funext i u v
    rw [tensor_apply_of_decomp hxyz i u v, tensor_apply_of_decomp hxyz i0 u v]
    simp only [outer3, Finset.sum_apply, hx']
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [show r' + 1 - 1 = r' from rfl]
  refine ⟨fun j => x' (t0.succAbove j), fun j => y (t0.succAbove j), fun j => z (t0.succAbove j), ?_⟩
  rw [hsum, Fin.sum_univ_succAbove _ t0, hx't0]
  have hz : outer3 (0 : Fin n0 → K) (y t0) (z t0) = 0 := by funext i u v; simp [outer3]
  rw [hz, zero_add]

/-- **L-K2.** Substitution of `f` linearly independent slices. -/
theorem subst {n0 m1 m2 nr : ℕ} :
    ∀ (f r : ℕ) (U : Fin n0 → Fin m1 → Fin m2 → K) (Fi : Fin f → Fin n0) (Ri : Fin nr → Fin n0),
      LinearIndependent K (fun l => U (Fi l)) → RankLE U r →
      f ≤ r ∧ ∃ α : Fin nr → Fin f → K, RankLE (usub U Fi Ri α) (r - f)
  | 0, r, U, Fi, Ri, _, hU => by
    refine ⟨Nat.zero_le _, fun _ _ => 0, ?_⟩
    rw [Nat.sub_zero]
    obtain ⟨x, y, z, hxyz⟩ := hU
    refine ⟨fun t s => x t (Ri s), y, z, ?_⟩
    funext s u v
    simp only [usub, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [tensor_apply_of_decomp hxyz]
    simp [outer3, Finset.sum_apply]
  | f + 1, r, U, Fi, Ri, hli, hU => by
    have h0 : U (Fi 0) ≠ 0 := hli.ne_zero 0
    obtain ⟨hr, β, hβ⟩ := subst_step U (Fi 0) h0 hU
    set U1 : Fin n0 → Fin m1 → Fin m2 → K := fun i u v => U i u v + β i * U (Fi 0) u v with hU1
    have hli1 : LinearIndependent K (fun l : Fin f => U1 (Fi l.succ)) := by
      rw [Fintype.linearIndependent_iff] at hli ⊢
      intro g hg
      have key := hli (Fin.cons (∑ l, g l * β (Fi l.succ)) g) (by
        funext u v
        have h1 := congrFun (congrFun hg u) v
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hU1] at h1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.sum_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
        rw [← h1, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun l _ => by ring))
      intro l
      have := key l.succ
      simpa using this
    obtain ⟨hf, α1, hα1⟩ := subst f (r - 1) U1 (fun l => Fi l.succ) Ri hli1 hβ
    refine ⟨by omega, fun s => Fin.cons (β (Ri s) + ∑ l, α1 s l * β (Fi l.succ)) (α1 s), ?_⟩
    have heq : usub U Fi Ri (fun s => Fin.cons (β (Ri s) + ∑ l, α1 s l * β (Fi l.succ)) (α1 s)) =
        usub U1 (fun l => Fi l.succ) Ri α1 := by
      funext s u v
      simp only [usub, hU1, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hs : ∑ l, α1 s l * (U (Fi l.succ) u v + β (Fi l.succ) * U (Fi 0) u v) =
          ∑ l, α1 s l * U (Fi l.succ) u v + (∑ l, α1 s l * β (Fi l.succ)) * U (Fi 0) u v := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun l _ => by ring)
      rw [hs]
      ring
    rw [heq, show r - (f + 1) = r - 1 - f by omega]
    exact hα1

end B334.MethodK
