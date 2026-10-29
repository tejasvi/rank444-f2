import B334.Bind.Sym
import B334.Bind.Span

/-! # Table binding: transport of a row bound along G₀

A table row proves `QuotLB T334 (spanMasks basis) lb` for its class representative. An IP row or a coset row cites the
image subspace `actA P Q '' S`. `quotLB_transport`: QuotLB is invariant under the G₀ action on the first factor
(`sym334` maps decompositions to decompositions, and `a ∉ g S ↔ g⁻¹ a ∉ S`). -/

namespace B334.Bind

open Finset

theorem mat3_add (v w : Fin (3 * 3) → ZMod 2) : mat3 (v + w) = mat3 v + mat3 w := by
  ext i j; simp [mat3]
theorem mat3_smul (c : ZMod 2) (v : Fin (3 * 3) → ZMod 2) : mat3 (c • v) = c • mat3 v := by
  ext i j; simp [mat3]

/-- `actA P Q` as a linear map of the first factor -/
def actAL (P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) : (Fin (3 * 3) → ZMod 2) →ₗ[ZMod 2] (Fin (3 * 3) → ZMod 2) where
  toFun := actA P Q
  map_add' v w := by
    funext x
    simp only [actA, mat3_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]
  map_smul' c v := by
    funext x
    simp only [actA, mat3_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply,
      RingHom.id_apply]

theorem actAL_apply (P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin (3 * 3) → ZMod 2) :
    actAL P Q v = actA P Q v := rfl

theorem mat3_actA (P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin (3 * 3) → ZMod 2) :
    mat3 (actA P Q v) = P * mat3 v * Q := by
  ext i j; simp [mat3, actA, Equiv.symm_apply_apply]

theorem actA_actA (P Q P' Q' : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin (3 * 3) → ZMod 2) :
    actA P' Q' (actA P Q v) = actA (P' * P) (Q * Q') v := by
  funext x
  simp only [actA, mat3_actA, Matrix.mul_assoc]

theorem actA_one (v : Fin (3 * 3) → ZMod 2) : actA 1 1 v = v := by
  funext x
  simp only [actA, Matrix.one_mul, Matrix.mul_one, mat3, Matrix.of_apply, Prod.mk.eta, Equiv.apply_symm_apply]

/-- **Transport.** If `P Pi = 1` and `Q Qi = 1`, a bound for `S` gives the same bound for its image. -/
theorem quotLB_transport (P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hP : P * Pi = 1) (hQ : Q * Qi = 1)
    (S : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2)) (k : ℕ) (h : QuotLB T334 S k) :
    QuotLB T334 (S.map (actAL P Q)) k := by
  intro r a b c hT
  have hP' : Pi * P = 1 := mul_eq_one_comm.mp hP
  have hQ' : Qi * Q = 1 := mul_eq_one_comm.mp hQ
  have hT' := sym334 Pi Qi P Q hP' hQ' r a b c hT
  have hk := h r _ _ _ hT'
  have hiff : ∀ s, actA Pi Qi (a s) ∉ S ↔ a s ∉ S.map (actAL P Q) := by
    intro s
    constructor
    · intro hn hm
      obtain ⟨w, hw, he⟩ := Submodule.mem_map.mp hm
      rw [actAL_apply] at he
      apply hn
      rw [← he, actA_actA, hP', hQ, actA_one]
      exact hw
    · intro hn hm
      apply hn
      refine Submodule.mem_map.mpr ⟨actA Pi Qi (a s), hm, ?_⟩
      rw [actAL_apply, actA_actA, hP, hQ', actA_one]
  calc k ≤ Nat.card {s : Fin r // actA Pi Qi (a s) ∉ S} := hk
    _ = Nat.card {s : Fin r // a s ∉ S.map (actAL P Q)} := Nat.card_congr (Equiv.subtypeEquivRight hiff)

end B334.Bind
