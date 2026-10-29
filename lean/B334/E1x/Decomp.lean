import B334.E1x.Act
import B334.Core.Tensor334

/-! # Every element of G₀ maps decompositions of ⟨3,3,4⟩ to decompositions

Port of `C3/Decomp.lean` from the ⟨3,3,3⟩ release (`rank333-f2`, Apache-2.0) to `B334.Core.IsDecomp` (b 3×4, c 4×3).
For invertible `P, Q` (3×3):
* `(a, b, c) ↦ (P a, b, c P⁻¹)` (`isDecomp_left`) and `(a, b, c) ↦ (a Q, Q⁻¹ b, c)` (`isDecomp_mid`) keep
  decompositions, because `tr(P a b c P⁻¹) = tr(a b c)` and `tr(a Q Q⁻¹ b c) = tr(a b c)`; the middle index `k` (range 4)
  is untouched;
* so the first factors `toM3 (actF P Q (av s))` decompose with `b' = Q⁻¹ b`, `c' = c P⁻¹` (`isDecomp_actF`), which stay
  nonzero (`actF_nz`).
⟨3,3,3⟩'s transpose `(a, b, c) ↦ (aᵀ, cᵀ, bᵀ)` is not a symmetry of ⟨3,3,4⟩ and is not ported (`t = false`). -/

open Matrix

namespace B334.E1x

open B334.Core

theorem isDecomp_left {n : ℕ} {a : Fin n → M3} {b : Fin n → M34} {c : Fin n → M43} (hd : IsDecomp a b c)
    (P P' : M3) (hP : P * P' = 1) :
    IsDecomp (fun s => P * a s) b (fun s => c s * P') := by
  intro i j j' k k' i'
  simp only [Matrix.mul_apply]
  have e1 : ∀ s, (∑ p, P i p * a s p j) * b s j' k * (∑ u, c s k' u * P' u i') =
      ∑ p, ∑ u, (P i p * P' u i') * (a s p j * b s j' k * c s k' u) := by
    intro s
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun s _ => e1 s), Finset.sum_comm]
  have e2 : ∀ p, (∑ s, ∑ u, (P i p * P' u i') * (a s p j * b s j' k * c s k' u)) =
      ∑ u, (P i p * P' u i') * (if j = j' ∧ k = k' ∧ p = u then 1 else 0) := by
    intro p
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.mul_sum, hd p j j' k k' u]
  rw [Finset.sum_congr rfl (fun p _ => e2 p)]
  have hPP := congrFun (congrFun hP i) i'
  rw [Matrix.mul_apply] at hPP
  by_cases h : j = j' ∧ k = k'
  · have e3 : ∀ p, (∑ u, (P i p * P' u i') * (if j = j' ∧ k = k' ∧ p = u then (1 : F2) else 0)) =
        P i p * P' p i' := by
      intro p
      rw [Finset.sum_eq_single p]
      · rw [if_pos ⟨h.1, h.2, rfl⟩, mul_one]
      · intro u _ hu; rw [if_neg (fun h' => hu h'.2.2.symm), mul_zero]
      · intro hp; exact absurd (Finset.mem_univ p) hp
    rw [Finset.sum_congr rfl (fun p _ => e3 p), hPP, Matrix.one_apply]
    by_cases hi : i = i'
    · rw [if_pos hi, if_pos ⟨h.1, h.2, hi⟩]
    · rw [if_neg hi, if_neg (fun h' => hi h'.2.2)]
  · have e3 : ∀ p, (∑ u, (P i p * P' u i') * (if j = j' ∧ k = k' ∧ p = u then (1 : F2) else 0)) = 0 := by
      intro p
      apply Finset.sum_eq_zero
      intro u _
      rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), mul_zero]
    rw [Finset.sum_congr rfl (fun p _ => e3 p), Finset.sum_const_zero, if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]

theorem isDecomp_mid {n : ℕ} {a : Fin n → M3} {b : Fin n → M34} {c : Fin n → M43} (hd : IsDecomp a b c)
    (Q Q' : M3) (hQ : Q' * Q = 1) :
    IsDecomp (fun s => a s * Q) (fun s => Q' * b s) c := by
  intro i j j' k k' i'
  simp only [Matrix.mul_apply]
  have e1 : ∀ s, (∑ q, a s i q * Q q j) * (∑ r, Q' j' r * b s r k) * c s k' i' =
      ∑ q, ∑ r, (Q q j * Q' j' r) * (a s i q * b s r k * c s k' i') := by
    intro s
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun s _ => e1 s), Finset.sum_comm]
  have e2 : ∀ q, (∑ s, ∑ r, (Q q j * Q' j' r) * (a s i q * b s r k * c s k' i')) =
      ∑ r, (Q q j * Q' j' r) * (if q = r ∧ k = k' ∧ i = i' then 1 else 0) := by
    intro q
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.mul_sum, hd i q r k k' i']
  rw [Finset.sum_congr rfl (fun q _ => e2 q)]
  have hQQ := congrFun (congrFun hQ j') j
  rw [Matrix.mul_apply] at hQQ
  by_cases h : k = k' ∧ i = i'
  · have e3 : ∀ q, (∑ r, (Q q j * Q' j' r) * (if q = r ∧ k = k' ∧ i = i' then (1 : F2) else 0)) =
        Q' j' q * Q q j := by
      intro q
      rw [Finset.sum_eq_single q]
      · rw [if_pos ⟨rfl, h.1, h.2⟩, mul_one, mul_comm]
      · intro r _ hr; rw [if_neg (fun h' => hr h'.1.symm), mul_zero]
      · intro hq; exact absurd (Finset.mem_univ q) hq
    rw [Finset.sum_congr rfl (fun q _ => e3 q), hQQ, Matrix.one_apply]
    by_cases hj : j' = j
    · rw [if_pos hj, if_pos ⟨hj.symm, h.1, h.2⟩]
    · rw [if_neg hj, if_neg (fun h' => hj h'.1.symm)]
  · have e3 : ∀ q, (∑ r, (Q q j * Q' j' r) * (if q = r ∧ k = k' ∧ i = i' then (1 : F2) else 0)) = 0 := by
      intro q
      apply Finset.sum_eq_zero
      intro r _
      rw [if_neg (fun h' => h ⟨h'.2.1, h'.2.2⟩), mul_zero]
    rw [Finset.sum_congr rfl (fun q _ => e3 q), Finset.sum_const_zero, if_neg (fun h' => h ⟨h'.2.1, h'.2.2⟩)]

/-- **Decomposition transport.** If the first factors `toM3 (av s)` belong to a decomposition `(b, c)`, the first factors
`toM3 (actF P Q (av s))` belong to the decomposition `(Q⁻¹ b, c P⁻¹)`, for every invertible `P`, `Q`. -/
theorem isDecomp_actF {n : ℕ} {av : Fin n → ℕ} {b : Fin n → M34} {c : Fin n → M43}
    (hd : IsDecomp (fun s => toM3 (av s)) b c) {P Q : Nat} (hP : isGL P = true) (hQ : isGL Q = true) :
    IsDecomp (fun s => toM3 (actF P Q (av s))) (fun s => toM3 (invN Q) * b s) (fun s => c s * toM3 (invN P)) := by
  obtain ⟨hP1, -⟩ := gl_inv hP
  obtain ⟨-, hQ2⟩ := gl_inv hQ
  have h := isDecomp_mid (isDecomp_left hd (toM3 P) (toM3 (invN P)) hP1) (toM3 Q) (toM3 (invN Q)) hQ2
  simp only [toM3_actF]
  exact h

/-- the moved second and third factors stay nonzero -/
theorem actF_nz {n : ℕ} {b : Fin n → M34} {c : Fin n → M43} (hbc : ∀ s, b s ≠ 0 ∧ c s ≠ 0) {P Q : Nat}
    (hP : isGL P = true) (hQ : isGL Q = true) :
    ∀ s, toM3 (invN Q) * b s ≠ 0 ∧ c s * toM3 (invN P) ≠ 0 := by
  obtain ⟨-, hP2⟩ := gl_inv hP
  obtain ⟨hQ1, -⟩ := gl_inv hQ
  intro s
  constructor
  · intro h0; apply (hbc s).1
    calc b s = (toM3 Q * toM3 (invN Q)) * b s := by rw [hQ1, Matrix.one_mul]
      _ = toM3 Q * (toM3 (invN Q) * b s) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  · intro h0; apply (hbc s).2
    calc c s = c s * (toM3 (invN P) * toM3 P) := by rw [hP2, Matrix.mul_one]
      _ = (c s * toM3 (invN P)) * toM3 P := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.zero_mul]

end B334.E1x
