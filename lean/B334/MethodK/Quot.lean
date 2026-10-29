import B334.MethodK.Subst

/-! # Method K, L-K0 and L-K1: the quotient map and the mode permutations

* L-K0 `quotLB_of_proj`: if `S ⊆ ker π` and every decomposition of `Q = (π ⊗ id ⊗ id) T` has at least `k` terms, then
  `QuotLB T S k`. The outside terms of a decomposition of `T` decompose `Q`; no quotient space is formed.
* L-K1 `rankLE_perm1`, `rankLE_perm2`: moving mode 1 or mode 2 first keeps the number of terms. -/

namespace B334.MethodK

open Finset

section quot

variable {n0 n1 n2 na : ℕ}

/-- `Q = (π ⊗ id ⊗ id) T` -/
def qproj (π : Matrix (Fin na) (Fin n0) (ZMod 2)) (T : Fin n0 → Fin n1 → Fin n2 → ZMod 2) :
    Fin na → Fin n1 → Fin n2 → ZMod 2 :=
  fun x y z => ∑ a, π x a * T a y z

/-- **L-K0.** -/
theorem quotLB_of_proj (T : Fin n0 → Fin n1 → Fin n2 → ZMod 2) (S : Submodule (ZMod 2) (Fin n0 → ZMod 2))
    (π : Matrix (Fin na) (Fin n0) (ZMod 2)) (hS : ∀ v ∈ S, π.mulVec v = 0) (k : ℕ)
    (h : ∀ r, RankLE (qproj π T) r → k ≤ r) : QuotLB T S k := by
  intro r a b c hT
  classical
  -- every term, mapped by π
  have hall : qproj π T = ∑ s, outer3 (π.mulVec (a s)) (b s) (c s) := by
    funext x y z
    simp only [qproj, outer3, Finset.sum_apply]
    have hTa : ∀ a' : Fin n0, T a' y z = ∑ s, a s a' * b s y * c s z := fun a' => tensor_apply_of_decomp hT a' y z
    simp only [hTa, Finset.mul_sum, Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a' _ => by ring)
  -- the terms inside S vanish
  have hout : qproj π T = ∑ s : {s : Fin r // a s ∉ S}, outer3 (π.mulVec (a s.1)) (b s.1) (c s.1) := by
    rw [hall, ← Fintype.sum_subtype_add_sum_subtype (fun s => a s ∉ S)]
    have hz : ∑ s : {s : Fin r // ¬ (a s ∉ S)}, outer3 (π.mulVec (a s.1)) (b s.1) (c s.1) = 0 := by
      refine Finset.sum_eq_zero (fun s _ => ?_)
      have hin : a s.1 ∈ S := not_not.mp s.2
      rw [hS _ hin]
      funext x y z; simp [outer3]
    rw [hz, add_zero]
  -- reindex the outside terms by Fin
  set I := {s : Fin r // a s ∉ S}
  let e := Fintype.equivFin I
  have hrank : RankLE (qproj π T) (Fintype.card I) := by
    refine ⟨fun j => π.mulVec (a (e.symm j).1), fun j => b (e.symm j).1, fun j => c (e.symm j).1, ?_⟩
    rw [hout]
    exact Fintype.sum_equiv e (fun s : I => outer3 (π.mulVec (a s.1)) (b s.1) (c s.1))
      (fun j => outer3 (π.mulVec (a (e.symm j).1)) (b (e.symm j).1) (c (e.symm j).1)) (fun s => by simp)
  rw [Nat.card_eq_fintype_card]
  exact h _ hrank

end quot

section perm

variable {K : Type*} [Field K] {n0 n1 n2 : ℕ}

/-- mode 1 first: `perm1 Q i u v = Q v i u` (p = 1) -/
def perm1 (Q : Fin n0 → Fin n1 → Fin n2 → K) : Fin n1 → Fin n2 → Fin n0 → K := fun i u v => Q v i u
/-- mode 2 first: `perm2 Q i u v = Q u v i` (p = 2) -/
def perm2 (Q : Fin n0 → Fin n1 → Fin n2 → K) : Fin n2 → Fin n0 → Fin n1 → K := fun i u v => Q u v i

/-- **L-K1**, p = 1. -/
theorem rankLE_perm1 (Q : Fin n0 → Fin n1 → Fin n2 → K) (r : ℕ) (h : RankLE Q r) : RankLE (perm1 Q) r := by
  obtain ⟨x, y, z, hxyz⟩ := h
  refine ⟨y, z, x, ?_⟩
  funext i u v
  simp only [perm1, outer3, Finset.sum_apply]
  rw [tensor_apply_of_decomp hxyz]
  exact Finset.sum_congr rfl (fun t _ => by ring)

/-- **L-K1**, p = 2. -/
theorem rankLE_perm2 (Q : Fin n0 → Fin n1 → Fin n2 → K) (r : ℕ) (h : RankLE Q r) : RankLE (perm2 Q) r := by
  obtain ⟨x, y, z, hxyz⟩ := h
  refine ⟨z, x, y, ?_⟩
  funext i u v
  simp only [perm2, outer3, Finset.sum_apply]
  rw [tensor_apply_of_decomp hxyz]
  exact Finset.sum_congr rfl (fun t _ => by ring)

end perm

end B334.MethodK
