import B334.E1x.Decomp
import B334.Bind.Sym
import B334.Bind.Rows

/-! # Row facts on 9-bit codes for ⟨3,3,4⟩, and their link with `QuotLB`

Port of `RT.Fact` (`RT/Sound.lean`) and `RT.FactN` (`RT/SoundN.lean`) from the ⟨3,3,3⟩ release (`rank333-f2`,
Apache-2.0) to `B334.Core.IsDecomp` (second factors 3×4, third factors 4×3, `B334/Core/Tensor334.lean`).

* `Fact m k`: every decomposition of ⟨3,3,4⟩ whose first factors are given by 9-bit codes `av s` has at least `k` terms
  whose code is outside the 512-bit point mask `m`. This is the form the E1 checkers' soundness proofs use.
* `fact_mono`, `fact_factN`, and `fact_actF` (transport along G₀ on codes, `E1x/Decomp.lean`).
* The link with the statement's form (`B334/Statement.lean`, decompositions as sums of `outer3`):
  `T334_of_isDecomp` and `isDecomp_of_T334` translate decompositions; `fact_of_quotLB` and `quotLB_of_fact` translate the
  bounds, for a mask `m` whose bits are exactly the vectors of the subspace `S` (`hm`). -/

open Matrix Finset

namespace B334.E1x

open B334.Core

/-- `m` has bound `k` (9-bit codes for the first factors) -/
def Fact (m k : Nat) : Prop := ∀ (n : ℕ) (av : Fin n → ℕ) (b : Fin n → M34) (c : Fin n → M43), (∀ s, av s < 512) →
  IsDecomp (fun s => toM3 (av s)) b c → k ≤ (univ.filter (fun s => m.testBit (av s) = false)).card

theorem fact_mono {m m' k k' : Nat} (hk : k' ≤ k)
    (hm : ∀ w, w < 512 → m'.testBit w = true → m.testBit w = true) (h : Fact m k) : Fact m' k' := by
  intro n av b c hav hd
  refine le_trans hk (le_trans (h n av b c hav hd) (Finset.card_le_card ?_))
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  cases e : m'.testBit (av s)
  · rfl
  · rw [hm _ (hav s) e] at hs; exact absurd hs (by decide)

/-- `m` has bound `k` for decompositions with exactly `R` terms whose codes are distinct and nonzero -/
def FactN (R m k : Nat) : Prop := ∀ (av : Fin R → ℕ) (b : Fin R → M34) (c : Fin R → M43), (∀ s, av s < 512) →
  (∀ s, av s ≠ 0) → Function.Injective av → IsDecomp (fun s => toM3 (av s)) b c →
    k ≤ (univ.filter (fun s => m.testBit (av s) = false)).card

theorem fact_factN {m k : Nat} (R : Nat) (h : Fact m k) : FactN R m k :=
  fun av b c hav _ _ hd => h R av b c hav hd

/-- **Transport along G₀.** If the element `(P, Q)` maps every code of `m'` into `m`, a bound for `m` is one for `m'`. -/
theorem fact_actF {m m' k : Nat} {P Q : Nat} (hP : isGL P = true) (hQ : isGL Q = true)
    (hmap : ∀ w < 512, m'.testBit w = true → m.testBit (actF P Q w) = true) (h : Fact m k) : Fact m' k := by
  intro n av b c hav hd
  refine le_trans (h n (fun s => actF P Q (av s)) _ _ (fun s => actF_lt _ _ _) (isDecomp_actF hd hP hQ))
    (Finset.card_le_card ?_)
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  cases e : m'.testBit (av s)
  · rfl
  · rw [hmap _ (hav s) e] at hs; exact absurd hs (by decide)

/-! ## The statement's decompositions and `IsDecomp` -/

/-- a 3×3 matrix as a statement vector (coordinate `3i+j`, as `mat3`) -/
def vecA (x : M3) : Fin (3 * 3) → ZMod 2 := fun p => x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
/-- a 3×4 matrix as a statement vector (coordinate `4j+k`, as `mat34`) -/
def vecB34 (x : M34) : Fin (3 * 4) → ZMod 2 := fun p => x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
/-- a 4×3 matrix as a statement vector (coordinate `3k+i`, as `mat43`) -/
def vecC43 (x : M43) : Fin (4 * 3) → ZMod 2 := fun p => x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

/-- `IsDecomp` gives a decomposition in the statement's form -/
theorem T334_of_isDecomp {n : ℕ} {a : Fin n → M3} {b : Fin n → M34} {c : Fin n → M43} (hd : IsDecomp a b c) :
    T334 = ∑ s, outer3 (vecA (a s)) (vecB34 (b s)) (vecC43 (c s)) := by
  funext x y z
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j', k⟩, rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨k', i'⟩, rfl⟩ := finProdFinEquiv.surjective z
  rw [T334_apply]
  simp only [outer3, Finset.sum_apply, vecA, vecB34, vecC43, Equiv.symm_apply_apply]
  have h := hd i j j' k k' i'
  by_cases hc : j = j' ∧ k = k' ∧ i = i'
  · rw [if_pos hc] at h
    rw [if_pos ⟨hc.1, hc.2.1, hc.2.2.symm⟩]
    exact h.symm
  · rw [if_neg hc] at h
    rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1, h'.2.2.symm⟩)]
    exact h.symm

/-- a decomposition in the statement's form gives `IsDecomp` -/
theorem isDecomp_of_T334 {r : ℕ} {a : Fin r → Fin (3 * 3) → ZMod 2} {b : Fin r → Fin (3 * 4) → ZMod 2}
    {c : Fin r → Fin (4 * 3) → ZMod 2} (hT : T334 = ∑ s, outer3 (a s) (b s) (c s)) :
    IsDecomp (fun s => (mat3 (a s) : M3)) (fun s => (mat34 (b s) : M34)) (fun s => (mat43 (c s) : M43)) := by
  intro i j j' k k' i'
  have h := entry_of_decomp hT i j j' k k' i'
  by_cases hc : j = j' ∧ k = k' ∧ i = i'
  · rw [if_pos ⟨hc.1, hc.2.1, hc.2.2.symm⟩] at h
    rw [if_pos hc]
    exact h
  · rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1, h'.2.2.symm⟩)] at h
    rw [if_neg hc]
    exact h

theorem vecA_toM3 (v : ℕ) : vecA (toM3 v) = vecOfMask (3 * 3) v := by
  funext p
  have e : 3 * (finProdFinEquiv.symm p).1.val + (finProdFinEquiv.symm p).2.val = p.val := by
    simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat]
    omega
  show (if v.testBit (3 * (finProdFinEquiv.symm p).1.val + (finProdFinEquiv.symm p).2.val) then (1 : F2) else 0) =
    (if v.testBit p.val then (1 : ZMod 2) else 0)
  rw [e]
  rfl

theorem mat3_vecOfMask (w : ℕ) : (mat3 (vecOfMask (3 * 3) w) : M3) = toM3 w := by
  ext i j
  have e : (finProdFinEquiv (i, j)).val = 3 * i.val + j.val := by
    rw [finProdFinEquiv_apply_val]
    dsimp only
    omega
  show (if w.testBit (finProdFinEquiv (i, j)).val then (1 : ZMod 2) else 0) =
    (if w.testBit (3 * i.val + j.val) then (1 : F2) else 0)
  rw [e]
  rfl

/-! ## Bounds: `QuotLB` and `Fact` -/

/-- a `QuotLB` bound is a `Fact` for the point mask of the subspace -/
theorem fact_of_quotLB {S : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2)} {m k : ℕ} (h : QuotLB T334 S k)
    (hm : ∀ w < 512, m.testBit w = true ↔ vecOfMask (3 * 3) w ∈ S) : Fact m k := by
  classical
  intro n av b c hav hd
  have hk := h n _ _ _ (T334_of_isDecomp hd)
  simp only [vecA_toM3] at hk
  refine le_trans hk (le_of_eq ?_)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hm (av s) (hav s)]
  cases m.testBit (av s) <;> simp

/-- a `Fact` for the point mask of a subspace is a `QuotLB` bound -/
theorem quotLB_of_fact {S : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2)} {m k : ℕ} (h : Fact m k)
    (hm : ∀ w < 512, m.testBit w = true ↔ vecOfMask (3 * 3) w ∈ S) : QuotLB T334 S k := by
  classical
  intro r a b c hT
  have hd := isDecomp_of_T334 hT
  choose av hav hva using fun s => B334.Bind.exists_mask (a s)
  have hav' : ∀ s, av s < 512 := fun s => lt_of_lt_of_eq (hav s) (by norm_num)
  have hA : (fun s => (mat3 (a s) : M3)) = fun s => toM3 (av s) := by
    funext s
    rw [← hva s, mat3_vecOfMask]
  rw [hA] at hd
  refine le_trans (h r av _ _ hav' hd) (le_of_eq ?_)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hva s, ← hm (av s) (hav' s)]
  cases m.testBit (av s) <;> simp

end B334.E1x
