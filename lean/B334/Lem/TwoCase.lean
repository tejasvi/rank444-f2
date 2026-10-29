import B334.Statement

/-! # L2: the two-case argument (`B334/Statement.lean` `TwoCase`)

Suppose T334 had a decomposition with 26 terms. By L1 the first-factor ranks add up to at least 36 > 26, so some term
`s₀` has rank 2 or 3. By L3b some `(P, Q) ∈ G₀` moves `a s₀` to mask 10 (mask 84), and by L3a the moved terms again
decompose T334. Term `s₀` now lies in `P707` (`P708`), so at most 25 first factors lie outside it (`card_notMem_lt`),
against `QuotLB T334 P707 26` (`QuotLB T334 P708 26`). -/

namespace B334.Lem

open B334 Finset

/-- if `a s₀ ∈ S`, fewer than `r` first factors lie outside `S` -/
theorem card_notMem_lt {r : ℕ} (a : Fin r → Fin (3 * 3) → ZMod 2) (S : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2))
    (s₀ : Fin r) (h : a s₀ ∈ S) : Nat.card {s : Fin r // a s ∉ S} < r := by
  classical
  rw [Nat.card_eq_fintype_card]
  calc Fintype.card {s : Fin r // a s ∉ S} < Fintype.card (Fin r) :=
        Fintype.card_subtype_lt (p := fun s => a s ∉ S) (x := s₀) (fun hn => hn h)
    _ = r := Fintype.card_fin r

/-- **L2** (`two_case`). -/
theorem two_case : TwoCase := by
  intro hL1 hSym hO2 hO3 h707 h708 hR
  obtain ⟨a, b, c, hT⟩ := hR
  have hsum := hL1 26 a b c hT
  -- some term has rank at least 2
  have hex : ∃ s, 2 ≤ (mat3 (a s)).rank := by
    by_contra hno
    push_neg at hno
    have h26 : ∑ s, (mat3 (a s)).rank ≤ 26 := by
      calc ∑ s, (mat3 (a s)).rank ≤ ∑ _s : Fin 26, 1 :=
            Finset.sum_le_sum (fun s _ => Nat.le_of_lt_succ (hno s))
        _ = 26 := by simp
    omega
  obtain ⟨s₀, hs₀⟩ := hex
  have hle : (mat3 (a s₀)).rank ≤ 3 := Matrix.rank_le_width _
  -- a G₀-image of the decomposition with first factor `s₀` in `S` contradicts `QuotLB T334 S 26`
  have key : ∀ S : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2), QuotLB T334 S 26 →
      ∀ P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2), P * Pi = 1 → Q * Qi = 1 → actA P Q (a s₀) ∈ S → False := by
    intro S hS P Q Pi Qi hP hQ hin
    have hT' := hSym P Q Pi Qi hP hQ 26 a b c hT
    have h1 := hS 26 _ _ _ hT'
    have h2 := card_notMem_lt (fun s => actA P Q (a s)) S s₀ hin
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl 26)
  rcases (show (mat3 (a s₀)).rank = 2 ∨ (mat3 (a s₀)).rank = 3 by omega) with h2 | h3
  · obtain ⟨P, Q, Pi, Qi, hP, hQ, hv⟩ := hO2 (a s₀) h2
    have hin : actA P Q (a s₀) ∈ P707 := by
      rw [hv, P707]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact key P707 h707 P Q Pi Qi hP hQ hin
  · obtain ⟨P, Q, Pi, Qi, hP, hQ, hv⟩ := hO3 (a s₀) h3
    have hin : actA P Q (a s₀) ∈ P708 := by
      rw [hv, P708]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact key P708 h708 P Q Pi Qi hP hQ hin

end B334.Lem
