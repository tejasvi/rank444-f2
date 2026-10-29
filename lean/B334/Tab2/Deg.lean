import B334.Bind.Rows

/-! # Monotone and degenerate rows

* `quotLB_mono` (L5a): a bound for a subspace holds for every smaller subspace (a first factor outside the larger one is
  outside the smaller one); `quotLB_le`: a bound holds for every smaller value.
* `quotLB_of_map_le`: if a G₀ element `g` maps `S` into `S'`, a bound for `S'` is one for `S` (apply `g` to the
  decomposition: a term with `a ∈ S` has `g a ∈ S'`). This needs only the inclusion, not `g S = S'`.
* `rowValid_deg` (L5b): a degenerate row `S` with extra vector `e` and a G₀ element mapping the generators of `S + ⟨e⟩`
  into a certified row `S_j` has every bound `b ≤ b_j`. -/

namespace B334.Tab2

open B334 B334.Bind

/-- **L5a.** -/
theorem quotLB_mono {S S' : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2)} (hle : S ≤ S') {k : ℕ}
    (h : QuotLB T334 S' k) : QuotLB T334 S k := by
  intro r a b c hT
  refine le_trans (h r a b c hT) (Nat.card_le_card_of_injective (fun x => ⟨x.1, fun hm => x.2 (hle hm)⟩) ?_)
  intro x y hxy
  apply Subtype.ext
  have h' := congrArg Subtype.val hxy
  simpa using h'

theorem quotLB_le {S : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2)} {k k' : ℕ} (hk : k' ≤ k) (h : QuotLB T334 S k) :
    QuotLB T334 S k' :=
  fun r a b c hT => le_trans hk (h r a b c hT)

/-- a G₀ element mapping `S` into `S'` carries a bound for `S'` back to `S` -/
theorem quotLB_of_map_le (P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hP : P * Pi = 1) (hQ : Q * Qi = 1)
    {S S' : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2)} (hle : S.map (actAL P Q) ≤ S') {k : ℕ}
    (h : QuotLB T334 S' k) : QuotLB T334 S k := by
  intro r a b c hT
  have hT' := sym334 P Q Pi Qi hP hQ r a b c hT
  refine le_trans (h r _ _ _ hT') (Nat.card_le_card_of_injective
    (fun x => ⟨x.1, fun hm => x.2 (hle (Submodule.mem_map.mpr ⟨a x.1, hm, rfl⟩))⟩) ?_)
  intro x y hxy
  apply Subtype.ext
  have h' := congrArg Subtype.val hxy
  simpa using h'

/-- **L5b.** A degenerate row: the G₀ element `(P, Q)` maps the generators of `S + ⟨e⟩` into `span Bj`, and
`RowValid Bj bj` with `b ≤ bj`. -/
theorem rowValid_deg {B Bj : List ℕ} {e b bj : ℕ} (P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hP : P * Pi = 1)
    (hQ : Q * Qi = 1) (himg : ∀ x ∈ B ++ [e], actA P Q (vecOfMask (3 * 3) x) ∈ spanMasks Bj)
    (hj : RowValid Bj bj) (hb : b ≤ bj) : RowValid B b := by
  have hle : (spanMasks (B ++ [e])).map (actAL P Q) ≤ spanMasks Bj := by
    unfold spanMasks
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨v, ⟨m, hm, rfl⟩, rfl⟩
    exact himg m hm
  have h1 : QuotLB T334 (spanMasks (B ++ [e])) bj := quotLB_of_map_le P Q Pi Qi hP hQ hle hj
  have h2 : spanMasks B ≤ spanMasks (B ++ [e]) := by
    apply Submodule.span_mono
    rintro v ⟨m, hm, rfl⟩
    exact ⟨m, List.mem_append_left _ hm, rfl⟩
  exact quotLB_le hb (quotLB_mono h2 h1)

end B334.Tab2
