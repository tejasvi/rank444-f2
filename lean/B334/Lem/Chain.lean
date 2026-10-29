import B334.MethodK.Cert

/-! # L6: the chain to ⟨3,4,4⟩ and ⟨4,4,4⟩ (`B334/Statement.lean` `ChainStep`, `Cyclic`,
`Chain344`, `Chain444`)

* `mmT_apply`: the entries of ⟨n,m,p⟩ in matrix indices (`finProdFinEquiv`), for every format.
* L6b `cyclic`: `mmT m p n = perm1 (mmT n m p)`, and `MethodK.rankLE_perm1` keeps the number of terms.
* L6a `chain_step`: for `n, m ≥ 1`, move the second factor first (`perm1`). Its `m` slices `(j, p)` (the last column of
  the second matrix) are independent: at the positions `(z, x) = ((p, 0), (0, j))` they form the identity matrix
  (`MethodK.linIndep_of_inv`). L-K2 (`MethodK.subst`, iterated substitution) removes `m` terms;
  every added slice lives on row `p` of the third matrix, so restricting the third factor to rows `k < p`
  (`rankLE_restrict1` with `cRow`) leaves `perm1 (mmT n m p)`, and `perm2` moves the factors back. For `n = 0` or
  `m = 0` the first factor has no coordinates (`rankLE_of_isEmpty`).
* L6c `chain344`, `chain444`: `⟨3,4,4⟩` with 30 = 26 + 4 terms gives `⟨3,4,3⟩`, `⟨4,3,3⟩`, `⟨3,3,4⟩` with 26; `⟨4,4,4⟩`
  with 34 = 30 + 4 gives `⟨4,4,3⟩`, `⟨4,3,4⟩`, `⟨3,4,4⟩` with 30. -/

namespace B334.Lem

open B334 Finset

theorem fpf_div {a b : ℕ} (x : Fin a) (y : Fin b) : (finProdFinEquiv (x, y)).val / b = x.val := by
  rw [finProdFinEquiv_apply_val]
  show (y.val + b * x.val) / b = x.val
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt y.isLt), Nat.div_eq_of_lt y.isLt, Nat.zero_add]

theorem fpf_mod {a b : ℕ} (x : Fin a) (y : Fin b) : (finProdFinEquiv (x, y)).val % b = y.val := by
  rw [finProdFinEquiv_apply_val]
  show (y.val + b * x.val) % b = y.val
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]

/-- the entries of ⟨n,m,p⟩ in matrix indices -/
theorem mmT_apply {n m p : ℕ} (i : Fin n) (j j' : Fin m) (k k' : Fin p) (i' : Fin n) :
    mmT n m p (finProdFinEquiv (i, j)) (finProdFinEquiv (j', k)) (finProdFinEquiv (k', i')) =
      if j = j' ∧ k = k' ∧ i' = i then 1 else 0 := by
  simp only [mmT]
  apply if_congr _ rfl rfl
  simp only [fpf_mod, fpf_div, Fin.val_inj]

/-! ## L6b: cyclic invariance -/

theorem mmT_cyclic (n m p : ℕ) : mmT m p n = MethodK.perm1 (mmT n m p) := by
  funext y z x
  simp only [mmT, MethodK.perm1]
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3, h1, h2⟩
  · rintro ⟨g1, g2, g3⟩
    exact ⟨g2, g3, g1⟩

/-- **L6b** (`cyclic`). -/
theorem cyclic : Cyclic := by
  intro n m p r h
  rw [mmT_cyclic]
  exact MethodK.rankLE_perm1 _ r h

/-! ## L6a: the chain step -/

/-- a tensor whose first factor has no coordinates has a decomposition of any length -/
theorem rankLE_of_isEmpty {n₀ n₁ n₂ : ℕ} (T : Fin n₀ → Fin n₁ → Fin n₂ → ZMod 2) (h : n₀ = 0) (r : ℕ) :
    RankLE T r := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  funext x
  exact absurd x.isLt (by omega)

/-- restricting the middle factor to some coordinates keeps the number of terms -/
theorem rankLE_restrict1 {n₀ n₁ n₁' n₂ : ℕ} {V : Fin n₀ → Fin n₁ → Fin n₂ → ZMod 2} {r : ℕ} (h : RankLE V r)
    (f : Fin n₁' → Fin n₁) : RankLE (fun s u v => V s (f u) v) r := by
  obtain ⟨x, y, z, hxyz⟩ := h
  refine ⟨x, fun t u => y t (f u), z, ?_⟩
  funext s u v
  rw [MethodK.tensor_apply_of_decomp hxyz]
  simp [outer3, Finset.sum_apply]

/-- the slice `(j, p)` of the second factor of ⟨n,m,p+1⟩ (last column of the second matrix) -/
def fSl {m p : ℕ} (j : Fin m) : Fin (m * (p + 1)) := finProdFinEquiv (j, Fin.last p)
/-- the slice `(j, k)` (`k < p`) of the second factor of ⟨n,m,p+1⟩, indexed as in ⟨n,m,p⟩ -/
def rSl {m p : ℕ} (y : Fin (m * p)) : Fin (m * (p + 1)) :=
  finProdFinEquiv ((finProdFinEquiv.symm y).1, Fin.castSucc (finProdFinEquiv.symm y).2)
/-- the coordinate `(k, i)` (`k < p`) of the third factor of ⟨n,m,p+1⟩, indexed as in ⟨n,m,p⟩ -/
def cRow {n p : ℕ} (z : Fin (p * n)) : Fin ((p + 1) * n) :=
  finProdFinEquiv (Fin.castSucc (finProdFinEquiv.symm z).1, (finProdFinEquiv.symm z).2)

/-- **L6a** (`chain_step`). -/
theorem chain_step : ChainStep := by
  intro n m p r h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact rankLE_of_isEmpty _ (by rw [hn, Nat.zero_mul]) r
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact rankLE_of_isEmpty _ (by rw [hm, Nat.mul_zero]) r
  have i0 : Fin n := ⟨0, hn⟩
  -- the `m` forced slices give the identity matrix at the positions `(z, x) = ((p, i0), (i0, j))`
  have hG : (1 : Matrix (Fin m) (Fin m) (ZMod 2)) * (Matrix.of fun l j =>
      MethodK.perm1 (mmT n m (p + 1)) (fSl l) (finProdFinEquiv (Fin.last p, i0)) (finProdFinEquiv (i0, j))) = 1 := by
    rw [Matrix.one_mul]
    ext l j
    simp only [Matrix.of_apply, MethodK.perm1, fSl, mmT_apply, Matrix.one_apply]
    by_cases hlj : l = j
    · subst hlj
      simp
    · have hjl : ¬ j = l := fun e => hlj e.symm
      simp [hlj, hjl]
  have hli := MethodK.linIndep_of_inv (MethodK.perm1 (mmT n m (p + 1))) fSl
    (fun _ => finProdFinEquiv (Fin.last p, i0)) (fun j => finProdFinEquiv (i0, j)) 1 hG
  obtain ⟨-, α, hα⟩ := MethodK.subst m (r + m) (MethodK.perm1 (mmT n m (p + 1))) fSl rSl hli
    (MethodK.rankLE_perm1 _ _ h)
  rw [Nat.add_sub_cancel] at hα
  -- on rows `k < p` of the third matrix the forced slices vanish and the rest is ⟨n,m,p⟩
  have heq : (fun s u v => MethodK.usub (MethodK.perm1 (mmT n m (p + 1))) fSl rSl α s (cRow u) v) =
      MethodK.perm1 (mmT n m p) := by
    funext s u v
    obtain ⟨⟨j', k⟩, rfl⟩ := finProdFinEquiv.surjective s
    obtain ⟨⟨k', i'⟩, rfl⟩ := finProdFinEquiv.surjective u
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective v
    have hne : Fin.last p ≠ Fin.castSucc k' := (Fin.castSucc_lt_last k').ne'
    have hz : ∀ l, MethodK.perm1 (mmT n m (p + 1)) (fSl l) (cRow (finProdFinEquiv (k', i')))
        (finProdFinEquiv (i, j)) = 0 := by
      intro l
      simp only [MethodK.perm1, fSl, cRow, Equiv.symm_apply_apply]
      rw [mmT_apply, if_neg]
      rintro ⟨-, h2, -⟩
      exact hne h2
    simp only [MethodK.usub, hz, mul_zero, Finset.sum_const_zero, add_zero]
    simp only [MethodK.perm1, rSl, cRow, Equiv.symm_apply_apply, mmT_apply, Fin.castSucc_inj]
  have h1 : RankLE (MethodK.perm1 (mmT n m p)) r := by
    rw [← heq]
    exact rankLE_restrict1 hα cRow
  exact MethodK.rankLE_perm2 _ r h1

/-! ## L6c: the corollaries -/

/-- **L6c** (`chain344`): R(⟨3,3,4⟩) ≥ 27 gives R(⟨3,4,4⟩) ≥ 31. -/
theorem chain344 : Chain344 := by
  intro hstep hcyc h334 h344
  exact h334 (hcyc 4 3 3 26 (hcyc 3 4 3 26 (hstep 3 4 3 26 h344)))

/-- **L6c** (`chain444`): R(⟨3,4,4⟩) ≥ 31 gives R(⟨4,4,4⟩) ≥ 35. -/
theorem chain444 : Chain444 := by
  intro hstep hcyc h344 h444
  exact h344 (hcyc 4 3 4 30 (hcyc 4 4 3 30 (hstep 4 4 3 30 h444)))

end B334.Lem
