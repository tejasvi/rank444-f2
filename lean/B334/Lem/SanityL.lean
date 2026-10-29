import B334.Sanity
import B334.Lem.Chain

/-! # The non-vacuity facts of `B334/Sanity.lean`: proofs

* NV1 `rankLE_29`: the rank-29 scheme `scheme29` rebuilds T334. Entry `(x, y, z)` of `∑ₛ aₛ ⊗ bₛ ⊗ cₛ` is the parity of
  the terms whose three masks have bits `x`, `y`, `z` (`entryN`, a Boolean fold over the list); `nv1_check`
  (`decide +kernel`) compares the 1,296 entries with T334 (`tgtN`). `sum_getD` turns the sum over `Fin 29` into a list
  sum and `zb_entryN` turns that into the fold, so no `Finset.sum` is evaluated by the kernel.
* NVnaive `rankLE_naive`: ⟨n,m,p⟩ is the sum of the n·m·p terms `e_{(i,j)} ⊗ e_{(j,k)} ⊗ e_{(k,i)}`, term
  `s = ((i, j), k)` through `finProdFinEquiv`; the sums are split by `sum_fpf` and each entry is a Kronecker delta.
* NV2 `trace_identity`: with the sums split by `sum_fpf`, the Kronecker deltas of `mmT_apply` (`Lem/Chain.lean`) leave
  `∑ᵢ ∑ⱼ ∑ₖ Xᵢⱼ Yⱼₖ Zₖᵢ = tr(XYZ)`. -/

namespace B334.Lem

open B334 B334.MethodK Finset

/-! ## Sums over `Fin (a * b)` and over lists -/

theorem sum_fpf {a b : ℕ} (F : Fin (a * b) → ZMod 2) :
    ∑ x, F x = ∑ i : Fin a, ∑ j : Fin b, F (finProdFinEquiv (i, j)) := by
  rw [← Equiv.sum_comp finProdFinEquiv F, Fintype.sum_prod_type]

theorem sum_getD {α : Type*} (L : List α) (d : α) (g : α → ZMod 2) {N : ℕ} (hN : L.length = N) :
    ∑ s : Fin N, g (L.getD s d) = (L.map g).sum := by
  subst hN
  induction L with
  | nil => simp
  | cons t L ih =>
    show ∑ s : Fin (L.length + 1), g ((t :: L).getD s d) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ, ih, List.map_cons,
      List.sum_cons]

/-! ## NV1: the rank-29 scheme -/

/-- entry `(x, y, z)` of `∑ₛ aₛ ⊗ bₛ ⊗ cₛ` for a list of mask triples `(aₛ, bₛ, cₛ)`, as a parity -/
def entryN : List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ → Bool
  | [], _, _, _ => false
  | t :: L, x, y, z => xor (t.1.testBit x && t.2.1.testBit y && t.2.2.testBit z) (entryN L x y z)

/-- entry `(x, y, z)` of T334 (`mmT 3 3 4`) -/
def tgtN (x y z : ℕ) : Bool := decide (x % 3 = y / 4 ∧ y % 4 = z / 3 ∧ z % 3 = x / 3)

theorem nv1_check : ∀ x < 9, ∀ y < 12, ∀ z < 12, entryN scheme29 x y z = tgtN x y z := by
  decide +kernel

theorem zb_entryN (L : List (ℕ × ℕ × ℕ)) (x y z : ℕ) :
    zb (entryN L x y z) = (L.map (fun t => zbit t.1 x * zbit t.2.1 y * zbit t.2.2 z)).sum := by
  induction L with
  | nil => simp [entryN, zb]
  | cons t L ih =>
    simp only [entryN, zb_xor, zb_and, ih, List.map_cons, List.sum_cons, zbit]

theorem T334_eq_zb (x : Fin (3 * 3)) (y : Fin (3 * 4)) (z : Fin (4 * 3)) :
    T334 x y z = zb (tgtN x.val y.val z.val) := by
  simp only [T334, mmT, tgtN, zb, decide_eq_true_eq]

/-- **NV1** (`rankLE_29`). -/
theorem rankLE_29 : NV1 := by
  refine ⟨fun s => vecOfMask (3 * 3) (scheme29.getD s (0, 0, 0)).1,
    fun s => vecOfMask (3 * 4) (scheme29.getD s (0, 0, 0)).2.1,
    fun s => vecOfMask (4 * 3) (scheme29.getD s (0, 0, 0)).2.2, ?_⟩
  funext x y z
  have h := sum_getD (N := 29) scheme29 (0, 0, 0)
    (fun t => zbit t.1 x.val * zbit t.2.1 y.val * zbit t.2.2 z.val) rfl
  rw [← zb_entryN, nv1_check x.val x.isLt y.val y.isLt z.val z.isLt, ← T334_eq_zb] at h
  rw [← h]
  simp only [Finset.sum_apply, outer3]
  rfl

/-! ## NVnaive: the standard algorithm -/

/-- **NVnaive** (`rankLE_naive`). -/
theorem rankLE_naive : NVnaive := by
  intro n m p
  refine ⟨fun s x => if x = (finProdFinEquiv.symm s).1 then 1 else 0,
    fun s y => if y = finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm s).1).2,
      (finProdFinEquiv.symm s).2) then 1 else 0,
    fun s z => if z = finProdFinEquiv ((finProdFinEquiv.symm s).2,
      (finProdFinEquiv.symm (finProdFinEquiv.symm s).1).1) then 1 else 0, ?_⟩
  funext x y z
  obtain ⟨⟨i0, j0⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j1, k1⟩, rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨k2, i2⟩, rfl⟩ := finProdFinEquiv.surjective z
  rw [mmT_apply]
  simp only [Finset.sum_apply, outer3, sum_fpf, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq]
  rw [Finset.sum_eq_single i0]
  · rw [Finset.sum_eq_single j0]
    · rw [Finset.sum_eq_single k1]
      · by_cases h1 : j0 = j1
        · subst h1
          by_cases h2 : k1 = k2
          · subst h2
            by_cases h3 : i2 = i0
            · subst h3
              simp
            · simp [h3]
          · simp [h2, Ne.symm h2]
        · simp [h1, Ne.symm h1]
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro k _
      simp [Ne.symm hj]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    simp [Ne.symm hi]
  · simp

/-! ## NV2: the trace identity -/

/-- **NV2** (`trace_identity`). -/
theorem trace_identity : NV2 := by
  intro n m p X Y Z
  have hR : Matrix.trace (X * Y * Z) = ∑ i, ∑ j, ∑ k, X i j * Y j k * Z k i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  rw [hR]
  simp only [sum_fpf, Equiv.symm_apply_apply, mmT_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hi'
        simp [hi']
      · simp
    · intro k' _ hk'
      apply Finset.sum_eq_zero
      intro i' _
      simp [Ne.symm hk']
    · simp
  · intro j' _ hj'
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro k' _
    apply Finset.sum_eq_zero
    intro i' _
    simp [Ne.symm hj']
  · simp

end B334.Lem
