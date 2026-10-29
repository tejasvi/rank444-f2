import B334.Bind.Row44C0
import B334.Bind.Row44C1
import B334.Bind.Row44C2
import B334.Bind.Row44C3
import B334.Bind.Row44C4
import B334.Bind.Row44C5
import B334.Bind.Row44C6
import B334.Bind.Row44C7
import B334.MethodK.Coset

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # Row 44 by the coset-count lemma

S = span [1, 2, 8, 20, 68, 256] (class 44, lb 18) has 7 nonzero cosets `c`. Each `S_c = span (basis ++ [c])` is a
G₀-image of a table class:
class 7 (lb 8, a flattening row) for c = 4; class 13 (lb 16, method K) for c = 32, 36, 128, 132; class 16 (lb 16,
method K) for c = 160, 164. Each image is checked on masks (`map_spanMasks_eq`), the bound moves along G₀
(`quotLB_transport`), every vector outside S lies in exactly one `S_c` (`existsUnique_of_certs`, from the per-mask
certificates of `Row44Certs`, checked 64 masks per module in `Row44C0` … `Row44C7`), and `quotLB_coset_count` gives
`6 r ≥ 8 + 6·16 = 104`, so `r ≥ 18`. Negative control: the same count cannot give 19 (`no19`: 6·18 = 108 > 104).
`basis`, `cs` and `ClN` (the generators of S_c by a natural-number index) are defined in `Row44Certs`.

`row44_of` takes the three class rows as hypotheses, so this module does not depend on their kernel facts; the final
`B334.Row44.row` (module `Row44Final`) supplies `R7.row`, `R13.row` and `R16.row`. -/

namespace B334.Row44

open B334 B334.Bind B334.MethodK Finset

def lbs : List ℕ := [8, 16, 16, 16, 16, 16, 16]
def cb7 : List ℕ := [1, 2, 4, 8, 16, 64, 256]
def cb13 : List ℕ := [1, 2, 8, 20, 32, 68, 128]
def cb16 : List ℕ := [1, 2, 8, 20, 68, 160, 256]
def cbs : List (List ℕ) := [cb7, cb13, cb13, cb13, cb13, cb16, cb16]
def Ps : List ℕ := [161, 266, 267, 161, 161, 273, 273]
def Qs : List ℕ := [161, 161, 161, 266, 267, 273, 281]
def Pis : List ℕ := [161, 266, 282, 161, 161, 273, 273]
def Qis : List ℕ := [161, 161, 161, 266, 282, 273, 281]
def imgs : List (List ℕ) := [[1, 4, 2, 64, 256, 8, 16], [8, 32, 1, 20, 2, 80, 256], [9, 36, 1, 22, 2, 82, 256],
  [2, 1, 128, 68, 256, 20, 8], [3, 1, 192, 68, 256, 28, 8], [1, 2, 8, 20, 68, 160, 256], [1, 3, 8, 28, 68, 224, 256]]
def invimgs : List (List ℕ) := [[1, 4, 64, 258, 10, 16, 2], [8, 32, 1, 20, 80, 128, 2], [8, 32, 9, 52, 80, 128, 2],
  [2, 1, 128, 68, 20, 32, 8], [2, 3, 128, 196, 20, 32, 28], [1, 2, 8, 20, 68, 256, 160], [1, 3, 8, 28, 68, 256, 228]]

/-- the coset spaces `S_c` -/
def Cl (i : Fin 7) : List ℕ := ClN i.val
def Sc (i : Fin 7) : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2) := spanMasks (Cl i)
def lbc (i : Fin 7) : ℕ := lbs.getD i 0
def cb (i : Fin 7) : List ℕ := cbs.getD i []

theorem hPinv : ∀ i : Fin 7, mat3m (Ps.getD i 0) * mat3m (Pis.getD i 0) = 1 := by decide
theorem hQinv : ∀ i : Fin 7, mat3m (Qs.getD i 0) * mat3m (Qis.getD i 0) = 1 := by decide
theorem himg : ∀ i : Fin 7, ∀ j < (cb i).length,
    actA (mat3m (Ps.getD i 0)) (mat3m (Qs.getD i 0)) (vecOfMask (3 * 3) ((cb i).getD j 0)) =
      vecOfMask (3 * 3) ((imgs.getD i []).getD j 0) := by decide +kernel
theorem hinv : ∀ i : Fin 7, ∀ j < (Cl i).length,
    actA (mat3m (Pis.getD i 0)) (mat3m (Qis.getD i 0)) (vecOfMask (3 * 3) ((Cl i).getD j 0)) =
      vecOfMask (3 * 3) ((invimgs.getD i []).getD j 0) := by decide +kernel
theorem hspan1 : ∀ i : Fin 7, ∀ j < (cb i).length, inSpan (Cl i) ((imgs.getD i []).getD j 0) = true := by
  decide +kernel
theorem hspan2 : ∀ i : Fin 7, ∀ j < (Cl i).length, inSpan (cb i) ((invimgs.getD i []).getD j 0) = true := by
  decide +kernel
theorem hlt1 : ∀ i : Fin 7, ∀ b ∈ Cl i, b < 2 ^ 9 := by decide
theorem hlt2 : ∀ i : Fin 7, ∀ b ∈ cb i, b < 2 ^ 9 := by decide
theorem hlt3 : ∀ i : Fin 7, ∀ j < (cb i).length, (imgs.getD i []).getD j 0 < 2 ^ 9 := by decide
theorem hlt4 : ∀ i : Fin 7, ∀ j < (Cl i).length, (invimgs.getD i []).getD j 0 < 2 ^ 9 := by decide
/-- the certificate of mask `m` (chunk `m / 64`, entry `m % 64`) -/
def cert (m : ℕ) : ℕ × ℕ × ℕ × List ℕ := (certsK (m / 64)).getD (m % 64) (0, 0, 0, [])
theorem hch : ∀ k < 8, chkAll (fun c m => chkC basis ClN 7 c m) (certsK k) (64 * k) = true := by
  intro k hk
  interval_cases k
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3
  · exact hc4
  · exact hc5
  · exact hc6
  · exact hc7
theorem hlen : ∀ k < 8, (certsK k).length = 64 := by decide +kernel
theorem hcerts : ∀ m < 2 ^ 9, chkC basis ClN 7 (cert m) m = true := by
  intro m hm
  have hk : m / 64 < 8 := by omega
  have h := chkAll_spec (fun c m => chkC basis ClN 7 c m) (0, 0, 0, []) (certsK (m / 64)) (64 * (m / 64))
    (hch (m / 64) hk) (m % 64) (by rw [hlen (m / 64) hk]; exact Nat.mod_lt _ (by norm_num))
  rw [Nat.mod_add_div m 64] at h
  exact h
theorem hk : (7 - 1) * (18 - 1) < ∑ i : Fin 7, lbc i := by decide
/-- negative control: the coset count does not reach 19 -/
theorem no19 : ¬ ((7 - 1) * (19 - 1) < ∑ i : Fin 7, lbc i) := by decide

/-- each coset space is the G₀-image of its class representative -/
theorem hmap (i : Fin 7) :
    (spanMasks (cb i)).map (actAL (mat3m (Ps.getD i 0)) (mat3m (Qs.getD i 0))) = Sc i :=
  map_spanMasks_eq _ _ _ _ (hPinv i) (hQinv i) (cb i) (Cl i) (imgs.getD i []) (invimgs.getD i []) (himg i)
    (fun j hj => (mem_spanMasks_iff (Cl i) (hlt1 i) _ (hlt3 i j hj)).mpr (hspan1 i j hj)) (hinv i)
    (fun j hj => (mem_spanMasks_iff (cb i) (hlt2 i) _ (hlt4 i j hj)).mpr (hspan2 i j hj))

/-- **Row 44**, given the three class rows. -/
theorem row44_of (h7 : RowValid cb7 8) (h13 : RowValid cb13 16) (h16 : RowValid cb16 16) :
    RowValid basis 18 := by
  have hrow : ∀ i : Fin 7, QuotLB T334 (spanMasks (cb i)) (lbc i) := by
    intro i
    fin_cases i
    · exact h7
    · exact h13
    · exact h13
    · exact h13
    · exact h13
    · exact h16
    · exact h16
  have hc : ∀ i : Fin 7, QuotLB T334 (Sc i) (lbc i) := by
    intro i
    rw [← hmap i]
    exact quotLB_transport _ _ _ _ (hPinv i) (hQinv i) _ _ (hrow i)
  have hsub : ∀ i : Fin 7, spanMasks basis ≤ Sc i := by
    intro i
    apply Submodule.span_mono
    rintro v ⟨m, hm, rfl⟩
    exact ⟨m, List.mem_append.mpr (Or.inl hm), rfl⟩
  have hone : ∀ v, v ∉ spanMasks basis → ∃! i, v ∈ Sc i :=
    existsUnique_of_certs basis ClN 7 cert hcerts
  exact quotLB_coset_count T334 (spanMasks basis) Sc lbc hc hsub hone 18 hk

end B334.Row44
