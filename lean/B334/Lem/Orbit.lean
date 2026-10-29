import B334.Lem.OrbitTab
import B334.E1x.Fact

/-! # L3b: the point orbits of G₀ on first factors of rank 2 and 3

* `rkN m`: the rank of the 9-bit first factor `m` (entry `(i, j)` at bit `3i+j`), row by row: a row counts when it lies
  outside the span of the rows above it. `rk3 v := rkN (maskOf v)` is the computable rank of a statement vector.
* `wit_all` (`decide +kernel`, all 512 masks): the table `WIT` of `Lem/OrbitTab.lean` gives `P, Q ∈ GL₃(F₂)` with
  `P · m · Q = canonN (rkN m)`, where `canonN 0, 1, 2, 3 = 0, 1, 10, 84`.
* `rank_vecOfMask`: `(mat3 (vecOfMask 9 m)).rank = rkN m`. The rank is invariant under invertible factors
  (`rank_mul_inv_left`, `rank_mul_inv_right`), and `canonN r = diagonal (wr r) · S` with `S² = 1` has rank `r`
  (`rank_canon`). Hence `rk3_eq : rk3 v = (mat3 v).rank`.
* `point_orbit2`, `point_orbit3`: the table entry of a first factor of rank 2 (3) moves it to mask 10 (84). The bit-level
  action is `E1x.actF` (`E1x/Act.lean`); `actA_vecOfMask` reads it in the statement's `actA`. -/

namespace B334.Lem

open B334 B334.E1x

/-- row `k` (3 bits) of a 9-bit first factor -/
def row3 (m k : ℕ) : ℕ := Nat.land (Nat.shiftRight m (Nat.mul 3 k)) 7

/-- the rank of a 9-bit first factor, row by row -/
def rkN (m : ℕ) : ℕ :=
  (if row3 m 0 = 0 then 0 else 1) +
  (if row3 m 1 = 0 ∨ row3 m 1 = row3 m 0 then 0 else 1) +
  (if row3 m 2 = 0 ∨ row3 m 2 = row3 m 0 ∨ row3 m 2 = row3 m 1 ∨ row3 m 2 = Nat.xor (row3 m 0) (row3 m 1)
    then 0 else 1)

theorem rkN_le (m : ℕ) : rkN m ≤ 3 := by
  unfold rkN
  split_ifs <;> omega

/-- the canonical first factor of rank `r`: 0, `E₀₀`, `E₀₁ + E₁₀` (class 707), `E₀₂ + E₁₁ + E₂₀` (class 708) -/
def canonN (r : ℕ) : ℕ := if r = 0 then 0 else if r = 1 then 1 else if r = 2 then 10 else 84

/-- the witnesses of mask `m` -/
def witP (m : ℕ) : ℕ := fld9 WIT (2 * m)
def witQ (m : ℕ) : ℕ := fld9 WIT (2 * m + 1)

/-- the table entry of mask `m` is correct -/
def witOK (m : ℕ) : Bool :=
  isGL (witP m) && isGL (witQ m) && (actF (witP m) (witQ m) m == canonN (rkN m))

theorem wit_all : ∀ m < 512, witOK m = true := by decide +kernel

theorem wit_spec {m : ℕ} (hm : m < 512) :
    isGL (witP m) = true ∧ isGL (witQ m) = true ∧ actF (witP m) (witQ m) m = canonN (rkN m) := by
  have h := wit_all m hm
  simp only [witOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## Bit-level products in the statement's matrices -/

theorem mat3_mulF (u v : ℕ) :
    mat3 (vecOfMask (3 * 3) (mulF u v)) = mat3 (vecOfMask (3 * 3) u) * mat3 (vecOfMask (3 * 3) v) := by
  have h := toM3_mulF u v
  rw [← mat3_vecOfMask, ← mat3_vecOfMask, ← mat3_vecOfMask] at h
  exact h

theorem mat3_gl {P : ℕ} (h : isGL P = true) :
    mat3 (vecOfMask (3 * 3) P) * mat3 (vecOfMask (3 * 3) (invN P)) = 1 := by
  have h1 := (gl_inv h).1
  rw [← mat3_vecOfMask, ← mat3_vecOfMask] at h1
  exact h1

theorem mat3_inj {v w : Fin (3 * 3) → ZMod 2} (h : mat3 v = mat3 w) : v = w := by
  funext x
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective x
  have := congrFun (congrFun h i) j
  simpa [mat3] using this

/-- `actA` on masks is the bit-level `actF` -/
theorem actA_vecOfMask (p q m : ℕ) :
    actA (mat3 (vecOfMask (3 * 3) p)) (mat3 (vecOfMask (3 * 3) q)) (vecOfMask (3 * 3) m) =
      vecOfMask (3 * 3) (actF p q m) := by
  apply mat3_inj
  rw [B334.Bind.mat3_actA, actF, mat3_mulF, mat3_mulF]

/-! ## Rank -/

theorem rank_mul_inv_right (A Q Qi : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hQ : Q * Qi = 1) :
    (A * Q).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left _ _)
  calc A.rank = (A * Q * Qi).rank := by rw [Matrix.mul_assoc, hQ, Matrix.mul_one]
    _ ≤ (A * Q).rank := Matrix.rank_mul_le_left _ _

theorem rank_mul_inv_left (A P Pi : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hP : P * Pi = 1) :
    (P * A).rank = A.rank := by
  have hP' : Pi * P = 1 := mul_eq_one_comm.mp hP
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc A.rank = (Pi * (P * A)).rank := by rw [← Matrix.mul_assoc, hP', Matrix.one_mul]
    _ ≤ (P * A).rank := Matrix.rank_mul_le_right _ _

/-- the diagonal of the canonical form of rank `r` -/
def wr (r : ℕ) : Fin 3 → ZMod 2 := fun i => if i.val < r then 1 else 0
/-- the column operation from `diagonal (wr r)` to `canonN r` (an involution): 1, 1, the swap of columns 0 and 1,
the reversal of the columns -/
def sN (r : ℕ) : ℕ := if r = 2 then 266 else if r = 3 then 84 else 273

theorem canon_facts : ∀ r < 4,
    mat3 (vecOfMask (3 * 3) (canonN r)) = Matrix.diagonal (wr r) * mat3 (vecOfMask (3 * 3) (sN r)) ∧
    mat3 (vecOfMask (3 * 3) (sN r)) * mat3 (vecOfMask (3 * 3) (sN r)) = 1 ∧
    Fintype.card {i : Fin 3 // wr r i ≠ 0} = r := by
  decide +kernel

theorem rank_canon {r : ℕ} (hr : r ≤ 3) : (mat3 (vecOfMask (3 * 3) (canonN r))).rank = r := by
  obtain ⟨h1, h2, h3⟩ := canon_facts r (by omega)
  rw [h1, rank_mul_inv_right _ _ _ h2]
  exact (Matrix.rank_diagonal (wr r)).trans h3

/-- the rank of a mask is `rkN` -/
theorem rank_vecOfMask {m : ℕ} (hm : m < 512) : (mat3 (vecOfMask (3 * 3) m)).rank = rkN m := by
  obtain ⟨hP, hQ, he⟩ := wit_spec hm
  have h := congrArg mat3 (actA_vecOfMask (witP m) (witQ m) m)
  rw [he, B334.Bind.mat3_actA] at h
  rw [← rank_canon (rkN_le m), ← h, rank_mul_inv_right _ _ _ (mat3_gl hQ), rank_mul_inv_left _ _ _ (mat3_gl hP)]

/-- **the computable rank** of a first factor -/
def rk3 (v : Fin (3 * 3) → ZMod 2) : ℕ := rkN (B334.MethodK.maskOf v)

theorem vecOfMask_maskOf (v : Fin (3 * 3) → ZMod 2) : vecOfMask (3 * 3) (B334.MethodK.maskOf v) = v := by
  have h : vecOfMask (3 * 3) (B334.MethodK.maskOf v) = B334.MethodK.mvec (3 * 3) (B334.MethodK.maskOf v) := by
    funext p; rfl
  rw [h, B334.MethodK.mvec_maskOf]

theorem rk3_eq (v : Fin (3 * 3) → ZMod 2) : rk3 v = (mat3 v).rank := by
  have hm : B334.MethodK.maskOf v < 512 := lt_of_lt_of_eq (B334.MethodK.maskOf_lt v) (by norm_num)
  rw [rk3, ← rank_vecOfMask hm, vecOfMask_maskOf]

/-! ## The point orbits -/

/-- a first factor of rank `r` is moved by G₀ to `canonN r` -/
theorem orbit_of_rank {v : Fin (3 * 3) → ZMod 2} {r : ℕ} (hv : (mat3 v).rank = r) :
    ∃ P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2), P * Pi = 1 ∧ Q * Qi = 1 ∧
      actA P Q v = vecOfMask (3 * 3) (canonN r) := by
  obtain ⟨m, hm, rfl⟩ := B334.Bind.exists_mask v
  have hm' : m < 512 := lt_of_lt_of_eq hm (by norm_num)
  obtain ⟨hP, hQ, he⟩ := wit_spec hm'
  rw [rank_vecOfMask hm'] at hv
  refine ⟨_, _, _, _, mat3_gl hP, mat3_gl hQ, ?_⟩
  rw [actA_vecOfMask, he, hv]

/-- **L3b, rank 2** (`point_orbits`). -/
theorem point_orbit2 : PointOrbit2 := fun _ hv => orbit_of_rank hv

/-- **L3b, rank 3** (`point_orbits`). -/
theorem point_orbit3 : PointOrbit3 := fun _ hv => orbit_of_rank hv

end B334.Lem
