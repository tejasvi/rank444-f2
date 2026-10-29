import B334.E1x.GLTab
import B334.Core.SymBits

/-! # G₀ on 9-bit first factors, in kernel-cheap `Nat` arithmetic

Port of `C3/Act.lean` from the ⟨3,3,3⟩ release (`rank333-f2`, Apache-2.0) to ⟨3,3,4⟩. The first factor is a 3×3 matrix
in both tensors, so the bit-level product and the GL₃(F₂) tables are unchanged. The only change: ⟨3,3,4⟩ has no
transpose symmetry, so the action is `actF P Q v = P · v · Q` (⟨3,3,3⟩'s `actN false P Q`); the second and third factors
move by `b ↦ Q⁻¹ b`, `c ↦ c P⁻¹` (`E1x/Decomp.lean`).

* `mulF u v` is the matrix product of 9-bit matrices (entry `(i, j)` at bit `3i+j`): column `k` of `u` (bits `k, k+3,
  k+6`, i.e. `(u >>> k) &&& 73`) times row `k` of `v` (`(v >>> 3k) &&& 7`), without carries.
* `toM3_mulF`: the encoding is multiplicative; `toM3_inj`: it is injective below 512; `gl_inv`: `isGL P` gives the
  inverse `invN P` (`GLTab`, checked by `gl_facts`).
* `actF_xor`, `actF_zero`: `actF P Q` is linear on codes; `actF_inj`: injective for invertible `P`, `Q`. -/

open Matrix

namespace B334.E1x

open B334.Core

/-- a 9-bit mask as a 3×3 matrix (bit `3i+j` = entry `(i, j)`; the same body as `B334.BCP.toM3`) -/
def toM3 (v : Nat) : M3 := fun i j => bitF v (3 * i.val + j.val)

/-- field `i` (9 bits) of `S` -/
def fld9 (S i : Nat) : Nat := Nat.land (Nat.shiftRight S (Nat.mul 9 i)) 511

/-- the product of 9-bit matrices -/
def mulF (u v : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.mul (Nat.land u 73) (Nat.land v 7))
    (Nat.mul (Nat.land (Nat.shiftRight u 1) 73) (Nat.land (Nat.shiftRight v 3) 7)))
    (Nat.mul (Nat.land (Nat.shiftRight u 2) 73) (Nat.land (Nat.shiftRight v 6) 7))

/-- the element `(P, Q)` of G₀ on first factors: `v ↦ P v Q` -/
def actF (P Q v : Nat) : Nat := mulF (mulF P v) Q

def isGL (P : Nat) : Bool := Nat.testBit GLM P
def invN (P : Nat) : Nat := fld9 INVT P

theorem fld9_eq (S i : Nat) : fld9 S i = (S >>> (9 * i)) &&& 511 := rfl
theorem fld9_lt (S i : Nat) : fld9 S i < 512 := Nat.lt_succ_of_le Nat.and_le_right

theorem mulF_eq (u v : Nat) : mulF u v = ((u &&& 73) * (v &&& 7)) ^^^ (((u >>> 1) &&& 73) * ((v >>> 3) &&& 7)) ^^^
    (((u >>> 2) &&& 73) * ((v >>> 6) &&& 7)) := rfl

/-! ## The encoding is a homomorphism -/

theorem spr_mul_all : ∀ a < 74, ∀ b < 8, a &&& 73 = a → ∀ i < 3, ∀ j < 3,
    (a * b).testBit (3 * i + j) = (a.testBit (3 * i) && b.testBit j) := by decide +kernel

theorem prod_lt (x y : Nat) : (x &&& 73) * (y &&& 7) < 2 ^ 9 := by
  have h1 : x &&& 73 ≤ 73 := Nat.and_le_right
  have h2 : y &&& 7 ≤ 7 := Nat.and_le_right
  calc (x &&& 73) * (y &&& 7) ≤ 73 * 7 := Nat.mul_le_mul h1 h2
    _ < 2 ^ 9 := by norm_num

theorem prod_testBit (x y i j : Nat) (hi : i < 3) (hj : j < 3) :
    ((x &&& 73) * (y &&& 7)).testBit (3 * i + j) = (x.testBit (3 * i) && y.testBit j) := by
  have h1 : x &&& 73 < 74 := Nat.lt_succ_of_le Nat.and_le_right
  have h2 : (x &&& 73) &&& 73 = x &&& 73 := by rw [Nat.and_assoc, Nat.and_self]
  have h3 : y &&& 7 < 8 := Nat.lt_succ_of_le Nat.and_le_right
  rw [spr_mul_all _ h1 _ h3 h2 i hi j hj, Nat.testBit_and, Nat.testBit_and]
  have e1 : Nat.testBit 73 (3 * i) = true := by interval_cases i <;> decide
  have e2 : Nat.testBit 7 j = true := by interval_cases j <;> decide
  rw [e1, e2, Bool.and_true, Bool.and_true]

theorem mulF_lt (u v : Nat) : mulF u v < 512 := by
  rw [mulF_eq]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (prod_lt _ _) (prod_lt _ _)) (prod_lt _ _)

theorem mulF_testBit (u v i j : Nat) (hi : i < 3) (hj : j < 3) :
    (mulF u v).testBit (3 * i + j) = xor (xor (u.testBit (3 * i) && v.testBit j)
      (u.testBit (3 * i + 1) && v.testBit (3 + j))) (u.testBit (3 * i + 2) && v.testBit (6 + j)) := by
  rw [mulF_eq, Nat.testBit_xor, Nat.testBit_xor, prod_testBit _ _ _ _ hi hj, prod_testBit _ _ _ _ hi hj,
    prod_testBit _ _ _ _ hi hj, Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, show 1 + 3 * i = 3 * i + 1 by omega, show 2 + 3 * i = 3 * i + 2 by omega]

theorem toM3_mulF (u v : Nat) : toM3 (mulF u v) = toM3 u * toM3 v := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp only [toM3, bitF_bf]
  rw [mulF_testBit u v i.val j.val hi hj, bf_xor, bf_xor, bf_and, bf_and, bf_and]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero, Nat.mul_zero, Nat.zero_add, Nat.mul_one]

theorem toM3_inj {u v : Nat} (hu : u < 512) (hv : v < 512) (h : toM3 u = toM3 v) : u = v := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 9
  · have e := congrFun (congrFun h ⟨p / 3, by omega⟩) ⟨p % 3, by omega⟩
    simp only [toM3, bitF_bf] at e
    rw [show 3 * (p / 3) + p % 3 = p by omega] at e
    cases hu' : u.testBit p <;> cases hv' : v.testBit p <;> rw [hu', hv'] at e <;>
      first | rfl | exact absurd e (by decide)
  · have h512 : 512 ≤ 2 ^ p := by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hu h512), Nat.testBit_lt_two_pow (lt_of_lt_of_le hv h512)]

theorem toM3_273 : toM3 273 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem toM3_zero : toM3 0 = 0 := by
  ext i j; simp [toM3, bitF]

theorem toM3_xor (x y : Nat) : toM3 (x ^^^ y) = toM3 x + toM3 y := by
  ext i j
  simp only [toM3, Matrix.add_apply, bitF_bf, Nat.testBit_xor, bf_xor]

/-! ## `GL₃(F₂)` facts, checked by the kernel -/

theorem gl_facts : ∀ P < 512, isGL P = true → (mulF P (invN P) = 273 ∧ mulF (invN P) P = 273) := by
  decide +kernel

theorem GLM_lt : GLM < 2 ^ 512 := by decide +kernel

theorem isGL_lt {P : Nat} (h : isGL P = true) : P < 512 := by
  by_contra hc
  have h1 : 2 ^ 512 ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Nat.testBit GLM P = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le GLM_lt h1)
  rw [isGL, this] at h
  exact absurd h (by decide)

theorem isGL_273 : isGL 273 = true := by decide +kernel

theorem gl_inv {P : Nat} (h : isGL P = true) : toM3 P * toM3 (invN P) = 1 ∧ toM3 (invN P) * toM3 P = 1 := by
  obtain ⟨h1, h2⟩ := gl_facts P (isGL_lt h) h
  rw [← toM3_mulF, ← toM3_mulF, h1, h2, toM3_273]
  exact ⟨rfl, rfl⟩

/-! ## The action -/

theorem actF_lt (P Q v : Nat) : actF P Q v < 512 := mulF_lt _ _

theorem toM3_actF (P Q v : Nat) : toM3 (actF P Q v) = toM3 P * toM3 v * toM3 Q := by
  rw [actF, toM3_mulF, toM3_mulF]

theorem xor_lt512 {x y : Nat} (hx : x < 512) (hy : y < 512) : x ^^^ y < 512 := by
  have e : (512 : ℕ) = 2 ^ 9 := by norm_num
  rw [e] at hx hy ⊢
  exact Nat.xor_lt_two_pow hx hy

theorem actF_xor (P Q x y : Nat) (hx : x < 512) (hy : y < 512) :
    actF P Q (x ^^^ y) = actF P Q x ^^^ actF P Q y := by
  apply toM3_inj (actF_lt _ _ _) (xor_lt512 (actF_lt _ _ _) (actF_lt _ _ _))
  rw [toM3_xor, toM3_actF, toM3_actF, toM3_actF, toM3_xor, Matrix.mul_add, Matrix.add_mul]

theorem actF_zero (P Q : Nat) : actF P Q 0 = 0 := by
  apply toM3_inj (actF_lt _ _ _) (by norm_num)
  rw [toM3_actF, toM3_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem actF_inj {P Q : Nat} (hP : isGL P = true) (hQ : isGL Q = true) {x y : Nat} (hx : x < 512) (hy : y < 512)
    (h : actF P Q x = actF P Q y) : x = y := by
  apply toM3_inj hx hy
  have e := congrArg toM3 h
  rw [toM3_actF, toM3_actF] at e
  obtain ⟨-, hP2⟩ := gl_inv hP
  obtain ⟨hQ1, -⟩ := gl_inv hQ
  have := congrArg (fun M => toM3 (invN P) * M * toM3 (invN Q)) e
  simp only [← Matrix.mul_assoc, hP2, Matrix.one_mul] at this
  simpa only [Matrix.mul_assoc, hQ1, Matrix.mul_one] using this

end B334.E1x
