import B334.Core.LinAlg
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin

/-! # The tensor ⟨3,3,4⟩ over F₂, decompositions, and the contraction by a functional

Port of `RootSound/Tensor.lean` from the ⟨3,3,3⟩ release (`rank333-f2`, Apache-2.0) to ⟨3,3,4⟩.


Coordinates as in `B334/Statement.lean`:
- a first factor `a` is a 3×3 matrix with `a i j` at bit `3i+j`;
- a second factor `b` is a 3×4 matrix, coordinate `y = 4j+k`;
- a third factor `c` is a 4×3 matrix, coordinate `z = 3k+i`;
- `T = ∑_{i, j < 3, k < 4} e_ij ⊗ e_jk ⊗ e_ki`.

The only changes against ⟨3,3,3⟩: the middle index `k` ranges over `Fin 4`, so `b` and `c` have 12 coordinates and
`T(X)` is 12×12, and the index maps `hi`/`lo` split into `hiB`/`loB` (for `y = 4j+k`) and `hiC`/`loC` (for
`z = 3k+i`). -/

open Matrix

namespace B334.Core

/-- `ZMod 2` with only its field structure exposed, so every ring operation on matrices over `F2` uses the instances
derived from `Field F2` (as in the ⟨3,3,3⟩ release: the general lemmas of `LinAlg` are stated for a field, and matching
`ZMod.commRing` against `Field.toCommRing` is a costly unification). -/
instance fact_prime_two_b334 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
def F2 : Type := ZMod 2
instance : Field F2 := inferInstanceAs (Field (ZMod 2))
instance : DecidableEq F2 := inferInstanceAs (DecidableEq (ZMod 2))
instance : Fintype F2 := inferInstanceAs (Fintype (ZMod 2))

/-- first factors: 3×3 -/
abbrev M3 := Matrix (Fin 3) (Fin 3) F2
/-- second factors: 3×4 -/
abbrev M34 := Matrix (Fin 3) (Fin 4) F2
/-- third factors: 4×3 -/
abbrev M43 := Matrix (Fin 4) (Fin 3) F2

/-- `T = ∑_s a_s ⊗ b_s ⊗ c_s` for `T = ⟨3,3,4⟩` -/
def IsDecomp {n : ℕ} (a : Fin n → M3) (b : Fin n → M34) (c : Fin n → M43) : Prop :=
  ∀ (i j j' : Fin 3) (k k' : Fin 4) (i' : Fin 3),
    (∑ s, a s i j * b s j' k * c s k' i') = if j = j' ∧ k = k' ∧ i = i' then 1 else 0

/-- `X(a) = ∑ X_ij a_ij` -/
def pair (X a : M3) : F2 := ∑ i, ∑ j, X i j * a i j

/-- row index `j` of the second-factor coordinate `y = 4j+k` -/
def hiB (y : Fin 12) : Fin 3 := ⟨y.val / 4, by omega⟩
/-- column index `k` of the second-factor coordinate `y = 4j+k` -/
def loB (y : Fin 12) : Fin 4 := ⟨y.val % 4, by omega⟩
/-- row index `k` of the third-factor coordinate `z = 3k+i` -/
def hiC (z : Fin 12) : Fin 4 := ⟨z.val / 3, by omega⟩
/-- column index `i` of the third-factor coordinate `z = 3k+i` -/
def loC (z : Fin 12) : Fin 3 := ⟨z.val % 3, by omega⟩

/-- `b` as a vector, coordinate `y = 4j+k` -/
def vecB (b : M34) : Fin 12 → F2 := fun y => b (hiB y) (loB y)
/-- `c` as a vector, coordinate `z = 3k+i` -/
def vecC (c : M43) : Fin 12 → F2 := fun z => c (hiC z) (loC z)

/-- `T(X)`, the 12×12 matrix of `(b, c) ↦ tr(X b c)`: entry `(y = 4j+k, z = 3k'+i)` is `X i j` if `k = k'` -/
def TX (X : M3) : Matrix (Fin 12) (Fin 12) F2 := fun y z => if loB y = hiC z then X (loC z) (hiB y) else 0

theorem sum_swap3 {n : ℕ} (G : Fin n → Fin 3 → Fin 3 → F2) (X : M3) :
    (∑ s, ∑ i, ∑ j, X i j * G s i j) = ∑ i, ∑ j, X i j * ∑ s, G s i j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]

theorem contract {n : ℕ} {a : Fin n → M3} {b : Fin n → M34} {c : Fin n → M43} (hd : IsDecomp a b c) (X : M3)
    (y z : Fin 12) :
    TX X y z = ∑ s, pair X (a s) * vecB (b s) y * vecC (c s) z := by
  have key : ∀ s, pair X (a s) * vecB (b s) y * vecC (c s) z =
      ∑ i, ∑ j, X i j * (a s i j * b s (hiB y) (loB y) * c s (hiC z) (loC z)) := by
    intro s
    simp only [pair, vecB, vecC, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  simp_rw [key]
  rw [sum_swap3 (fun s i j => a s i j * b s (hiB y) (loB y) * c s (hiC z) (loC z)) X]
  unfold IsDecomp at hd
  simp only [hd]
  unfold TX
  by_cases h : loB y = hiC z
  · simp only [h, true_and, if_true]
    rw [Finset.sum_eq_single (loC z)]
    · rw [Finset.sum_eq_single (hiB y)]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    · intro i _ hi'
      apply Finset.sum_eq_zero
      intro j _
      simp only [mul_ite, mul_one, mul_zero]
      split_ifs with hh
      · exact absurd hh.2 hi'
      · rfl
    · simp
  · simp [h]

end B334.Core
