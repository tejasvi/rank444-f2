import Mathlib

/-! # B334: statements for R_F₂(⟨3,3,4⟩) ≥ 27 ⇒ R_F₂(⟨3,4,4⟩) ≥ 31 ⇒ R_F₂(⟨4,4,4⟩) ≥ 35

Compiled against Lean v4.30.0 + Mathlib v4.30.0. The release README records its SHA256,
and the release build checks it.
- Every claim is a `def … : Prop`, so the file has no proofs and no `sorry`. The intended theorem names are in the
  docstrings. The proofs go in other modules, which import this file unchanged.

**Conventions.** The indices are those of C. Wang's code and certificates (`problems/matrix/tensor.h` in the repository
linked from arXiv:2603.07280), which write the third factor in the reverse order from the paper's displayed formula.
- `mmT n m p` is ⟨n,m,p⟩ = Σ_{i<n, j<m, k<p} x_{ij} ⊗ y_{jk} ⊗ z_{ki}.
- Entry (i, j) of the first factor is at index m·i + j, entry (j, k) of the second at p·j + k, and entry (k, i) of the
  third at n·k + i. For ⟨3,3,4⟩ these are bits 3i+j, 4j+k and 3k+i.
- `RankLE T r`: T is a sum of r rank-one tensors (zero terms allowed). So `¬ RankLE T r` means
  R(T) ≥ r + 1.

**The proof chain.** Names are those of the B334 modules; the labels name the steps of the proof.
1. `split_flattening : SplitFlattening334` (L1).
2. `sym334 : Sym334` and `point_orbits : PointOrbit2 ∧ PointOrbit3` (L3).
3. `quot707 : QuotLB T334 P707 26` and `quot708 : QuotLB T334 P708 26` (the two point bounds).
4. `two_case : TwoCase` (L2), hence `rank334_ge_27 : Rank334`.
5. `chain_step : ChainStep` and `cyclic : Cyclic` (L6), hence `rank344_ge_31 : Rank344` and `rank444_ge_35 : Rank444`
   through `Chain344` and `Chain444`.
-/

namespace B334

open Finset

section Tensors

variable {R : Type*} [CommSemiring R] {n₀ n₁ n₂ : ℕ}

/-- The rank-one tensor `a ⊗ b ⊗ c`: its entry `(i, j, k)` is `a i * b j * c k`. -/
def outer3 (a : Fin n₀ → R) (b : Fin n₁ → R) (c : Fin n₂ → R) : Fin n₀ → Fin n₁ → Fin n₂ → R :=
  fun i j k => a i * b j * c k

/-- `RankLE T r`: `T` is a sum of `r` rank-one tensors. -/
def RankLE (T : Fin n₀ → Fin n₁ → Fin n₂ → R) (r : ℕ) : Prop :=
  ∃ (a : Fin r → Fin n₀ → R) (b : Fin r → Fin n₁ → R) (c : Fin r → Fin n₂ → R),
    T = ∑ s, outer3 (a s) (b s) (c s)

end Tensors

/-- The matrix multiplication tensor ⟨n,m,p⟩ over F₂. Entry `(x, y, z)` is 1 iff `x = m i + j`, `y = p j + k`,
`z = n k + i` for some `i < n`, `j < m`, `k < p`. -/
def mmT (n m p : ℕ) : Fin (n * m) → Fin (m * p) → Fin (p * n) → ZMod 2 :=
  fun x y z => if x.val % m = y.val / p ∧ y.val % p = z.val / n ∧ z.val % n = x.val / m then 1 else 0

/-- ⟨3,3,4⟩: the 3×3 first factor (9 coordinates), then 3×4 and 4×3 (12 each). -/
abbrev T334 : Fin (3 * 3) → Fin (3 * 4) → Fin (4 * 3) → ZMod 2 := mmT 3 3 4

/-- Bit `p` of the mask `m`, as an element of F₂ (for any length). -/
def vecOfMask (n m : ℕ) : Fin n → ZMod 2 :=
  fun p => if m.testBit p.val then 1 else 0

/-- `QuotLB T S k`: every decomposition of `T` has at least `k` terms whose first factor lies outside `S`.
This is equivalent to R(T mod S) ≥ k, stated without quotient spaces, like the ⟨3,3,3⟩
project's `RT.Fact`. -/
def QuotLB {n₀ n₁ n₂ : ℕ} (T : Fin n₀ → Fin n₁ → Fin n₂ → ZMod 2)
    (S : Submodule (ZMod 2) (Fin n₀ → ZMod 2)) (k : ℕ) : Prop :=
  ∀ (r : ℕ) (a : Fin r → Fin n₀ → ZMod 2) (b : Fin r → Fin n₁ → ZMod 2) (c : Fin r → Fin n₂ → ZMod 2),
    T = ∑ s, outer3 (a s) (b s) (c s) → k ≤ Nat.card {s : Fin r // a s ∉ S}

/-- The rank-2 point of class 707 (mask 10 = e₀₁ + e₁₀) and the rank-3 point of class 708 (mask 84 =
e₀₂ + e₁₁ + e₂₀), as subspaces of the first factor. -/
def P707 : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2) :=
  Submodule.span (ZMod 2) ({vecOfMask (3 * 3) 10} : Set (Fin (3 * 3) → ZMod 2))
def P708 : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2) :=
  Submodule.span (ZMod 2) ({vecOfMask (3 * 3) 84} : Set (Fin (3 * 3) → ZMod 2))

/-! ## The first factor as a matrix, and the symmetry group G₀ = GL₃ × GL₃ -/

/-- The first factor as a 3×3 matrix: entry `(i, j)` is coordinate `3 i + j` (`finProdFinEquiv (i, j) = j + 3 i`). -/
def mat3 (v : Fin (3 * 3) → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => v (finProdFinEquiv (i, j))
/-- The second factor as a 3×4 matrix (coordinate `4 j + k`). -/
def mat34 (w : Fin (3 * 4) → ZMod 2) : Matrix (Fin 3) (Fin 4) (ZMod 2) :=
  Matrix.of fun j k => w (finProdFinEquiv (j, k))
/-- The third factor as a 4×3 matrix (coordinate `3 k + i`). -/
def mat43 (u : Fin (4 * 3) → ZMod 2) : Matrix (Fin 4) (Fin 3) (ZMod 2) :=
  Matrix.of fun k i => u (finProdFinEquiv (k, i))

/-- G₀ acting on the three factors: `a ↦ P a Q`, `b ↦ Q⁻¹ b`, `c ↦ c P⁻¹`. -/
def actA (P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin (3 * 3) → ZMod 2) : Fin (3 * 3) → ZMod 2 :=
  fun x => (P * mat3 v * Q) (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2
def actB (Qi : Matrix (Fin 3) (Fin 3) (ZMod 2)) (w : Fin (3 * 4) → ZMod 2) : Fin (3 * 4) → ZMod 2 :=
  fun y => (Qi * mat34 w) (finProdFinEquiv.symm y).1 (finProdFinEquiv.symm y).2
def actC (Pi : Matrix (Fin 3) (Fin 3) (ZMod 2)) (u : Fin (4 * 3) → ZMod 2) : Fin (4 * 3) → ZMod 2 :=
  fun z => (mat43 u * Pi) (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2

/-- **L3a** (`sym334`): G₀ maps decompositions of ⟨3,3,4⟩ to decompositions. -/
def Sym334 : Prop :=
  ∀ (P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2)), P * Pi = 1 → Q * Qi = 1 →
    ∀ (r : ℕ) (a : Fin r → Fin (3 * 3) → ZMod 2) (b : Fin r → Fin (3 * 4) → ZMod 2)
      (c : Fin r → Fin (4 * 3) → ZMod 2),
      T334 = ∑ s, outer3 (a s) (b s) (c s) →
      T334 = ∑ s, outer3 (actA P Q (a s)) (actB Qi (b s)) (actC Pi (c s))

/-- **L3b** (`point_orbits`): every rank-2 first factor is moved by G₀ to mask 10. -/
def PointOrbit2 : Prop :=
  ∀ v : Fin (3 * 3) → ZMod 2, (mat3 v).rank = 2 →
    ∃ P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2), P * Pi = 1 ∧ Q * Qi = 1 ∧ actA P Q v = vecOfMask (3 * 3) 10
/-- **L3b** (`point_orbits`): every rank-3 first factor is moved by G₀ to mask 84. -/
def PointOrbit3 : Prop :=
  ∀ v : Fin (3 * 3) → ZMod 2, (mat3 v).rank = 3 →
    ∃ P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2), P * Pi = 1 ∧ Q * Qi = 1 ∧ actA P Q v = vecOfMask (3 * 3) 84

/-! ## The split flattening and the two-case argument -/

/-- **L1** (`split_flattening`): in every decomposition of ⟨3,3,4⟩ the matrix ranks of the first factors add up to at
least 36. The split flattening (rows (i, y), columns (j, z)) of ⟨3,3,4⟩ is a 36×36 permutation matrix, and the term
`a ⊗ b ⊗ c` contributes rank ≤ rank a. -/
def SplitFlattening334 : Prop :=
  ∀ (r : ℕ) (a : Fin r → Fin (3 * 3) → ZMod 2) (b : Fin r → Fin (3 * 4) → ZMod 2)
    (c : Fin r → Fin (4 * 3) → ZMod 2),
    T334 = ∑ s, outer3 (a s) (b s) (c s) → 36 ≤ ∑ s, (mat3 (a s)).rank

/-- **The main theorem** (`rank334_ge_27`): R_F₂(⟨3,3,4⟩) ≥ 27. -/
def Rank334 : Prop := ¬ RankLE T334 26

/-- **L2** (`two_case`): the two-case argument as an implication. Its hypotheses are L1, L3 and the two computed
point bounds (Lemma 2). -/
def TwoCase : Prop :=
  SplitFlattening334 → Sym334 → PointOrbit2 → PointOrbit3 →
    QuotLB T334 P707 26 → QuotLB T334 P708 26 → Rank334

/-! ## The chain to ⟨3,4,4⟩ and ⟨4,4,4⟩ -/

/-- **L6a** (`chain_step`): R(⟨n,m,p+1⟩) ≥ R(⟨n,m,p⟩) + m (substitution on the m slices of the last column of the
second matrix, then the last row of the third matrix set to zero). -/
def ChainStep : Prop :=
  ∀ n m p r : ℕ, RankLE (mmT n m (p + 1)) (r + m) → RankLE (mmT n m p) r

/-- **L6b** (`cyclic`): rank is invariant under the cyclic shift ⟨n,m,p⟩ → ⟨m,p,n⟩ (factors (A, B, C) → (B, C, A)). -/
def Cyclic : Prop :=
  ∀ n m p r : ℕ, RankLE (mmT n m p) r → RankLE (mmT m p n) r

/-- **Corollary** (`rank344_ge_31`): R_F₂(⟨3,4,4⟩) ≥ 31. -/
def Rank344 : Prop := ¬ RankLE (mmT 3 4 4) 30

/-- **Corollary** (`rank444_ge_35`): R_F₂(⟨4,4,4⟩) ≥ 35. -/
def Rank444 : Prop := ¬ RankLE (mmT 4 4 4) 34

/-- How the corollaries follow (`chain344`):
`RankLE (mmT 3 4 (3+1)) (26+4)` → (chain) `RankLE (mmT 3 4 3) 26` → (cyclic, twice) `RankLE (mmT 3 3 4) 26`. -/
def Chain344 : Prop := ChainStep → Cyclic → Rank334 → Rank344

/-- (`chain444`): `RankLE (mmT 4 4 (3+1)) (30+4)` → `RankLE (mmT 4 4 3) 30` → (cyclic, twice)
`RankLE (mmT 3 4 4) 30`. -/
def Chain444 : Prop := ChainStep → Cyclic → Rank344 → Rank444

/-! ## Table rows (the inputs of Lemma 2) -/

/-- The subspace spanned by a list of 9-bit masks (a class basis). -/
def spanMasks (l : List ℕ) : Submodule (ZMod 2) (Fin (3 * 3) → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ m ∈ l, v = vecOfMask (3 * 3) m}

/-- A table row `(basis, lb)` is valid: R(T334 mod span basis) ≥ lb. Each row the result uses is proved by
flattening, forced products, coset counting, transport along G₀, or a checked search. -/
def RowValid (basis : List ℕ) (lb : ℕ) : Prop := QuotLB T334 (spanMasks basis) lb

end B334
