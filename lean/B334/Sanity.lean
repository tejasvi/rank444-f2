import B334.Statement

/-! # B334.Sanity: non-vacuity facts for `B334/Statement.lean`

It imports `Statement.lean` unchanged; the proofs are in `B334/Lem/SanityL.lean`.
- Guard against a definitional slip in `outer3`, `mmT` or `RankLE` that would make `¬ RankLE` true for a trivial
  reason. Each `def … : Prop` below is proved in `B334/Lem/SanityL.lean`, along the proof plan in its
  docstring.
- The proofs must be kernel-only, like the final theorems: no `native_decide` and no `ofReduceBool`.
- `#print axioms` on each proof must show only propext, Classical.choice and Quot.sound.
-/

namespace B334

/-- The rank-29 scheme `334-29-mod0.exp` as (a, b, c) masks in the conventions of `Statement.lean`:
a bit 3i+j, b bit 4j+k, c bit 3k+i. It was extracted and checked to rebuild T334 exactly by a script
(`rankLE_29` checks it in the kernel). -/
def scheme29 : List (ℕ × ℕ × ℕ) :=
  [(81, 100, 306), (146, 168, 288), (65, 102, 27), (36, 1332, 2), (2, 119, 361),
   (195, 104, 256), (388, 2440, 2564), (56, 1536, 3268), (64, 9, 45), (16, 580, 434),
   (390, 136, 800), (3, 8, 2605), (67, 111, 41), (292, 2568, 1024), (260, 3720, 3076),
   (316, 1544, 3332), (53, 51, 360), (4, 256, 2567), (511, 8, 2308), (63, 7, 320),
   (60, 1543, 322), (48, 512, 1528), (384, 2304, 2560), (276, 648, 1312), (52, 563, 362),
   (3, 48, 360), (128, 2448, 4), (73, 2, 18), (24, 1540, 130)]

/-- **NV1** (`rankLE_29`): T334 has a decomposition with 29 terms.
Proof plan:
- witnesses `a s := vecOfMask (3*3) (scheme29.getD s (0,0,0)).1`, and likewise b (length 3*4) and c (length 4*3);
- then the tensor equation by computational reflection. Write a `Bool` checker of the 9·12·12 = 1,296 entries
  (each entry an XOR over the 29 terms), prove it sound once, and evaluate it with `decide`.
- Mathlib's `Finset.sum` over `Fin 29` is not kernel-reducible in reasonable time, so it is not evaluated directly. -/
def NV1 : Prop := RankLE T334 29

/-- **NV1′** (`rankLE_naive`): the standard algorithm, ⟨n,m,p⟩ has a decomposition with n·m·p terms, one per (i,j,k).
Proof plan: the term for s ≅ (i,j,k) is e_{mi+j} ⊗ e_{pj+k} ⊗ e_{nk+i}. Sum the indicator functions with
`Finset.sum_eq_single` per entry. -/
def NVnaive : Prop := ∀ n m p : ℕ, RankLE (mmT n m p) (n * m * p)

/-- **NV2** (`trace_identity`): mmT is the trilinear form of matrix multiplication,
Σ_{x,y,z} mmT x y z · X_x · Y_y · Z_z = tr(X·Y·Z), with the factors flattened by `finProdFinEquiv`, as in `mat3`.
Proof plan: rewrite each sum over `Fin (n*m)` as a double sum over `Fin n × Fin m` (`finProdFinEquiv.sum_comp`),
evaluate the `if` with the Kronecker deltas (`Finset.sum_ite_eq`), and compare with `Matrix.trace_mul…`
(`Matrix.trace`, `Matrix.mul_apply`). -/
def NV2 : Prop :=
  ∀ (n m p : ℕ) (X : Matrix (Fin n) (Fin m) (ZMod 2)) (Y : Matrix (Fin m) (Fin p) (ZMod 2))
    (Z : Matrix (Fin p) (Fin n) (ZMod 2)),
    (∑ x : Fin (n * m), ∑ y : Fin (m * p), ∑ z : Fin (p * n),
        mmT n m p x y z * X (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2
          * Y (finProdFinEquiv.symm y).1 (finProdFinEquiv.symm y).2
          * Z (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2)
      = Matrix.trace (X * Y * Z)

end B334
