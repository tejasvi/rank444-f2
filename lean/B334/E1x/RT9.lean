import B334.BC.BranchCheck334

/-! # Row-table entries and point masks over the 9-bit first factors (core Lean)

Entries and masks for the E1 slot layer of ⟨3,3,4⟩, ported from `RT/Defs.lean` and the `perp` part of `BranchCheck5.lean`
(⟨3,3,3⟩ release `rank333-f2`, Apache-2.0). First factors and functionals are 9-bit in both tensors.

**Entry layout** (118 bits, the 333 layout with the transpose bit replaced by a 10th class bit: ⟨3,3,4⟩ has 710
classes and no transpose symmetry): `[4] d`, nine 9-bit vectors (the first `d` an RREF basis of the row subspace `U`, the
other `9 - d` a basis of `U^⊥`), `[5] cap`, `[10] c`, `[9] P`, `[9] Q`.

**Point masks** are 512-bit numbers (bit `w` for the vector `w`). `nperp9 v`, the vectors `w` with odd `<w, v>`, is the
XOR of the bit-column masks `B_i` over the set bits `i` of `v` (nine XORs, no table); `perp9 v` is its complement;
`kerM9 f n` is the common kernel of `f 0 … f (n-1)`; `dualM e` is the point mask of an entry's row (the common kernel of
its dual vectors). -/

namespace B334.E1x.RT

/-! ## Entry fields -/
def eD (e : Nat) : Nat := e % 16
def eV (e i : Nat) : Nat := (e >>> (4 + 9 * i)) % 512
def eCap (e : Nat) : Nat := (e >>> 85) % 32
def eCls (e : Nat) : Nat := (e >>> 90) % 1024
def eP (e : Nat) : Nat := (e >>> 100) % 512
def eQ (e : Nat) : Nat := (e >>> 109) % 512

/-! ## Point masks -/
/-- all 512 vectors -/
def M512 : Nat := 2 ^ 512 - 1
/-- `B_i`: the vectors `w < 512` with bit `i` set -/
def B0 : Nat := 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
def B1 : Nat := 0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC
def B2 : Nat := 0xF0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0
def B3 : Nat := 0xFF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00
def B4 : Nat := 0xFFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000
def B5 : Nat := 0xFFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000
def B6 : Nat := 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF0000000000000000
def B7 : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000
def B8 : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0000000000000000000000000000000000000000000000000000000000000000

/-- the vectors `w < 512` with odd `<w, v>` -/
def nperp9 (v : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
    (cond (Nat.testBit v 0) B0 0) (cond (Nat.testBit v 1) B1 0)) (cond (Nat.testBit v 2) B2 0))
    (cond (Nat.testBit v 3) B3 0)) (cond (Nat.testBit v 4) B4 0)) (cond (Nat.testBit v 5) B5 0))
    (cond (Nat.testBit v 6) B6 0)) (cond (Nat.testBit v 7) B7 0)) (cond (Nat.testBit v 8) B8 0)

/-- the kernel of the functional `v`: the vectors `w < 512` with even `<w, v>` -/
def perp9 (v : Nat) : Nat := Nat.xor M512 (nperp9 v)

/-- the common kernel of `f 0, …, f (n-1)`, as a point mask -/
def kerM9 (f : Nat → Nat) (n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) M512 (fun j S => Nat.land S (perp9 (f j))) n

/-- the point mask of an entry's row: the common kernel of its dual vectors `d … 8` -/
def dualM (e : Nat) : Nat := kerM9 (fun j => eV e (eD e + j)) (9 - eD e)

end B334.E1x.RT
