import B334.BC.BranchCheck334
import B334.Core.SymBits

/-! # Soundness of BranchCheck334: basic helpers

Port of `S5/Base.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0). New for ⟨3,3,4⟩: the second and third factors are
12-bit, so the duality `⟨c, x(b)⟩` is the parity of 12 bits, `par12`; the checker's `par` (the 512-entry table) stays
the parity of 9-bit first factors and functionals. -/

namespace B334.BCP

open B334.BC B334.Core

theorem ndiv (x y : Nat) : Nat.div x y = x / y := rfl
theorem nmod (x y : Nat) : Nat.mod x y = x % y := rfl

theorem bit_eq (n i : Nat) : bit n i = n.testBit i := by
  unfold bit
  have h1 : Nat.land (Nat.shiftRight n i) 1 = n / 2 ^ i % 2 := by
    show (n >>> i) &&& 1 = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;> rw [h] <;> rfl

/-- parity of bits `0 … k-1` -/
def xorBits (v k : Nat) : Bool := @Nat.rec (fun _ => Bool) false (fun i ih => xor ih (v.testBit i)) k

/-- parity of the low 12 bits: `⟨u, v⟩ = par12 (u &&& v)` for 12-bit masks -/
def par12 (v : Nat) : Bool := xorBits v 12

end B334.BCP
