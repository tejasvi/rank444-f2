import B334.E1x.RT9
import B334.E1x.Act
import B334.BCP.Count

/-! # Point masks over 9-bit vectors: the specifications

* `nperp9_bit`, `perp9_bit`: bit `w` of `nperp9 v` (of `perp9 v`) is the parity (its negation) of `<w, v>`, for `v, w <
  512`; checked once by the kernel over all pairs (`nperp9_fact`).
* `kerM9_testBit`: `kerM9 f n` is the common kernel of `f 0 … f (n-1)`.
* `par_xor9`: the parity is linear. -/

namespace B334.E1x.RT

open B334.BC B334.BCP B334.Core

theorem M512_bit (w : Nat) : M512.testBit w = decide (w < 512) := Nat.testBit_two_pow_sub_one 512 w

theorem nperp9_fact : allLT 512 (fun v => allLT 512 (fun w => (nperp9 v).testBit w == par (w &&& v))) = true := by
  decide +kernel

theorem nperp9_bit (v w : Nat) (hv : v < 512) (hw : w < 512) : (nperp9 v).testBit w = par (w &&& v) := by
  have h := allLT_spec (allLT_spec nperp9_fact v hv) w hw
  simpa using h

theorem perp9_bit (v w : Nat) (hv : v < 512) (hw : w < 512) : (perp9 v).testBit w = !par (w &&& v) := by
  show (M512 ^^^ nperp9 v).testBit w = _
  rw [Nat.testBit_xor, M512_bit, nperp9_bit v w hv hw]
  simp [hw]

theorem kerM9_testBit (f : Nat → Nat) (hf : ∀ j, f j < 512) (n w : Nat) (hw : w < 512) :
    (kerM9 f n).testBit w = true ↔ ∀ j < n, par (w &&& f j) = false := by
  induction n with
  | zero => simp [kerM9, M512_bit, hw]
  | succ n ih =>
    show (kerM9 f n &&& perp9 (f n)).testBit w = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, ih, perp9_bit _ _ (hf n) hw, Bool.not_eq_true']
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact h1 j h
      · subst h; exact h2
    · intro h; exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

theorem dualM_testBit (e w : Nat) (hw : w < 512) :
    (dualM e).testBit w = true ↔ ∀ k < 9 - eD e, par (w &&& eV e (eD e + k)) = false :=
  kerM9_testBit (fun k => eV e (eD e + k)) (fun _ => Nat.mod_lt _ (by norm_num)) _ w hw

theorem xorBits_xor (a b k : Nat) : xorBits (a ^^^ b) k = xor (xorBits a k) (xorBits b k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show xor (xorBits (a ^^^ b) k) ((a ^^^ b).testBit k) =
      xor (xor (xorBits a k) (a.testBit k)) (xor (xorBits b k) (b.testBit k))
    rw [ih, Nat.testBit_xor]
    cases xorBits a k <;> cases xorBits b k <;> cases a.testBit k <;> cases b.testBit k <;> rfl

theorem and_lt512 {x : Nat} (v : Nat) (hx : x < 512) : x &&& v < 512 := lt_of_le_of_lt Nat.and_le_left hx

theorem par_xor9 (x y v : Nat) (hx : x < 512) (hy : y < 512) :
    par ((x ^^^ y) &&& v) = xor (par (x &&& v)) (par (y &&& v)) := by
  have h1 : (x ^^^ y) &&& v = (x &&& v) ^^^ (y &&& v) := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases x.testBit i <;> cases y.testBit i <;> cases v.testBit i <;> rfl
  rw [h1, par_eq _ (xor_lt512 (and_lt512 v hx) (and_lt512 v hy)), par_eq _ (and_lt512 v hx),
    par_eq _ (and_lt512 v hy), xorBits_xor]

theorem par_zero_and (v : Nat) : par (0 &&& v) = false := by rw [Nat.zero_and]; decide

end B334.E1x.RT
