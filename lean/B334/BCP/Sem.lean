import B334.BC.BranchCheck334
import B334.Core.Terms334
import B334.Core.SymBits

/-! # Semantics of the BranchCheck334 state: residuals, hit sets, the residual identity

Port of the definitions of `S5/Sem.lean` and `S5/Rec.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to ⟨3,3,4⟩:
second and third factors are 12-bit masks, first factors and functionals stay 9-bit.

* `aT T t`: the `t`-th 9-bit first factor packed in `T`;
* `resM X asg`: the residual `R(X) = T(X) + ∑_{assigned (a, b, c), X(a) = 1} b cᵀ` (12×12 over F₂);
* `hitS T n ACT X`: the active terms hit by `X`;
* `BC n b c`: nonzero 12-bit factors; `HD`: the residual identity `R(X) = ∑_{t ∈ hitS} b_t c_tᵀ` on the domain
  (part of the invariant `Inv`). -/

namespace B334.BCP

open B334.Core B334.BC Matrix

/-- first factor `t` of packed terms -/
def aT (T t : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul 9 t)) 511

theorem aT_lt (T t : Nat) : aT T t < 512 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

/-- a 9-bit mask as a 3×3 matrix (bit `3i+j` = entry `(i, j)`) -/
def toM3 (v : Nat) : M3 := fun i j => bitF v (3 * i.val + j.val)

/-- a 12-bit mask as a vector (bit `y` = coordinate `y`; `vecB`/`vecC` order, `vecB_toM34`, `vecC_toM43`) -/
def nv (v : Nat) : Fin 12 → F2 := fun y => bitF v y.val

/-- the residual `R(X) = T(X) + ∑_{assigned, X(a) = 1} b cᵀ` -/
def resM (X : Nat) (asg : Asg) : Matrix (Fin 12) (Fin 12) F2 :=
  TX (toM3 X) + (asg.map (fun e => if par (e.1 &&& X) = true then vecMulVec (nv e.2.1) (nv e.2.2) else 0)).sum

theorem resM_cons (X : Nat) (e : Nat × Nat × Nat) (asg : Asg) :
    resM X (e :: asg) = resM X asg + (if par (e.1 &&& X) = true then vecMulVec (nv e.2.1) (nv e.2.2) else 0) := by
  simp only [resM, List.map_cons, List.sum_cons]; abel

theorem resM_nil (X : Nat) : resM X [] = TX (toM3 X) := by simp [resM]

/-- the active terms hit by `X` -/
def hitS (T n ACT X : Nat) : Finset Nat :=
  (Finset.range n).filter (fun t => ACT.testBit t = true ∧ par (aT T t &&& X) = true)

theorem mem_hitS {T n ACT X t : Nat} :
    t ∈ hitS T n ACT X ↔ t < n ∧ ACT.testBit t = true ∧ par (aT T t &&& X) = true := by
  simp [hitS]

/-- nonzero 12-bit second and third factors -/
def BC (n : Nat) (b c : Nat → Nat) : Prop := ∀ t, t < n → 0 < b t ∧ b t < 4096 ∧ 0 < c t ∧ c t < 4096

/-- the residual identity on the domain -/
def HD (T n dom : Nat) (b c : Nat → Nat) (ACT : Nat) (asg : Asg) : Prop :=
  ∀ X, X < 512 → dom.testBit X = true → resM X asg = ∑ t ∈ hitS T n ACT X, vecMulVec (nv (b t)) (nv (c t))

end B334.BCP
