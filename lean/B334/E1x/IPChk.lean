/-! # Chunked Boolean checks for the per-IP facts (core Lean)

`allR f a m` is `f a && f (a + 1) && … && f (a + m - 1)`. Generated fact modules prove it by `decide +kernel` for
chunks of 512 indices (the 333 `slOKL` pattern of `E1G/OK_l479cw_Base.lean`, ⟨3,3,3⟩ release `rank333-f2`,
Apache-2.0, made generic in `f`); `allR_join` joins chunks and `allR_spec` reads one index back. -/

namespace B334.E1x.IPChk

/-- `f` holds on `a, a + 1, …, a + m - 1` -/
def allR (f : Nat → Bool) (a m : Nat) : Bool := Nat.rec (motive := fun _ => Bool) true (fun i b => b && f (a + i)) m

theorem allR_succ (f : Nat → Bool) (a m : Nat) : allR f a (m + 1) = (allR f a m && f (a + m)) := rfl

theorem allR_join (f : Nat → Bool) (a m k : Nat) (h1 : allR f a m = true) (h2 : allR f (a + m) k = true) :
    allR f a (m + k) = true := by
  induction k with
  | zero => exact h1
  | succ k ih =>
    rw [allR_succ, Bool.and_eq_true] at h2
    rw [← Nat.add_assoc, allR_succ, Bool.and_eq_true]
    exact ⟨ih h2.1, by rw [← Nat.add_assoc]; exact h2.2⟩

theorem allR_spec (f : Nat → Bool) (a m : Nat) (h : allR f a m = true) : ∀ i < m, f (a + i) = true := by
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    intro i hi
    rw [allR_succ, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih h.1 i hlt
    · rw [heq]; exact h.2

theorem allR_spec0 {f : Nat → Bool} {m : Nat} (h : allR f 0 m = true) : ∀ i < m, f i = true := fun i hi => by
  have e := allR_spec f 0 m h i hi
  rwa [Nat.zero_add] at e

/-- `f` holds somewhere on `a, a + 1, …, a + m - 1` -/
def anyR (f : Nat → Bool) (a m : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun i b => b || f (a + i)) m

theorem anyR_spec (f : Nat → Bool) (a m : Nat) (h : anyR f a m = true) : ∃ i < m, f (a + i) = true := by
  induction m with
  | zero =>
    have e : anyR f a 0 = false := rfl
    rw [e] at h
    exact absurd h (by decide)
  | succ m ih =>
    have h' : (anyR f a m || f (a + m)) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · obtain ⟨i, hi, hf⟩ := ih h1
      exact ⟨i, Nat.lt_succ_of_lt hi, hf⟩
    · exact ⟨m, Nat.lt_succ_self m, h1⟩

end B334.E1x.IPChk
