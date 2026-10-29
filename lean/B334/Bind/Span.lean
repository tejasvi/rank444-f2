import B334.Statement

/-! # Membership in `spanMasks` as a finite check (table binding groundwork)

Over F₂ the span of a list of masks is the set of XORs of its sublists. `xorSub B s` is the XOR of the `B[i]` with bit
`i` of `s` set; `inSpan B m` asks whether some `s < 2 ^ |B|` gives `m`. Theorem `mem_spanMasks_iff`: for masks below
`2 ^ 9`, `vecOfMask 9 m ∈ spanMasks B ↔ inSpan B m = true`, so membership and non-membership are `decide` facts. -/

namespace B334.Bind

open Finset

/-- XOR of the `B[i]` for the bits `i` of `s` -/
def xorSub : List ℕ → ℕ → ℕ
  | [], _ => 0
  | b :: B, s => (if s.testBit 0 then b else 0) ^^^ xorSub B (s / 2)

/-- `g k` for some `k < n` (one recursor loop) -/
def anyLT (n : ℕ) (g : ℕ → Bool) : Bool := @Nat.rec (fun _ => Bool) false (fun k ih => g k || ih) n

theorem anyLT_iff {n : ℕ} {g : ℕ → Bool} : anyLT n g = true ↔ ∃ k < n, g k = true := by
  induction n with
  | zero => simp [anyLT]
  | succ k ih =>
    show (g k || anyLT k g) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨j, hj, hg⟩)
      · exact ⟨k, Nat.lt_succ_self k, h⟩
      · exact ⟨j, Nat.lt_succ_of_lt hj, hg⟩
    · rintro ⟨j, hj, hg⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact Or.inr ⟨j, h, hg⟩
      · subst h; exact Or.inl hg

/-- is `m` the XOR of a sublist of `B`? -/
def inSpan (B : List ℕ) (m : ℕ) : Bool := anyLT (2 ^ B.length) (fun s => xorSub B s == m)

theorem vecOfMask_xor (n x y : ℕ) : vecOfMask n (x ^^^ y) = vecOfMask n x + vecOfMask n y := by
  funext p
  simp only [vecOfMask, Pi.add_apply, Nat.testBit_xor]
  cases x.testBit p.val <;> cases y.testBit p.val <;> decide

theorem vecOfMask_zero (n : ℕ) : vecOfMask n 0 = 0 := by
  funext p; simp [vecOfMask]

theorem xorSub_zero : ∀ (B : List ℕ), xorSub B 0 = 0
  | [] => rfl
  | b :: B => by simp [xorSub, xorSub_zero B]

theorem div_two_xor (s t : ℕ) : (s ^^^ t) / 2 = s / 2 ^^^ t / 2 :=
  Nat.eq_of_testBit_eq (fun i => by simp [Nat.testBit_div_two, Nat.testBit_xor])

theorem xorSub_xor : ∀ (B : List ℕ) (s t : ℕ), xorSub B (s ^^^ t) = xorSub B s ^^^ xorSub B t
  | [], _, _ => by simp [xorSub]
  | b :: B, s, t => by
    simp only [xorSub]
    rw [div_two_xor, xorSub_xor B, Nat.testBit_xor]
    cases s.testBit 0 <;> cases t.testBit 0 <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm, Nat.xor_self, Nat.xor_zero, Nat.zero_xor]

theorem xorSub_lt : ∀ (B : List ℕ) (s : ℕ), (∀ b ∈ B, b < 2 ^ 9) → xorSub B s < 2 ^ 9
  | [], _, _ => by simp [xorSub]
  | b :: B, s, h => by
    simp only [xorSub]
    apply Nat.xor_lt_two_pow
    · split_ifs
      · exact h b (by simp)
      · exact Nat.two_pow_pos 9
    · exact xorSub_lt B (s / 2) (fun x hx => h x (by simp [hx]))

theorem xorSub_mem : ∀ (B : List ℕ) (s : ℕ), vecOfMask (3 * 3) (xorSub B s) ∈ spanMasks B
  | [], _ => by simp only [xorSub, vecOfMask_zero]; exact Submodule.zero_mem _
  | b :: B, s => by
    simp only [xorSub, vecOfMask_xor]
    apply Submodule.add_mem
    · split_ifs
      · exact Submodule.subset_span ⟨b, by simp, rfl⟩
      · rw [vecOfMask_zero]; exact Submodule.zero_mem _
    · have h := xorSub_mem B (s / 2)
      refine Submodule.span_mono ?_ h
      rintro v ⟨m, hm, rfl⟩
      exact ⟨m, by simp [hm], rfl⟩

theorem xorSub_pow : ∀ (B : List ℕ) (i : ℕ) (hi : i < B.length), xorSub B (2 ^ i) = B[i]
  | [], i, h => by simp at h
  | b :: B, 0, _ => by simp [xorSub, xorSub_zero]
  | b :: B, i + 1, h => by
    simp only [xorSub]
    have h1 : (2 ^ (i + 1)).testBit 0 = false := by simp [Nat.testBit_two_pow]
    have h2 : 2 ^ (i + 1) / 2 = 2 ^ i := by rw [Nat.pow_succ]; omega
    rw [h1, h2, xorSub_pow B i (by simp at h; omega)]
    simp

/-- every element of the span is the XOR of a sublist -/
theorem exists_of_mem (B : List ℕ) (v : Fin (3 * 3) → ZMod 2) (hv : v ∈ spanMasks B) :
    ∃ s < 2 ^ B.length, vecOfMask (3 * 3) (xorSub B s) = v := by
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, hm, rfl⟩ := hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    exact ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) hi, by rw [xorSub_pow B i hi]⟩
  | zero => exact ⟨0, Nat.two_pow_pos _, by rw [xorSub_zero, vecOfMask_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s ^^^ t, Nat.xor_lt_two_pow hs ht, by rw [xorSub_xor, vecOfMask_xor]⟩
  | smul c x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    rcases h01 c with rfl | rfl
    · exact ⟨0, Nat.two_pow_pos _, by rw [xorSub_zero, vecOfMask_zero, zero_smul]⟩
    · exact ⟨s, hs, by rw [one_smul]⟩

theorem vecOfMask_inj {x y : ℕ} (hx : x < 2 ^ 9) (hy : y < 2 ^ 9)
    (h : vecOfMask (3 * 3) x = vecOfMask (3 * 3) y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 9
  · have := congrFun h ⟨i, by omega⟩
    simp only [vecOfMask] at this
    cases hxi : x.testBit i <;> cases hyi : y.testBit i <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- **Membership as a finite check.** -/
theorem mem_spanMasks_iff (B : List ℕ) (hB : ∀ b ∈ B, b < 2 ^ 9) (m : ℕ) (hm : m < 2 ^ 9) :
    vecOfMask (3 * 3) m ∈ spanMasks B ↔ inSpan B m = true := by
  rw [inSpan, anyLT_iff]
  constructor
  · intro h
    obtain ⟨s, hs, he⟩ := exists_of_mem B _ h
    exact ⟨s, hs, by rw [beq_iff_eq]; exact vecOfMask_inj (xorSub_lt B s hB) hm he⟩
  · rintro ⟨s, _, he⟩
    rw [beq_iff_eq] at he
    rw [← he]; exact xorSub_mem B s

end B334.Bind
