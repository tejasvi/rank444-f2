import B334.E1x.Fact
import B334.BCP.Count

/-! # Padding: refuting "exactly `R` outside `E`" gives the bound `R + 1`

Port of `HC/Pad.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to ⟨3,3,4⟩ (second factors 3×4, third factors 4×3).
An E1 run concludes `E1Concl m R`: no decomposition of ⟨3,3,4⟩ whose `b`, `c` are all nonzero has exactly `R` first
factors outside the point mask `m`.

* `split_step`: a term `(a, b, c)` outside `m` splits into `(a, b, y)` and `(a, b, c + y)` with `y ≠ 0`, `c + y ≠ 0`.
* `drop_zero`: dropping the terms with `b = 0` or `c = 0` keeps a decomposition.
* **`pad`**: `E1Concl m R → Fact m 1 → Fact m (R + 1)`.
* **`fact_one`**: `Fact m 1` for every `m` inside a hyperplane `X^⊥` (`X ≠ 0`), since `T(X) ≠ 0`; `oneOK m X` checks
  the hypotheses in one loop over the 512 masks. -/

namespace B334.E1x

open B334.Core Matrix Finset

/-- the conclusion of an E1 run -/
def E1Concl (m R : Nat) : Prop :=
  ∀ (n : ℕ) (av : Fin n → ℕ) (b : Fin n → M34) (c : Fin n → M43), (∀ s, av s < 512) →
    IsDecomp (fun s => toM3 (av s)) b c → (∀ s, b s ≠ 0 ∧ c s ≠ 0) →
    (univ.filter (fun s : Fin n => m.testBit (av s) = false)).card = R → False

/-! ## Splitting one term -/

theorem f2_add_eq_zero : ∀ x y : F2, x + y = 0 → x = y := by decide

theorem m43_add_eq_zero {x y : M43} (h : x + y = 0) : x = y := by
  ext i j
  exact f2_add_eq_zero _ _ (by simpa using congrFun (congrFun h i) j)

/-- two distinct nonzero 4×3 matrices -/
def e00 : M43 := fun i j => if i = 0 ∧ j = 0 then 1 else 0
def e01 : M43 := fun i j => if i = 0 ∧ j = 1 then 1 else 0

theorem pick (x : M43) : ∃ y : M43, y ≠ 0 ∧ x + y ≠ 0 := by
  have h1 : e00 ≠ 0 := fun h => by
    have := congrFun (congrFun h 0) 0; simp [e00] at this
  have h2 : e01 ≠ 0 := fun h => by
    have := congrFun (congrFun h 0) 1; simp [e01] at this
  have h12 : e00 ≠ e01 := fun h => by
    have := congrFun (congrFun h 0) 0; simp [e00, e01] at this
  by_cases hx : x = e00
  · exact ⟨e01, h2, fun h => h12 (hx ▸ m43_add_eq_zero h)⟩
  · exact ⟨e00, h1, fun h => hx (m43_add_eq_zero h)⟩

theorem f2_cancel : ∀ x S : F2, x + (S + x) = S := by decide

theorem split_step {m : Nat} {n : ℕ} {av : Fin n → ℕ} {b : Fin n → M34} {c : Fin n → M43} (hav : ∀ s, av s < 512)
    (hd : IsDecomp (fun s => toM3 (av s)) b c) (hbc : ∀ s, b s ≠ 0 ∧ c s ≠ 0) (s0 : Fin n)
    (hs0 : m.testBit (av s0) = false) :
    ∃ (av' : Fin (n + 1) → ℕ) (b' : Fin (n + 1) → M34) (c' : Fin (n + 1) → M43), (∀ s, av' s < 512) ∧
      IsDecomp (fun s => toM3 (av' s)) b' c' ∧ (∀ s, b' s ≠ 0 ∧ c' s ≠ 0) ∧
      (univ.filter (fun s => m.testBit (av' s) = false)).card =
        (univ.filter (fun s => m.testBit (av s) = false)).card + 1 := by
  obtain ⟨y, hy0, hy⟩ := pick (c s0)
  refine ⟨Fin.cons (av s0) av, Fin.cons (b s0) b, Fin.cons y (fun s => c s + if s = s0 then y else 0), ?_, ?_, ?_, ?_⟩
  · intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · simp only [Fin.cons_zero]; exact hav s0
    · simp only [Fin.cons_succ]; exact hav i
  · intro i j j' k k' i'
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Matrix.add_apply]
    have e : ∀ s, toM3 (av s) i j * b s j' k * (c s k' i' + (if s = s0 then y else 0) k' i') =
        toM3 (av s) i j * b s j' k * c s k' i' + (if s = s0 then toM3 (av s0) i j * b s0 j' k * y k' i' else 0) := by
      intro s
      by_cases h : s = s0
      · subst h; simp only [if_true]; ring
      · simp only [h, if_false, Matrix.zero_apply, add_zero]
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hd i j j' k k' i']
    exact f2_cancel _ _
  · intro s
    refine Fin.cases ⟨(hbc s0).1, hy0⟩ (fun i => ?_) s
    simp only [Fin.cons_succ]
    refine ⟨(hbc i).1, ?_⟩
    by_cases h : i = s0
    · subst h; simpa using hy
    · simpa [h] using (hbc i).2
  · rw [Fin.card_filter_univ_succ']
    simp only [Fin.cons_zero, Fin.cons_succ, hs0, if_true]
    omega

/-! ## Dropping zero terms -/

theorem drop_zero {m : Nat} {n : ℕ} {av : Fin n → ℕ} {b : Fin n → M34} {c : Fin n → M43} (hav : ∀ s, av s < 512)
    (hd : IsDecomp (fun s => toM3 (av s)) b c) :
    ∃ (n' : ℕ) (av' : Fin n' → ℕ) (b' : Fin n' → M34) (c' : Fin n' → M43), (∀ s, av' s < 512) ∧
      IsDecomp (fun s => toM3 (av' s)) b' c' ∧ (∀ s, b' s ≠ 0 ∧ c' s ≠ 0) ∧
      (univ.filter (fun s => m.testBit (av' s) = false)).card ≤
        (univ.filter (fun s => m.testBit (av s) = false)).card := by
  classical
  let p : Fin n → Prop := fun s => b s ≠ 0 ∧ c s ≠ 0
  let e := (Fintype.equivFin {s // p s}).symm
  refine ⟨Fintype.card {s // p s}, fun i => av (e i).1, fun i => b (e i).1, fun i => c (e i).1,
    fun i => hav _, ?_, fun i => (e i).2, ?_⟩
  · intro i j j' k k' i'
    rw [← hd i j j' k k' i']
    rw [Equiv.sum_comp e (fun x : {s // p s} => toM3 (av x.1) i j * b x.1 j' k * c x.1 k' i')]
    rw [← Finset.sum_subtype (univ.filter p) (fun x => by simp) (fun s => toM3 (av s) i j * b s j' k * c s k' i')]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : p s
    · rw [if_pos h]
    · rw [if_neg h]
      simp only [p, not_and_or, not_not] at h
      rcases h with h | h <;> simp [h]
  · apply Finset.card_le_card_of_injOn (fun i => (e i).1)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      exact hi
    · intro i _ i' _ h
      exact e.injective (Subtype.ext h)

/-! ## Padding -/

theorem pad_up {m R : Nat} (hE : E1Concl m R) : ∀ (k n : ℕ) (av : Fin n → ℕ) (b : Fin n → M34) (c : Fin n → M43),
    (∀ s, av s < 512) → IsDecomp (fun s => toM3 (av s)) b c → (∀ s, b s ≠ 0 ∧ c s ≠ 0) →
    1 ≤ (univ.filter (fun s : Fin n => m.testBit (av s) = false)).card →
    (univ.filter (fun s : Fin n => m.testBit (av s) = false)).card + k = R → False := by
  intro k
  induction k with
  | zero => intro n av b c hav hd hbc _ hk; exact hE n av b c hav hd hbc (by simpa using hk)
  | succ k ih =>
    intro n av b c hav hd hbc h1 hk
    obtain ⟨s0, hs0⟩ : ∃ s0, m.testBit (av s0) = false := by
      obtain ⟨s0, hs⟩ := Finset.card_pos.mp h1
      exact ⟨s0, (Finset.mem_filter.mp hs).2⟩
    obtain ⟨av', b', c', hav', hd', hbc', hcnt⟩ := split_step hav hd hbc s0 hs0
    exact ih _ av' b' c' hav' hd' hbc' (by omega) (by omega)

/-- **Padding (L4b).** -/
theorem pad {m R : Nat} (hE : E1Concl m R) (h1 : Fact m 1) : Fact m (R + 1) := by
  intro n av b c hav hd
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n', av', b', c', hav', hd', hbc', hle⟩ := drop_zero (m := m) hav hd
  have h1' := h1 n' av' b' c' hav' hd'
  exact pad_up hE (R - (univ.filter (fun s : Fin n' => m.testBit (av' s) = false)).card) n' av' b' c' hav' hd' hbc' h1'
    (by omega)

/-! ## `Fact m 1` for a point mask inside a hyperplane -/

theorem exists_bit {X : Nat} (hX0 : X ≠ 0) (hX : X < 512) : ∃ i j : Fin 3, X.testBit (3 * i.val + j.val) = true := by
  by_contra hno
  simp only [not_exists] at hno
  apply hX0
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.zero_testBit]
  by_cases hk : k < 9
  · have := hno ⟨k / 3, by omega⟩ ⟨k % 3, by omega⟩
    simp only at this
    rw [show 3 * (k / 3) + k % 3 = k by omega] at this
    simpa using this
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- **`Fact m 1`** for `m` inside the hyperplane `X^⊥`, `X ≠ 0`: if every first factor lay in `m`, the contraction of
`T` with `X` would vanish, but `T(X) ≠ 0`. -/
theorem fact_one {m X : Nat} (hX0 : X ≠ 0) (hX : X < 512)
    (hm : ∀ w < 512, m.testBit w = true → B334.BC.par (w &&& X) = false) : Fact m 1 := by
  intro n av b c hav hd
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have hall : ∀ s, pair (toM3 X) (toM3 (av s)) = 0 := by
    intro s
    have hin : m.testBit (av s) = true := by
      have := h0 (Finset.mem_univ s)
      simpa using this
    have e : pair (toM3 X) (toM3 (av s)) = bf (B334.BC.par (av s &&& X)) := B334.BCP.pair_par X (av s) hX (hav s)
    rw [e, hm (av s) (hav s) hin]
    rfl
  obtain ⟨i, j, hij⟩ := exists_bit hX0 hX
  have hc := contract hd (toM3 X) ⟨4 * j.val, by omega⟩ ⟨i.val, by omega⟩
  simp only [hall, zero_mul, Finset.sum_const_zero] at hc
  have hlo : loB ⟨4 * j.val, by omega⟩ = hiC ⟨i.val, by omega⟩ := by
    apply Fin.ext; simp only [loB, hiC]; omega
  unfold TX at hc
  rw [if_pos hlo] at hc
  have e1 : loC ⟨i.val, by omega⟩ = i := by apply Fin.ext; simp only [loC]; omega
  have e2 : hiB ⟨4 * j.val, by omega⟩ = j := by apply Fin.ext; simp only [hiB]; omega
  rw [e1, e2] at hc
  simp only [toM3, bitF, hij, if_true] at hc
  exact absurd hc (by decide)

/-- the hypotheses of `fact_one` as one check: `X ≠ 0`, `X < 512`, and every mask of `m` below 512 orthogonal to `X` -/
def oneOK (m X : Nat) : Bool :=
  !(X == 0) && Nat.blt X 512 && allLT 512 (fun w => !(m.testBit w) || !(B334.BC.par (w &&& X)))

theorem fact_one' {m X : Nat} (h : oneOK m X = true) : Fact m 1 := by
  unfold oneOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, Nat.blt_eq] at h
  obtain ⟨⟨hX0, hX⟩, hall⟩ := h
  refine fact_one hX0 hX (fun w hw hmw => ?_)
  have := allLT_spec hall w hw
  rw [hmw] at this
  simpa using this

end B334.E1x
