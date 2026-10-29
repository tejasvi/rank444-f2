import B334.BCP.CheckC

/-! # Leaf and batch theorems for BranchCheck334 (the soundness theorem)

Port of `S5/Leaf.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0).

`NoDecomp T n dom`: no nonzero 12-bit `b_t, c_t` (`t < n`) with `T(X) = ∑_{t : X(a_t) = 1} b_t c_tᵀ` for every
functional `X` of the domain mask `dom`, where `a_t` is the `t`-th 9-bit first factor packed in `T`. For a
domain inside `E^⊥ ∖ {0}` this is the statement for the quotient leaf; the domain comes from the
IP (`DomPerp`) in the E1 interface.

* `leafS_sound`: a stream leaf record accepted by `leafS` (`n ≤ 31`, dom mode `01`, the 512-bit mask, an accepted
  certificate, nothing after it) gives `NoDecomp` of its terms on its mask;
* `batch_sound`: every leaf of an accepted batch;
* `leaf_sound`: the same for `Cert` terms;
* `noDecomp_mat`: `NoDecomp` stated with the matrices of `B334.Core` (`TX`, `hitSet`, `vecB`, `vecC`), the form the
  bridge to `QuotLB` uses. -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core Matrix

def NoDecomp (T n dom : Nat) : Prop :=
  ¬ ∃ b c : Nat → Nat, BC n b c ∧ ∀ X, X < 512 → dom.testBit X = true →
    TX (toM3 X) = ∑ t ∈ (Finset.range n).filter (fun t => par (aT T t &&& X) = true), vecMulVec (nv (b t)) (nv (c t))

theorem hitS_full (T n X : Nat) :
    hitS T n (2 ^ n - 1) X = (Finset.range n).filter (fun t => par (aT T t &&& X) = true) := by
  ext t
  simp only [hitS, Finset.mem_filter, Finset.mem_range, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, h1, h3⟩

theorem inv_root (T n dom : Nat) (b c : Nat → Nat) (hbc : BC n b c)
    (hd : ∀ X, X < 512 → dom.testBit X = true →
      TX (toM3 X) = ∑ t ∈ (Finset.range n).filter (fun t => par (aT T t &&& X) = true), vecMulVec (nv (b t)) (nv (c t))) :
    Inv T n dom b c (2 ^ n - 1) [] [] := by
  refine ⟨fun t ht => ?_, hbc, fun e he => absurd he List.not_mem_nil, fun X hX hdom => ?_, fun _ => rfl,
    fun r hr => absurd hr List.not_mem_nil⟩
  · rw [Nat.testBit_two_pow_sub_one] at ht; simpa using ht
  · rw [resM_nil, hitS_full]; exact hd X hX hdom

/-! ## Stream leaves and batches -/

def leafN (R : Nat) : Nat := rd 6 R
def leafT (R : Nat) : Nat := rd (Nat.mul 9 (rd 6 R)) (sk 6 R)
def leafDom (R : Nat) : Nat := rd 512 (sk 2 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))

/-- **Leaf theorem (stream format).** -/
theorem leafS_sound (R : Nat) (h : leafS R = true) : NoDecomp (leafT R) (leafN R) (leafDom R) := by
  rintro ⟨b, c, hbc, hd⟩
  have h' : (Nat.ble (rd 6 R) 31 && Nat.beq (rd 2 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 1 &&
      (checkS 64 (leafT R) (mkSSP (leafT R) (rd 6 R)) (Nat.pred (Nat.shiftLeft 1 (rd 6 R))) [] [] (leafDom R)
        (sk 514 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))).1 &&
      Nat.beq (checkS 64 (leafT R) (mkSSP (leafT R) (rd 6 R)) (Nat.pred (Nat.shiftLeft 1 (rd 6 R))) [] [] (leafDom R)
        (sk 514 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))).2 0) = true := h
  have e : Nat.pred (Nat.shiftLeft 1 (rd 6 R)) = 2 ^ rd 6 R - 1 := by
    show 1 <<< rd 6 R - 1 = _; rw [Nat.one_shiftLeft]
  rw [e] at h'
  simp only [Bool.and_eq_true, Nat.ble_eq] at h'
  obtain ⟨⟨⟨hn, _⟩, hchk⟩, _⟩ := h'
  exact checkS_sound (leafT R) (leafN R) (leafDom R) hn 64 _ [] [] _ hchk b c (inv_root _ _ _ b c hbc hd)

/-- the leaf records of a batch -/
def leaves : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, D => cond (Nat.beq (rd 1 D) 1) [sk 1 D]
      (leaves fuel (rd (rd 24 (sk 1 D)) (sk 25 D)) ++ leaves fuel (sk (Nat.add 25 (rd 24 (sk 1 D))) D))

theorem batch_leaves : ∀ fuel D, batch fuel D = true → ∀ R ∈ leaves fuel D, leafS R = true := by
  intro fuel
  induction fuel with
  | zero => intro D h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro D h R hR
    have hb : batch (fuel + 1) D = cond (Nat.beq (rd 1 D) 1) (leafS (sk 1 D))
        (batch fuel (rd (rd 24 (sk 1 D)) (sk 25 D)) && batch fuel (sk (Nat.add 25 (rd 24 (sk 1 D))) D)) := rfl
    have hl : leaves (fuel + 1) D = cond (Nat.beq (rd 1 D) 1) [sk 1 D]
        (leaves fuel (rd (rd 24 (sk 1 D)) (sk 25 D)) ++ leaves fuel (sk (Nat.add 25 (rd 24 (sk 1 D))) D)) := rfl
    rw [hb] at h; rw [hl] at hR
    cases e : Nat.beq (rd 1 D) 1
    · rw [e, cond_false, Bool.and_eq_true] at h
      rw [e, cond_false] at hR
      rcases List.mem_append.mp hR with h1 | h1
      · exact ih _ h.1 R h1
      · exact ih _ h.2 R h1
    · rw [e, cond_true] at h
      rw [e, cond_true] at hR
      rw [List.mem_singleton.mp hR]; exact h

/-- **Batch theorem.** Every leaf of an accepted batch has no decomposition. -/
theorem batch_sound (fuel D : Nat) (h : batch fuel D = true) :
    ∀ R ∈ leaves fuel D, NoDecomp (leafT R) (leafN R) (leafDom R) :=
  fun R hR => leafS_sound R (batch_leaves fuel D h R hR)

/-! ## `Cert` leaves -/

/-- **Leaf theorem (`Cert` format).** -/
theorem leaf_sound (terms : List Nat) (dom : Nat) (cert : Cert) (h : leaf terms dom cert = true)
    (hterms : ∀ a ∈ terms, a < 512) (hdom : dom < 2 ^ 512) : NoDecomp (packT terms) terms.length dom := by
  rintro ⟨b, c, hbc, hd⟩
  have h' : (Nat.ble terms.length 31 && check 64 (packT terms) (mkSS terms) (2 ^ terms.length - 1) [] [] dom cert) =
      true := by
    have e : Nat.pred (Nat.shiftLeft 1 terms.length) = 2 ^ terms.length - 1 := by
      show 1 <<< terms.length - 1 = _; rw [Nat.one_shiftLeft]
    rw [← e]; exact h
  rw [Bool.and_eq_true, Nat.ble_eq] at h'
  exact check_sound (packT terms) terms.length dom (mkSS terms) (by omega) (mkSS_ok terms hterms (by omega)) hdom 64
    _ [] [] cert h'.2 b c (inv_root _ _ _ b c hbc hd)

/-! ## In terms of the matrices of `B334.Core` -/

theorem vecB_inj (M : M34) (h : vecB M = 0) : M = 0 := by
  ext j k
  have := congrFun h ⟨4 * j.val + k.val, by omega⟩
  simp only [vecB, Pi.zero_apply] at this
  have e1 : hiB ⟨4 * j.val + k.val, by omega⟩ = j := by apply Fin.ext; simp only [hiB]; omega
  have e2 : loB ⟨4 * j.val + k.val, by omega⟩ = k := by apply Fin.ext; simp only [loB]; omega
  rw [e1, e2] at this; exact this

theorem vecC_inj (M : M43) (h : vecC M = 0) : M = 0 := by
  ext k i
  have := congrFun h ⟨3 * k.val + i.val, by omega⟩
  simp only [vecC, Pi.zero_apply] at this
  have e1 : hiC ⟨3 * k.val + i.val, by omega⟩ = k := by apply Fin.ext; simp only [hiC]; omega
  have e2 : loC ⟨3 * k.val + i.val, by omega⟩ = i := by apply Fin.ext; simp only [loC]; omega
  rw [e1, e2] at this; exact this

/-- **`NoDecomp` with matrices.** No nonzero `b_s ∈ F₂^{3×4}`, `c_s ∈ F₂^{4×3}` (`s < n`) make
`T(X) = ∑_{s : X(a_s) = 1} vecB(b_s) vecC(c_s)ᵀ` for every functional `X` of the domain. -/
theorem noDecomp_mat {T n dom : Nat} (h : NoDecomp T n dom) (b : Fin n → M34) (c : Fin n → M43)
    (hbc : ∀ s, b s ≠ 0 ∧ c s ≠ 0) :
    ¬ (∀ X, X < 512 → dom.testBit X = true →
      TX (toM3 X) = ∑ s ∈ hitSet (fun s : Fin n => toM3 (aT T s.val)) (toM3 X), vecMulVec (vecB (b s)) (vecC (c s))) := by
  intro hd
  apply h
  let b' : Nat → Nat := fun t => if ht : t < n then natOf (vecB (b ⟨t, ht⟩)) else 1
  let c' : Nat → Nat := fun t => if ht : t < n then natOf (vecC (c ⟨t, ht⟩)) else 1
  refine ⟨b', c', fun t ht => ?_, fun X hX hdom => ?_⟩
  · simp only [b', c', dif_pos ht]
    refine ⟨Nat.pos_of_ne_zero (fun e => (hbc ⟨t, ht⟩).1 (vecB_inj _ ?_)), natOf_lt _,
      Nat.pos_of_ne_zero (fun e => (hbc ⟨t, ht⟩).2 (vecC_inj _ ?_)), natOf_lt _⟩
    · rw [← nv_natOf (vecB (b ⟨t, ht⟩)), e]; funext i; simp [nv, bitF]
    · rw [← nv_natOf (vecC (c ⟨t, ht⟩)), e]; funext i; simp [nv, bitF]
  · rw [hd X hX hdom]
    have hmap : (hitSet (fun s : Fin n => toM3 (aT T s.val)) (toM3 X)).map Fin.valEmbedding =
        (Finset.range n).filter (fun t => par (aT T t &&& X) = true) := by
      ext t
      simp only [Finset.mem_map, hitSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
        Finset.mem_range]
      constructor
      · rintro ⟨s, hs, rfl⟩
        rw [pair_par X _ hX (aT_lt T _)] at hs
        exact ⟨s.isLt, by cases e : par (aT T s.val &&& X) <;> simp_all [bf]⟩
      · rintro ⟨ht, hp⟩
        refine ⟨⟨t, ht⟩, ?_, rfl⟩
        rw [pair_par X _ hX (aT_lt T _), hp]; rfl
    rw [← hmap, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Fin.valEmbedding_apply, b', c', dif_pos s.isLt, nv_natOf]

end B334.BCP
