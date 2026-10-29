import B334.BCP.Check

/-! # The same induction for certificates given as `Cert` terms (`B334.BC.check`, `B334.BC.leaf`)

Port of `S5/CheckC.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0). Also `mkSS_ok`: the hit table of a list of first
factors is the packed one. -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core Matrix

theorem kidsOk_ok (f : Asg → List Rec → Cert → Bool) (a : Nat) (asg : Asg) (allr : List Rec) :
    ∀ (cs : List (Nat × Nat)) (ks : List Cert), kidsOk f a asg allr cs ks = true →
      ∀ p ∈ cs, ∃ k, f ((a, p.1, p.2) :: asg) (updRecs a p.1 p.2 allr) k = true := by
  intro cs
  induction cs with
  | nil => intro ks _ p hp; exact absurd hp List.not_mem_nil
  | cons q cs ih =>
    intro ks h p hp
    cases ks with
    | nil => exact absurd h Bool.false_ne_true
    | cons k ks' =>
      have h' : (f ((a, q.1, q.2) :: asg) (updRecs a q.1 q.2 allr) k && kidsOk f a asg allr cs ks') = true := h
      rw [Bool.and_eq_true] at h'
      rcases List.mem_cons.mp hp with e | e
      · exact ⟨k, e ▸ h'.1⟩
      · exact ih ks' h'.2 p e

theorem lt_of_dom {dom X : Nat} (hdom : dom < 2 ^ 512) (h : dom.testBit X = true) : X < 512 := by
  by_contra hX
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hdom (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
  exact absurd h Bool.false_ne_true

/-- **Soundness of the node induction** (`Cert` certificates). -/
theorem check_sound (T n dom SS : Nat) (hn : n ≤ 32) (hSS : SSok T n SS) (hdom : dom < 2 ^ 512) :
    ∀ fuel ACT asg recs (cert : Cert), check fuel T SS ACT asg recs dom cert = true →
      ∀ b c, Inv T n dom b c ACT asg recs → False := by
  intro fuel
  induction fuel with
  | zero => intro ACT asg recs cert h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro ACT asg recs cert hchk b c hinv
    rcases cert with X | ⟨t, nt, sl, sym, cdir, kids⟩
    · have h' : (bit dom X && elimOk (elim (resC X asg)) && Nat.blt (ucnt SS ACT X) (elim (resC X asg)).rk) = true :=
        hchk
      have hX : X < 512 := by
        have h2 := h'
        simp only [Bool.and_eq_true] at h2
        exact lt_of_dom hdom (by rw [← bit_eq]; exact h2.1.1)
      exact over_step T n dom hn SS hSS ACT asg recs X hX h' b c hinv
    · have h' : ((brData SS ACT asg recs dom (aT T t) nt sl sym cdir t).1 &&
          kidsOk (fun asg' recs' k => check fuel T SS (Nat.xor ACT (Nat.shiftLeft 1 t)) asg' recs' dom k)
            (aT T t) asg (brData SS ACT asg recs dom (aT T t) nt sl sym cdir t).2.1
            (brData SS ACT asg recs dom (aT T t) nt sl sym cdir t).2.2 kids) = true := hchk
      rw [Bool.and_eq_true] at h'
      obtain ⟨hd1, hk⟩ := h'
      have hd1' : (bit ACT t && (!sym || (asg.isEmpty && !cdir)) && allDom dom nt &&
          (mkRecs SS ACT asg nt []).1 && allDom dom sl && allThru (aT T t) sl && (mkSls SS ACT asg sl).1) = true := hd1
      simp only [Bool.and_eq_true] at hd1'
      obtain ⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, h5⟩, _⟩, _⟩ := hd1'
      refine br_step T n dom hn SS hSS ACT asg recs t sym cdir nt sl
        (fun x hx => lt_of_dom hdom (allDom_spec dom nt h3 x hx))
        (fun x hx => lt_of_dom hdom (allDom_spec dom sl h5 x hx)) hd1 ?_ b c hinv
      intro p hp b' c' hinv'
      obtain ⟨k, hk'⟩ := kidsOk_ok _ _ _ _ _ kids hk p hp
      exact ih _ _ _ k hk' b' c' hinv'

/-! ## Packed terms of a `Cert` leaf -/

theorem testBit_511 (j : Nat) : Nat.testBit 511 j = decide (j < 9) := by
  rw [show (511 : Nat) = 2 ^ 9 - 1 by norm_num, Nat.testBit_two_pow_sub_one]

theorem lt512_bit (b j : Nat) (hb : b < 512) (hj : 9 ≤ j) : b.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (by
    calc 512 = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))

theorem mkSSAux_bit : ∀ (l : List Nat) (s0 : Nat), (∀ a ∈ l, a < 512) → s0 + l.length ≤ 32 → ∀ k s, k < 9 → s < 32 →
    (mkSSAux l s0).testBit (32 * k + s) = (decide (s0 ≤ s ∧ s < s0 + l.length) && (l.getD (s - s0) 0).testBit k) := by
  intro l
  induction l with
  | nil => intro s0 _ _ k s _ _; simp [mkSSAux]
  | cons a l ih =>
    intro s0 hl hlen k s hk hs
    have ha := hl a List.mem_cons_self
    show ((dep32 a <<< s0) ||| mkSSAux l (s0 + 1)).testBit (32 * k + s) = _
    rw [Nat.testBit_or, ih (s0 + 1) (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (by simp at hlen ⊢; omega) k s hk hs,
      Nat.testBit_shiftLeft, dep32_bit a ha]
    simp only [List.length_cons]
    by_cases e : s = s0
    · subst e
      have e0 : 32 * k + s - s = 32 * k := by omega
      have e1 : 32 * k % 32 = 0 ∧ 32 * k < 288 := by omega
      have e2 : 32 * k / 32 = k := by omega
      rw [e0, e2, decide_eq_true e1]
      simp
    · have e1 : ¬ (32 * k + s ≥ s0 ∧ (32 * k + s - s0) % 32 = 0 ∧ 32 * k + s - s0 < 288) := by
        simp at hlen; omega
      have hfirst : (decide (32 * k + s ≥ s0) && (decide ((32 * k + s - s0) % 32 = 0 ∧ 32 * k + s - s0 < 288) &&
          a.testBit ((32 * k + s - s0) / 32))) = false := by
        by_cases e2 : 32 * k + s ≥ s0
        · have e4 : ¬ ((32 * k + s - s0) % 32 = 0 ∧ 32 * k + s - s0 < 288) := fun x => e1 ⟨e2, x⟩
          simp [e2, e4]
        · simp [e2]
      rw [hfirst, Bool.false_or]
      by_cases hlt : s0 < s
      · have e3 : s - s0 = (s - (s0 + 1)) + 1 := by omega
        rw [e3, List.getD_cons_succ]
        have e5 : (s0 + 1 ≤ s ∧ s < s0 + 1 + l.length) ↔ (s0 ≤ s ∧ s < s0 + (l.length + 1)) := by omega
        simp only [e5]
      · have e5 : ¬ (s0 + 1 ≤ s ∧ s < s0 + 1 + l.length) := by omega
        have e6 : ¬ (s0 ≤ s ∧ s < s0 + (l.length + 1)) := by omega
        rw [decide_eq_false e5, decide_eq_false e6, Bool.false_and, Bool.false_and]

theorem aT_packT : ∀ (l : List Nat), (∀ a ∈ l, a < 512) → ∀ t, aT (packT l) t = l.getD t 0 := by
  intro l
  induction l with
  | nil => intro _ t; simp [aT, packT]
  | cons a l ih =>
    intro hl t
    have ha := hl a List.mem_cons_self
    have hP : packT (a :: l) = a ||| (packT l <<< 9) := rfl
    cases t with
    | zero =>
      show aT (packT (a :: l)) 0 = a
      apply Nat.eq_of_testBit_eq; intro i
      show ((packT (a :: l) >>> (9 * 0)) &&& 511).testBit i = _
      rw [hP, Nat.testBit_and, testBit_511, Nat.mul_zero, Nat.shiftRight_zero, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hi : i < 9
      · have : ¬ (i ≥ 9) := by omega
        simp [hi, this]
      · rw [lt512_bit a i ha (by omega)]; simp [hi]
    | succ t =>
      rw [List.getD_cons_succ, ← ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) t]
      apply Nat.eq_of_testBit_eq; intro i
      show ((packT (a :: l) >>> (9 * (t + 1))) &&& 511).testBit i = ((packT l >>> (9 * t)) &&& 511).testBit i
      rw [hP, Nat.testBit_and, Nat.testBit_and, testBit_511, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
        Nat.testBit_or, Nat.testBit_shiftLeft, lt512_bit a _ ha (by omega)]
      have e1 : 9 * (t + 1) + i ≥ 9 := by omega
      have e2 : 9 * (t + 1) + i - 9 = 9 * t + i := by omega
      simp [e1, e2]

theorem mkSS_ok (terms : List Nat) (hl : ∀ a ∈ terms, a < 512) (hlen : terms.length ≤ 32) :
    SSok (packT terms) terms.length (mkSS terms) := by
  intro k s hk hs
  show (mkSSAux terms 0).testBit (32 * k + s) = _
  rw [mkSSAux_bit terms 0 hl (by omega) k s hk hs, aT_packT terms hl, Nat.sub_zero]
  simp

end B334.BCP
