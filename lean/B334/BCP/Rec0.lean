import B334.BCP.Base
import B334.BCP.Sem

/-! # Records and the checker's list helpers (first part of the port of `S5/Rec.lean`)

`RecOK`: a tight record built at a node stays valid below it. The masks contain the factors of every active term it
hits, and `⟨c_s, x(b_t)⟩ = δ_st`; the duality is the 12-bit parity `par12`. The list lemmas say what
`thru`, `app`, `andLm`, `andRm`, `cmT`, `bmT`, `cmS`, `bmS`, `updRecs`, `mkRecs`, `mkSls`, `allDom` and `allThru`
compute. The validity of computed records (`mkRec_sound`, `mkSl_sound`) and the update (`updRec_ok`) need the
bit-level semantics of group C and are in `BCP/Rec.lean`. -/

namespace B334.BCP

open B334.BC B334.Core

def RecOK (T n : Nat) (b c : Nat → Nat) (ACT : Nat) (r : Rec) : Prop :=
  r.X < 512 ∧
  (∀ s t, s ∈ hitS T n ACT r.X → t ∈ hitS T n ACT r.X → par12 (c s &&& xof r.P (b t)) = decide (s = t)) ∧
  (∀ t ∈ hitS T n ACT r.X, r.lm.testBit (b t) = true ∧ r.rm.testBit (c t) = true)

theorem mem_thru (a : Nat) (l tail : List Rec) (r : Rec) :
    r ∈ thru a l tail → (r ∈ l ∧ par (Nat.land r.X a) = true) ∨ r ∈ tail := by
  induction l with
  | nil => intro h; exact Or.inr h
  | cons r0 l ih =>
    intro h
    have e : thru a (r0 :: l) tail = cond (par (Nat.land r0.X a)) (r0 :: thru a l tail) (thru a l tail) := rfl
    rw [e] at h
    cases hp : par (Nat.land r0.X a)
    · rw [hp, cond_false] at h
      rcases ih h with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
      · exact Or.inr h1
    · rw [hp, cond_true] at h
      rcases List.mem_cons.mp h with h1 | h1
      · subst h1; exact Or.inl ⟨List.mem_cons_self, hp⟩
      · rcases ih h1 with ⟨h2, h3⟩ | h2
        · exact Or.inl ⟨List.mem_cons_of_mem _ h2, h3⟩
        · exact Or.inr h2

theorem mem_app (l tail : List Rec) (r : Rec) : r ∈ app l tail → r ∈ l ∨ r ∈ tail := by
  induction l with
  | nil => intro h; exact Or.inr h
  | cons r0 l ih =>
    intro h
    rcases List.mem_cons.mp (show r ∈ r0 :: app l tail from h) with h1 | h1
    · exact Or.inl (h1 ▸ List.mem_cons_self)
    · rcases ih h1 with h2 | h2
      · exact Or.inl (List.mem_cons_of_mem _ h2)
      · exact Or.inr h2

theorem andLm_bit (l : List Rec) : ∀ (m w : Nat), m.testBit w = true → (∀ r ∈ l, r.lm.testBit w = true) →
    (andLm l m).testBit w = true := by
  induction l with
  | nil => intro m w hm _; exact hm
  | cons r l ih =>
    intro m w hm hl
    show (andLm l (Nat.land m r.lm)).testBit w = true
    exact ih _ w (by rw [show Nat.land m r.lm = m &&& r.lm from rfl, Nat.testBit_and, hm, hl r List.mem_cons_self]; rfl)
      (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr'))

theorem andRm_bit (l : List Rec) : ∀ (m w : Nat), m.testBit w = true → (∀ r ∈ l, r.rm.testBit w = true) →
    (andRm l m).testBit w = true := by
  induction l with
  | nil => intro m w hm _; exact hm
  | cons r l ih =>
    intro m w hm hl
    show (andRm l (Nat.land m r.rm)).testBit w = true
    exact ih _ w (by rw [show Nat.land m r.rm = m &&& r.rm from rfl, Nat.testBit_and, hm, hl r List.mem_cons_self]; rfl)
      (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr'))

theorem andLm_le (l : List Rec) : ∀ m, andLm l m ≤ m := by
  induction l with
  | nil => intro m; exact le_rfl
  | cons r l ih => intro m; exact le_trans (ih _) Nat.and_le_left

theorem andRm_le (l : List Rec) : ∀ m, andRm l m ≤ m := by
  induction l with
  | nil => intro m; exact le_rfl
  | cons r l ih => intro m; exact le_trans (ih _) Nat.and_le_left

theorem cmT_bit (bb : Nat) (l : List Rec) : ∀ (m w : Nat), m.testBit w = true →
    (∀ r ∈ l, (nperp (xof r.P bb)).testBit w = true) → (cmT bb l m).testBit w = true := by
  induction l with
  | nil => intro m w hm _; exact hm
  | cons r l ih =>
    intro m w hm hl
    show (cmT bb l (Nat.land m (nperp (xof r.P bb)))).testBit w = true
    exact ih _ w (by
        rw [show Nat.land m (nperp (xof r.P bb)) = m &&& nperp (xof r.P bb) from rfl, Nat.testBit_and, hm,
          hl r List.mem_cons_self]; rfl)
      (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr'))

theorem bmT_bit (cc : Nat) (l : List Rec) : ∀ (m w : Nat), m.testBit w = true →
    (∀ r ∈ l, (nperp (gof r.P cc)).testBit w = true) → (bmT cc l m).testBit w = true := by
  induction l with
  | nil => intro m w hm _; exact hm
  | cons r l ih =>
    intro m w hm hl
    show (bmT cc l (Nat.land m (nperp (gof r.P cc)))).testBit w = true
    exact ih _ w (by
        rw [show Nat.land m (nperp (gof r.P cc)) = m &&& nperp (gof r.P cc) from rfl, Nat.testBit_and, hm,
          hl r List.mem_cons_self]; rfl)
      (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr'))

theorem cmS_bit (bb : Nat) (l : List (Bool × Nat × Nat)) : ∀ (m w : Nat), m.testBit w = true →
    (∀ sd ∈ l, sd.2.1.testBit bb = true ∨ sd.2.2.testBit w = true) → (cmS bb l m).testBit w = true := by
  induction l with
  | nil => intro m w hm _; exact hm
  | cons sd l ih =>
    intro m w hm hl
    have e : cmS bb (sd :: l) m = cmS bb l (cond (bit sd.2.1 bb) m (Nat.land m sd.2.2)) := rfl
    rw [e]
    apply ih _ w _ (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs'))
    rw [bit_eq]
    cases h1 : sd.2.1.testBit bb
    · rw [cond_false, show Nat.land m sd.2.2 = m &&& sd.2.2 from rfl, Nat.testBit_and, hm]
      rcases hl sd List.mem_cons_self with h | h
      · rw [h1] at h; exact absurd h (by decide)
      · rw [h]; rfl
    · rw [cond_true]; exact hm

theorem bmS_bit (cc : Nat) (l : List (Bool × Nat × Nat)) : ∀ (m w : Nat), m.testBit w = true →
    (∀ sd ∈ l, sd.2.2.testBit cc = true ∨ sd.2.1.testBit w = true) → (bmS cc l m).testBit w = true := by
  induction l with
  | nil => intro m w hm _; exact hm
  | cons sd l ih =>
    intro m w hm hl
    have e : bmS cc (sd :: l) m = bmS cc l (cond (bit sd.2.2 cc) m (Nat.land m sd.2.1)) := rfl
    rw [e]
    apply ih _ w _ (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs'))
    rw [bit_eq]
    cases h1 : sd.2.2.testBit cc
    · rw [cond_false, show Nat.land m sd.2.1 = m &&& sd.2.1 from rfl, Nat.testBit_and, hm]
      rcases hl sd List.mem_cons_self with h | h
      · rw [h1] at h; exact absurd h (by decide)
      · rw [h]; rfl
    · rw [cond_true]; exact hm

theorem mem_updRecs (a bb cc : Nat) (l : List Rec) (r : Rec) : r ∈ updRecs a bb cc l →
    ∃ r0 ∈ l, (par (Nat.land r0.X a) = false ∧ r = r0) ∨
      (par (Nat.land r0.X a) = true ∧
        r = ⟨r0.X, r0.P, r0.PM, Nat.land r0.lm (perp (gof r0.P cc)), Nat.land r0.rm (perp (xof r0.P bb))⟩) := by
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons r0 l ih =>
    intro h
    have e : updRecs a bb cc (r0 :: l) = cond (par (Nat.land r0.X a))
      (⟨r0.X, r0.P, r0.PM, Nat.land r0.lm (perp (gof r0.P cc)), Nat.land r0.rm (perp (xof r0.P bb))⟩ ::
        updRecs a bb cc l) (r0 :: updRecs a bb cc l) := rfl
    rw [e] at h
    cases hp : par (Nat.land r0.X a)
    · rw [hp, cond_false] at h
      rcases List.mem_cons.mp h with h1 | h1
      · exact ⟨r0, List.mem_cons_self, Or.inl ⟨hp, h1⟩⟩
      · obtain ⟨r1, hr1, h2⟩ := ih h1; exact ⟨r1, List.mem_cons_of_mem _ hr1, h2⟩
    · rw [hp, cond_true] at h
      rcases List.mem_cons.mp h with h1 | h1
      · exact ⟨r0, List.mem_cons_self, Or.inr ⟨hp, h1⟩⟩
      · obtain ⟨r1, hr1, h2⟩ := ih h1; exact ⟨r1, List.mem_cons_of_mem _ hr1, h2⟩

theorem mem_mkRecs (SS ACT : Nat) (asg : Asg) (nt : List Nat) (tail : List Rec) (hok : (mkRecs SS ACT asg nt tail).1 = true)
    (r : Rec) (hr : r ∈ (mkRecs SS ACT asg nt tail).2) :
    r ∈ tail ∨ ∃ X ∈ nt, (mkRec SS ACT asg X).1 = true ∧ r = (mkRec SS ACT asg X).2 := by
  induction nt with
  | nil => exact Or.inl hr
  | cons X nt ih =>
    have e1 : (mkRecs SS ACT asg (X :: nt) tail).1 = ((mkRec SS ACT asg X).1 && (mkRecs SS ACT asg nt tail).1) := rfl
    have e2 : (mkRecs SS ACT asg (X :: nt) tail).2 = (mkRec SS ACT asg X).2 :: (mkRecs SS ACT asg nt tail).2 := rfl
    rw [e1, Bool.and_eq_true] at hok
    rw [e2] at hr
    rcases List.mem_cons.mp hr with h | h
    · exact Or.inr ⟨X, List.mem_cons_self, hok.1, h⟩
    · rcases ih hok.2 h with h1 | ⟨X', hX', h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨X', List.mem_cons_of_mem _ hX', h2, h3⟩

theorem mem_mkSls (SS ACT : Nat) (asg : Asg) (sl : List Nat) (hok : (mkSls SS ACT asg sl).1 = true)
    (sd : Bool × Nat × Nat) (hsd : sd ∈ (mkSls SS ACT asg sl).2) :
    ∃ X ∈ sl, (mkSl SS ACT asg X).1 = true ∧ sd = mkSl SS ACT asg X := by
  induction sl with
  | nil => exact absurd hsd List.not_mem_nil
  | cons X sl ih =>
    have e1 : (mkSls SS ACT asg (X :: sl)).1 = ((mkSl SS ACT asg X).1 && (mkSls SS ACT asg sl).1) := rfl
    have e2 : (mkSls SS ACT asg (X :: sl)).2 = mkSl SS ACT asg X :: (mkSls SS ACT asg sl).2 := rfl
    rw [e1, Bool.and_eq_true] at hok
    rw [e2] at hsd
    rcases List.mem_cons.mp hsd with h | h
    · exact ⟨X, List.mem_cons_self, hok.1, h⟩
    · obtain ⟨X', hX', h2, h3⟩ := ih hok.2 h
      exact ⟨X', List.mem_cons_of_mem _ hX', h2, h3⟩

theorem allDom_spec (dom : Nat) (l : List Nat) (h : allDom dom l = true) : ∀ X ∈ l, dom.testBit X = true := by
  induction l with
  | nil => intro X hX; exact absurd hX List.not_mem_nil
  | cons X l ih =>
    have e : allDom dom (X :: l) = (bit dom X && allDom dom l) := rfl
    rw [e, Bool.and_eq_true, bit_eq] at h
    intro Y hY
    rcases List.mem_cons.mp hY with h1 | h1
    · rw [h1]; exact h.1
    · exact ih h.2 Y h1

theorem allThru_spec (a : Nat) (l : List Nat) (h : allThru a l = true) : ∀ X ∈ l, par (Nat.land a X) = true := by
  induction l with
  | nil => intro X hX; exact absurd hX List.not_mem_nil
  | cons X l ih =>
    have e : allThru a (X :: l) = (par (Nat.land a X) && allThru a l) := rfl
    rw [e, Bool.and_eq_true] at h
    intro Y hY
    rcases List.mem_cons.mp hY with h1 | h1
    · rw [h1]; exact h.1
    · exact ih h.2 Y h1

end B334.BCP
