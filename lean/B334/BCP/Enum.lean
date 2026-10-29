import B334.BCP.Rec0
import B334.BCP.Bit

/-! # Candidate enumeration: `bitsOf`, `pairs`, `candsB`, `candsC` list every set bit

Port of `S5/Enum.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to 4096-bit masks: `lowIdx m` (the checker's
lowest-set-bit index, `Nat.log2` of the isolated lowest bit) replaces the table `lg2`, and the loops run on fuel
4096. `candsB` carries the `sym` filter `cb ∧ CORB[b]`. -/

namespace B334.BCP

open B334.BC B334.BCT

theorem lowIdx_eq {m k : Nat} (hk : m.testBit k = true) (hlow : ∀ i < k, m.testBit i = false) : lowIdx m = k := by
  show Nat.log2 (Nat.xor m (Nat.land m (Nat.pred m))) = k
  have e : Nat.xor m (Nat.land m (Nat.pred m)) = m ^^^ (m &&& (m - 1)) := rfl
  rw [e, (low_bit_spec hk hlow).2, Nat.log2_two_pow]

/-- one step of the enumeration: the lowest bit `k` comes out, `m &&& (m - 1)` keeps the others -/
theorem enum_step (f m : Nat) (hm : m < 2 ^ 4096) (hlow : ∀ i, i < 4096 - (f + 1) → m.testBit i = false)
    (hm0 : m ≠ 0) : ∃ k, lowIdx m = k ∧ m.testBit k = true ∧
      (∀ w, m.testBit w = true → w = k ∨ (Nat.land m (Nat.pred m)).testBit w = true) ∧
      Nat.land m (Nat.pred m) < 2 ^ 4096 ∧ (∀ i, i < 4096 - f → (Nat.land m (Nat.pred m)).testBit i = false) := by
  obtain ⟨k, hk, hkl⟩ := low_bit_exists hm0
  obtain ⟨hand, _⟩ := low_bit_spec hk hkl
  have e : Nat.land m (Nat.pred m) = m &&& (m - 1) := rfl
  rw [e]
  have hk4 : k < 4096 := by
    by_contra h
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega : 4096 ≤ k)))
    rw [hk] at this; exact absurd this (by decide)
  have hkf : 4096 - (f + 1) ≤ k := by
    by_contra h
    have := hlow k (by omega); rw [hk] at this; exact absurd this (by decide)
  refine ⟨k, lowIdx_eq hk hkl, hk, ?_, lt_of_le_of_lt Nat.and_le_left hm, ?_⟩
  · intro w hw
    by_cases e : w = k
    · exact Or.inl e
    · right; rw [hand, hw]; simp [e]
  · intro i hi
    rw [hand]
    by_cases e : i = k
    · simp [e]
    · have : i < k := by omega
      rw [hkl i this]; rfl

theorem bitsOfAux_mem : ∀ (f m : Nat), m < 2 ^ 4096 → (∀ i, i < 4096 - f → m.testBit i = false) →
    ∀ w, m.testBit w = true → w ∈ bitsOfAux f m := by
  intro f
  induction f with
  | zero =>
    intro m hm hlow w hw
    exfalso
    by_cases hw5 : w < 4096
    · rw [hlow w (by omega)] at hw; exact absurd hw (by decide)
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hw
      exact absurd hw (by decide)
  | succ f ih =>
    intro m hm hlow w hw
    have hs : bitsOfAux (f + 1) m = cond (Nat.beq m 0) [] (lowIdx m :: bitsOfAux f (Nat.land m (Nat.pred m))) := rfl
    rw [hs]
    have hm0 : m ≠ 0 := by intro e; rw [e, Nat.zero_testBit] at hw; exact absurd hw (by decide)
    have hb : Nat.beq m 0 = false := by
      cases h : Nat.beq m 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hm0
    rw [hb, cond_false]
    obtain ⟨k, hlg, _, hsplit, hlt, hlow'⟩ := enum_step f m hm hlow hm0
    rw [hlg]
    rcases hsplit w hw with e | h
    · rw [e]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ hlt hlow' w h)

theorem bitsOf_mem (m : Nat) (hm : m < 2 ^ 4096) (w : Nat) (hw : m.testBit w = true) : w ∈ bitsOf m :=
  bitsOfAux_mem 4096 m hm (fun i hi => by omega) w hw

theorem pairs_mem_aux (bfirst : Bool) (c : Nat) (tail : List (Nat × Nat)) : ∀ (f m : Nat), m < 2 ^ 4096 →
    (∀ i, i < 4096 - f → m.testBit i = false) →
    (∀ p ∈ tail, p ∈ pairs bfirst c f m tail) ∧
    (∀ w, m.testBit w = true → cond bfirst (c, w) (w, c) ∈ pairs bfirst c f m tail) := by
  intro f
  induction f with
  | zero =>
    intro m hm hlow
    refine ⟨fun p hp => hp, fun w hw => ?_⟩
    exfalso
    by_cases hw5 : w < 4096
    · rw [hlow w (by omega)] at hw; exact absurd hw (by decide)
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hw
      exact absurd hw (by decide)
  | succ f ih =>
    intro m hm hlow
    have hs : pairs bfirst c (f + 1) m tail = cond (Nat.beq m 0) tail
        (cond bfirst (c, lowIdx m) (lowIdx m, c) :: pairs bfirst c f (Nat.land m (Nat.pred m)) tail) := rfl
    rw [hs]
    by_cases hm0 : m = 0
    · have hb : Nat.beq m 0 = true := by rw [hm0]; rfl
      rw [hb, cond_true]
      refine ⟨fun p hp => hp, fun w hw => ?_⟩
      rw [hm0, Nat.zero_testBit] at hw; exact absurd hw (by decide)
    · have hb : Nat.beq m 0 = false := by
        cases h : Nat.beq m 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hm0
      rw [hb, cond_false]
      obtain ⟨k, hlg, _, hsplit, hlt, hlow'⟩ := enum_step f m hm hlow hm0
      rw [hlg]
      obtain ⟨ih1, ih2⟩ := ih _ hlt hlow'
      refine ⟨fun p hp => List.mem_cons_of_mem _ (ih1 p hp), fun w hw => ?_⟩
      rcases hsplit w hw with e | h
      · rw [e]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih2 w h)

theorem pairs_mem (bfirst : Bool) (c m : Nat) (tail : List (Nat × Nat)) (hm : m < 2 ^ 4096) :
    (∀ p ∈ tail, p ∈ pairs bfirst c 4096 m tail) ∧
    (∀ w, m.testBit w = true → cond bfirst (c, w) (w, c) ∈ pairs bfirst c 4096 m tail) :=
  pairs_mem_aux bfirst c tail 4096 m hm (fun i hi => by omega)

theorem cmS_le (bb : Nat) (l : List (Bool × Nat × Nat)) : ∀ m, cmS bb l m ≤ m := by
  induction l with
  | nil => intro m; exact le_rfl
  | cons sd l ih =>
    intro m
    have e : cmS bb (sd :: l) m = cmS bb l (cond (bit sd.2.1 bb) m (Nat.land m sd.2.2)) := rfl
    rw [e]
    refine le_trans (ih _) ?_
    cases bit sd.2.1 bb
    · rw [cond_false]; exact Nat.and_le_left
    · rw [cond_true]

theorem bmS_le (cc : Nat) (l : List (Bool × Nat × Nat)) : ∀ m, bmS cc l m ≤ m := by
  induction l with
  | nil => intro m; exact le_rfl
  | cons sd l ih =>
    intro m
    have e : bmS cc (sd :: l) m = bmS cc l (cond (bit sd.2.2 cc) m (Nat.land m sd.2.1)) := rfl
    rw [e]
    refine le_trans (ih _) ?_
    cases bit sd.2.2 cc
    · rw [cond_false]; exact Nat.and_le_left
    · rw [cond_true]

theorem cmT_le (bb : Nat) (l : List Rec) : ∀ m, cmT bb l m ≤ m := by
  induction l with
  | nil => intro m; exact le_rfl
  | cons r l ih => intro m; exact le_trans (ih _) Nat.and_le_left

theorem bmT_le (cc : Nat) (l : List Rec) : ∀ m, bmT cc l m ≤ m := by
  induction l with
  | nil => intro m; exact le_rfl
  | cons r l ih => intro m; exact le_trans (ih _) Nat.and_le_left

/-- the `cdir = false` list contains `(b, w)` for every listed `b` and every `w` of `b`'s filtered c-mask -/
theorem candsB_mem (sym : Bool) (part : List Rec) (ss : List (Bool × Nat × Nat)) (cb : Nat) (hcb : cb < 2 ^ 4096)
    (bb w : Nat) : ∀ bs : List Nat, bb ∈ bs →
      (cmS bb ss (cmT bb part (cond sym (Nat.land cb (corbM bb)) cb))).testBit w = true →
      (bb, w) ∈ candsB sym part ss cb bs := by
  intro bs
  induction bs with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons b' bs ih =>
    intro hb hw
    have e : candsB sym part ss cb (b' :: bs) =
        pairs true b' 4096 (cmS b' ss (cmT b' part (cond sym (Nat.land cb (corbM b')) cb))) (candsB sym part ss cb bs) :=
      rfl
    rw [e]
    have hlt : ∀ b'', cmS b'' ss (cmT b'' part (cond sym (Nat.land cb (corbM b'')) cb)) < 2 ^ 4096 := by
      intro b''
      refine lt_of_le_of_lt (le_trans (cmS_le _ _ _) (cmT_le _ _ _)) ?_
      cases sym
      · exact hcb
      · exact lt_of_le_of_lt Nat.and_le_left hcb
    rcases List.mem_cons.mp hb with h | h
    · subst h; exact (pairs_mem true bb _ _ (hlt bb)).2 w hw
    · exact (pairs_mem true b' _ _ (hlt b')).1 _ (ih h hw)

/-- the `cdir = true` list contains `(w, c)` for every listed `c` and every `w` of `c`'s filtered b-mask -/
theorem candsC_mem (part : List Rec) (ss : List (Bool × Nat × Nat)) (bm : Nat) (hbm : bm < 2 ^ 4096) (cc w : Nat) :
    ∀ cs : List Nat, cc ∈ cs → (bmS cc ss (bmT cc part bm)).testBit w = true → (w, cc) ∈ candsC part ss bm cs := by
  intro cs
  induction cs with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons c' cs ih =>
    intro hc hw
    have e : candsC part ss bm (c' :: cs) = pairs false c' 4096 (bmS c' ss (bmT c' part bm)) (candsC part ss bm cs) := rfl
    rw [e]
    have hlt : ∀ c'', bmS c'' ss (bmT c'' part bm) < 2 ^ 4096 :=
      fun c'' => lt_of_le_of_lt (le_trans (bmS_le _ _ _) (bmT_le _ _ _)) hbm
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact (pairs_mem false cc _ _ (hlt cc)).2 w hw
    · exact (pairs_mem false c' _ _ (hlt c')).1 _ (ih h hw)

end B334.BCP
