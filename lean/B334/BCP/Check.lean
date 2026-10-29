import B334.BCP.Rec
import B334.BCP.Enum
import B334.BCP.SymBind

/-! # The induction over `checkS`

Port of `S5/Check.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to BranchCheck334. `Inv` is the semantic state at a
node for a hypothetical decomposition `(b, c)` of the leaf: the residual identity `R(X) = ∑_{active t hit by X} b_t c_tᵀ`
on the domain, valid records, and (at the root only) no records.
* `over X`: `rank R(X) ≥ rk > #hits ≥ rank R(X)` (`over_step`);
* `br t`: the true `(b_t, c_t)` (after the GL₄ pair move at a `sym` root) is among the computed candidates
  (by the candidate rules), its subtree is accepted, and the child state is again an `Inv` (`br_step`);
* `checkS_sound`: an accepted stream subtree admits no decomposition in state `Inv`. -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core Matrix

structure Inv (T n dom : Nat) (b c : Nat → Nat) (ACT : Nat) (asg : Asg) (recs : List Rec) : Prop where
  act : ∀ t, ACT.testBit t = true → t < n
  bc : BC n b c
  asg_lt : ∀ e ∈ asg, e.2.1 < 4096 ∧ e.2.2 < 4096
  hd : HD T n dom b c ACT asg
  root : asg = [] → recs = []
  recs : ∀ r ∈ recs, RecOK T n b c ACT r

theorem rd_lt (k S : Nat) : rd k S < 2 ^ k := by
  show S &&& (1 <<< k - 1) < 2 ^ k
  rw [Nat.one_shiftLeft]; exact lt_of_land_mask

theorem rdList_lt : ∀ (m S : Nat), ∀ x ∈ (rdList m S).1, x < 512 := by
  intro m
  induction m with
  | zero => intro S x hx; exact absurd hx List.not_mem_nil
  | succ m ih =>
    intro S x hx
    have e : (rdList (m + 1) S).1 = rd 9 S :: (rdList m (sk 9 S)).1 := rfl
    rw [e] at hx
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact lt_of_lt_of_eq (rd_lt 9 S) (by norm_num)
    · exact ih _ x h

theorem allnz_lt : ALLNZ < 2 ^ 4096 := by decide +kernel

theorem kidsS_ok (f : Asg → List Rec → Nat → Bool × Nat) (a : Nat) (asg : Asg) (allr : List Rec) :
    ∀ (cs : List (Nat × Nat)) (S : Nat), (kidsS f a asg allr cs S).1 = true →
      ∀ p ∈ cs, ∃ S', (f ((a, p.1, p.2) :: asg) (updRecs a p.1 p.2 allr) S').1 = true := by
  intro cs
  induction cs with
  | nil => intro S _ p hp; exact absurd hp List.not_mem_nil
  | cons q cs ih =>
    intro S h p hp
    have e : kidsS f a asg allr (q :: cs) S =
        cond (f ((a, q.1, q.2) :: asg) (updRecs a q.1 q.2 allr) S).1
          (kidsS f a asg allr cs (f ((a, q.1, q.2) :: asg) (updRecs a q.1 q.2 allr) S).2)
          (false, (f ((a, q.1, q.2) :: asg) (updRecs a q.1 q.2 allr) S).2) := rfl
    rw [e] at h
    cases hq : (f ((a, q.1, q.2) :: asg) (updRecs a q.1 q.2 allr) S).1
    · rw [hq, cond_false] at h; exact absurd h Bool.false_ne_true
    · rw [hq, cond_true] at h
      rcases List.mem_cons.mp hp with e1 | e1
      · exact ⟨S, e1 ▸ hq⟩
      · exact ih _ h p e1

theorem mat_add_self (M : Matrix (Fin 12) (Fin 12) F2) : M + M = 0 := by
  ext i j; exact f2_add_self _

theorem sum_hitS_step (T n ACT X t : Nat) (htn : t < n) (hact : ACT.testBit t = true)
    (f : Nat → Matrix (Fin 12) (Fin 12) F2) :
    (∑ s ∈ hitS T n ACT X, f s) + (if par (aT T t &&& X) = true then f t else 0) =
      ∑ s ∈ hitS T n (ACT ^^^ 1 <<< t) X, f s := by
  have hmem : ∀ u, u ∈ hitS T n (ACT ^^^ 1 <<< t) X ↔ u ∈ hitS T n ACT X ∧ u ≠ t := by
    intro u
    simp only [mem_hitS, Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases e : u = t
    · subst e; simp [hact]
    · have e' : ¬ (t = u) := fun x => e x.symm
      simp [e', e]
  cases hp : par (aT T t &&& X)
  · rw [if_neg (by decide), add_zero]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext u; rw [hmem]; constructor
    · intro hu; refine ⟨hu, fun e => ?_⟩
      rw [e, mem_hitS] at hu; rw [hu.2.2] at hp; exact absurd hp (by decide)
    · intro hu; exact hu.1
  · rw [if_pos rfl]
    have ht : t ∈ hitS T n ACT X := mem_hitS.mpr ⟨htn, hact, hp⟩
    have hset : hitS T n (ACT ^^^ 1 <<< t) X = (hitS T n ACT X).erase t := by
      ext u; rw [hmem, Finset.mem_erase]; tauto
    rw [hset, ← Finset.sum_erase_add _ _ ht, add_assoc, mat_add_self, add_zero]

/-! ## The `br` step -/

/-- **`br` step.** If the node's runtime checks pass (`brData … .1`) and every accepted child state is contradictory,
the node's state is contradictory: the true `(b_t, c_t)` (after the GL₄ pair move at a `sym` root) is a candidate. -/
theorem br_step (T n dom : Nat) (hn : n ≤ 32) (SS : Nat) (hSS : SSok T n SS) (ACT : Nat) (asg : Asg)
    (recs : List Rec) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (hnt : ∀ x ∈ nt, x < 512)
    (hsl : ∀ x ∈ sl, x < 512)
    (hd1 : (brData SS ACT asg recs dom (aT T t) nt sl sym cdir t).1 = true)
    (hkids : ∀ p ∈ (brData SS ACT asg recs dom (aT T t) nt sl sym cdir t).2.2, ∀ b c : Nat → Nat,
      Inv T n dom b c (ACT ^^^ 1 <<< t) ((aT T t, p.1, p.2) :: asg)
        (updRecs (aT T t) p.1 p.2 (brData SS ACT asg recs dom (aT T t) nt sl sym cdir t).2.1) → False)
    (b c : Nat → Nat) (hinv : Inv T n dom b c ACT asg recs) : False := by
  set nr := mkRecs SS ACT asg nt [] with hnr
  set part := thru (aT T t) recs (thru (aT T t) nr.2 []) with hpart
  set allr := app recs nr.2 with hallr
  set ss := mkSls SS ACT asg sl with hss
  set B := andLm part (Nat.land ALLNZ (cond sym ORBM M4096)) with hB
  set Cb := andRm part ALLNZ with hCb
  have hcs : (brData SS ACT asg recs dom (aT T t) nt sl sym cdir t).2.2 =
      cond cdir (cond (Nat.beq Cb 0) [] (cond (Nat.beq B 0) [] (candsC part ss.2 B (bitsOf Cb))))
        (cond (Nat.beq B 0) [] (candsB sym part ss.2 Cb (bitsOf B))) := rfl
  have hallr' : (brData SS ACT asg recs dom (aT T t) nt sl sym cdir t).2.1 = allr := rfl
  have hd1' : (bit ACT t && (!sym || (asg.isEmpty && !cdir)) && allDom dom nt && nr.1 && allDom dom sl &&
      allThru (aT T t) sl && ss.1) = true := hd1
  rw [hallr'] at hkids
  rw [hcs] at hkids
  simp only [Bool.and_eq_true] at hd1'
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hd1'
  clear_value nr part allr ss B Cb
  have hact : ACT.testBit t = true := by rw [← bit_eq]; exact h1
  have htn : t < n := hinv.act t hact
  -- the decomposition to follow (moved by GL₄ at a `sym` root)
  obtain ⟨b', c', hinv', horb⟩ : ∃ b' c' : Nat → Nat, Inv T n dom b' c' ACT asg recs ∧
      (sym = true → ORBM.testBit (b' t) = true ∧ (corbM (b' t)).testBit (c' t) = true ∧ cdir = false) := by
    cases hs : sym
    · exact ⟨b, c, hinv, fun h => absurd h Bool.false_ne_true⟩
    · rw [hs] at h2
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at h2
      obtain ⟨hasg, hcd⟩ := h2
      have hrecs := hinv.root hasg
      subst hasg; subst hrecs
      obtain ⟨b', c', hbc', hd', ho, hcorb⟩ := sym_transform_bc hinv.bc hinv.hd t htn
      exact ⟨b', c', ⟨hinv.act, hbc', hinv.asg_lt, hd', fun _ => rfl, fun r hr => absurd hr List.not_mem_nil⟩,
        fun _ => ⟨ho, hcorb, hcd⟩⟩
  clear hinv
  obtain ⟨hb0, hb1, hc0, hc1⟩ := hinv'.bc t htn
  -- records and slack data
  have hnrok : ∀ r ∈ nr.2, RecOK T n b' c' ACT r := by
    intro r hr
    rw [hnr] at hr h4
    rcases mem_mkRecs _ _ _ _ _ h4 r hr with h | ⟨X, hX, hok, rfl⟩
    · exact absurd h List.not_mem_nil
    · exact mkRec_sound hn hSS hinv'.act hinv'.bc hinv'.asg_lt hinv'.hd X (hnt X hX) (allDom_spec dom nt h3 X hX) hok
  have hallok : ∀ r ∈ allr, RecOK T n b' c' ACT r := by
    intro r hr; rw [hallr] at hr
    rcases mem_app _ _ r hr with h | h
    · exact hinv'.recs r h
    · exact hnrok r h
  have hpartok : ∀ r ∈ part, RecOK T n b' c' ACT r ∧ t ∈ hitS T n ACT r.X := by
    intro r hr; rw [hpart] at hr
    have hthru : ∀ r, r ∈ recs ∨ r ∈ nr.2 → par (Nat.land r.X (aT T t)) = true →
        RecOK T n b' c' ACT r ∧ t ∈ hitS T n ACT r.X := by
      intro r hr hp
      refine ⟨?_, mem_hitS.mpr ⟨htn, hact, ?_⟩⟩
      · rcases hr with h | h
        · exact hinv'.recs r h
        · exact hnrok r h
      · show par (aT T t &&& r.X) = true
        rw [Nat.and_comm]; exact hp
    rcases mem_thru _ recs _ r hr with ⟨h, hp⟩ | h
    · exact hthru r (Or.inl h) hp
    · rcases mem_thru _ nr.2 [] r h with ⟨h', hp⟩ | h'
      · exact hthru r (Or.inr h') hp
      · exact absurd h' List.not_mem_nil
  have hssok : ∀ sd ∈ ss.2, sd.2.1.testBit (b' t) = true ∨ sd.2.2.testBit (c' t) = true := by
    intro sd hsd
    rw [hss] at hsd h7
    obtain ⟨X, hX, hok, rfl⟩ := mem_mkSls _ _ _ _ h7 sd hsd
    exact mkSl_sound hn hSS hinv'.act hinv'.bc hinv'.asg_lt hinv'.hd X (hsl X hX) (allDom_spec dom sl h5 X hX) hok t
      (mem_hitS.mpr ⟨htn, hact, allThru_spec _ sl h6 X hX⟩)
  -- the true factors pass every mask
  have hBlt : B < 2 ^ 4096 := by
    rw [hB]; exact lt_of_le_of_lt (le_trans (andLm_le _ _) Nat.and_le_left) allnz_lt
  have hCblt : Cb < 2 ^ 4096 := by
    rw [hCb]; exact lt_of_le_of_lt (andRm_le _ _) allnz_lt
  have hBbit : B.testBit (b' t) = true := by
    rw [hB]
    refine andLm_bit part _ _ ?_ (fun r hr => ((hpartok r hr).1.2.2 t (hpartok r hr).2).1)
    show (ALLNZ &&& cond sym ORBM M4096).testBit (b' t) = true
    rw [Nat.testBit_and, allnz_bit]
    have h0 : decide (0 < b' t ∧ b' t < 4096) = true := decide_eq_true ⟨by omega, hb1⟩
    rw [h0, Bool.true_and]
    cases hs : sym
    · rw [cond_false, m4096_eq, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hb1
    · rw [cond_true]; exact (horb hs).1
  have hCbit : Cb.testBit (c' t) = true := by
    rw [hCb]
    refine andRm_bit part _ _ ?_ (fun r hr => ((hpartok r hr).1.2.2 t (hpartok r hr).2).2)
    rw [allnz_bit]; exact decide_eq_true ⟨by omega, hc1⟩
  have hcm : (cmS (b' t) ss.2 (cmT (b' t) part (cond sym (Nat.land Cb (corbM (b' t))) Cb))).testBit (c' t) = true := by
    apply cmS_bit _ _ _ _ _ hssok
    apply cmT_bit _ _ _ _ ?_
    · intro r hr
      rw [nperp_bit _ _ (xof_lt _ _) hc1, par12_comm, (hpartok r hr).1.2.1 t t (hpartok r hr).2 (hpartok r hr).2]
      simp
    · cases hs : sym
      · rw [cond_false]; exact hCbit
      · rw [cond_true, show Nat.land Cb (corbM (b' t)) = Cb &&& corbM (b' t) from rfl, Nat.testBit_and, hCbit,
          (horb hs).2.1]; rfl
  have hbm : (bmS (c' t) ss.2 (bmT (c' t) part B)).testBit (b' t) = true := by
    apply bmS_bit _ _ _ _ _ (fun sd hsd => (hssok sd hsd).symm)
    apply bmT_bit _ _ _ _ hBbit
    intro r hr
    rw [nperp_bit _ _ (gof_lt _ _) hb1, par12_comm, par_gof_xof _ _ _ hb1 hc1,
      (hpartok r hr).1.2.1 t t (hpartok r hr).2 (hpartok r hr).2]
    simp
  have hB0 : Nat.beq B 0 = false := by
    cases e : Nat.beq B 0
    · rfl
    · rw [Nat.eq_of_beq_eq_true e, Nat.zero_testBit] at hBbit; exact absurd hBbit Bool.false_ne_true
  have hC0 : Nat.beq Cb 0 = false := by
    cases e : Nat.beq Cb 0
    · rfl
    · rw [Nat.eq_of_beq_eq_true e, Nat.zero_testBit] at hCbit; exact absurd hCbit Bool.false_ne_true
  have hmem : (b' t, c' t) ∈ cond cdir (cond (Nat.beq Cb 0) [] (cond (Nat.beq B 0) [] (candsC part ss.2 B (bitsOf Cb))))
      (cond (Nat.beq B 0) [] (candsB sym part ss.2 Cb (bitsOf B))) := by
    cases hcd : cdir
    · rw [cond_false, hB0, cond_false]
      exact candsB_mem sym part ss.2 Cb hCblt (b' t) (c' t) (bitsOf B) (bitsOf_mem B hBlt _ hBbit) hcm
    · rw [cond_true, hC0, cond_false, hB0, cond_false]
      exact candsC_mem part ss.2 B hBlt (c' t) (b' t) (bitsOf Cb) (bitsOf_mem Cb hCblt _ hCbit) hbm
  refine hkids _ hmem b' c' ⟨?_, hinv'.bc, ?_, ?_, fun h => absurd h (List.cons_ne_nil _ _), ?_⟩
  · intro u hu
    rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow] at hu
    by_cases e : u = t
    · rw [e]; exact htn
    · have e' : ¬ (t = u) := fun x => e x.symm
      simp only [e', decide_false, Bool.xor_false] at hu
      exact hinv'.act u hu
  · intro e he
    rcases List.mem_cons.mp he with h | h
    · rw [h]; exact ⟨hb1, hc1⟩
    · exact hinv'.asg_lt e h
  · intro X hX hdom
    rw [resM_cons, hinv'.hd X hX hdom]
    exact sum_hitS_step T n ACT X t htn hact (fun s => vecMulVec (nv (b' s)) (nv (c' s)))
  · intro r hr
    obtain ⟨r0, hr0, h⟩ := mem_updRecs (aT T t) (b' t) (c' t) allr r hr
    obtain ⟨u1, u2⟩ := updRec_ok hinv'.bc t htn hact r0 (hallok r0 hr0)
    rcases h with ⟨hp, rfl⟩ | ⟨hp, rfl⟩
    · exact u1 hp
    · exact u2 hp

/-- **`over` step.** -/
theorem over_step (T n dom : Nat) (hn : n ≤ 32) (SS : Nat) (hSS : SSok T n SS) (ACT : Nat) (asg : Asg)
    (recs : List Rec) (X : Nat) (hX : X < 512)
    (h : (bit dom X && elimOk (elim (resC X asg)) && Nat.blt (ucnt SS ACT X) (elim (resC X asg)).rk) = true)
    (b c : Nat → Nat) (hinv : Inv T n dom b c ACT asg recs) : False := by
  simp only [Bool.and_eq_true, Nat.blt_eq, bit_eq] at h
  obtain ⟨⟨hdom, hok⟩, hlt⟩ := h
  obtain ⟨hA, hRI⟩ := resC_sem _ hX asg hinv.asg_lt
  have hf := elim_facts _ hRI hok
  rw [hA] at hf
  have hrk := rank_ge_elim hf
  rw [hinv.hd _ hX hdom] at hrk
  have hle := rank_sum_le (hitS T n ACT X) (fun t => nv (b t)) (fun t => nv (c t))
  rw [ucnt_eq' T n ACT _ SS hSS hn hX hinv.act] at hlt
  omega

/-- **Soundness of the node induction** (stream certificates). An accepted subtree admits no decomposition in state
`Inv`. -/
theorem checkS_sound (T n dom : Nat) (hn : n ≤ 31) : ∀ fuel ACT asg recs S,
    (checkS fuel T (mkSSP T n) ACT asg recs dom S).1 = true → ∀ b c, Inv T n dom b c ACT asg recs → False := by
  intro fuel
  induction fuel with
  | zero => intro ACT asg recs S h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro ACT asg recs S hchk b c hinv
    have hs : checkS (fuel + 1) T (mkSSP T n) ACT asg recs dom S =
      cond (Nat.beq (rd 1 S) 0)
        ((bit dom (rd 9 (sk 1 S)) && elimOk (elim (resC (rd 9 (sk 1 S)) asg)) &&
            Nat.blt (ucnt (mkSSP T n) ACT (rd 9 (sk 1 S))) (elim (resC (rd 9 (sk 1 S)) asg)).rk, sk 10 S))
        (((brData (mkSSP T n) ACT asg recs dom (aT T (rd 5 (sk 1 S)))
              (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).1
              (rdList (rd 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)
                (sk 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)).1
              (Nat.beq (rd 1 (sk 5 (sk 1 S))) 1) (Nat.beq (rd 1 (sk 6 (sk 1 S))) 1) (rd 5 (sk 1 S))).1 &&
          (kidsS (fun asg' recs' S' => checkS fuel T (mkSSP T n) (Nat.xor ACT (Nat.shiftLeft 1 (rd 5 (sk 1 S))))
              asg' recs' dom S') (aT T (rd 5 (sk 1 S))) asg
            (brData (mkSSP T n) ACT asg recs dom (aT T (rd 5 (sk 1 S)))
              (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).1
              (rdList (rd 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)
                (sk 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)).1
              (Nat.beq (rd 1 (sk 5 (sk 1 S))) 1) (Nat.beq (rd 1 (sk 6 (sk 1 S))) 1) (rd 5 (sk 1 S))).2.1
            (brData (mkSSP T n) ACT asg recs dom (aT T (rd 5 (sk 1 S)))
              (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).1
              (rdList (rd 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)
                (sk 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)).1
              (Nat.beq (rd 1 (sk 5 (sk 1 S))) 1) (Nat.beq (rd 1 (sk 6 (sk 1 S))) 1) (rd 5 (sk 1 S))).2.2
            (rdList (rd 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)
              (sk 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)).2).1),
          (kidsS (fun asg' recs' S' => checkS fuel T (mkSSP T n) (Nat.xor ACT (Nat.shiftLeft 1 (rd 5 (sk 1 S))))
              asg' recs' dom S') (aT T (rd 5 (sk 1 S))) asg
            (brData (mkSSP T n) ACT asg recs dom (aT T (rd 5 (sk 1 S)))
              (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).1
              (rdList (rd 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)
                (sk 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)).1
              (Nat.beq (rd 1 (sk 5 (sk 1 S))) 1) (Nat.beq (rd 1 (sk 6 (sk 1 S))) 1) (rd 5 (sk 1 S))).2.1
            (brData (mkSSP T n) ACT asg recs dom (aT T (rd 5 (sk 1 S)))
              (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).1
              (rdList (rd 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)
                (sk 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)).1
              (Nat.beq (rd 1 (sk 5 (sk 1 S))) 1) (Nat.beq (rd 1 (sk 6 (sk 1 S))) 1) (rd 5 (sk 1 S))).2.2
            (rdList (rd 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)
              (sk 3 (rdList (rd 4 (sk 7 (sk 1 S))) (sk 11 (sk 1 S))).2)).2).2) := rfl
    rw [hs] at hchk
    revert hchk
    cases hb : Nat.beq (rd 1 S) 0
    · rw [cond_false]
      intro hchk
      rw [Bool.and_eq_true] at hchk
      obtain ⟨hd1, hkr⟩ := hchk
      refine br_step T n dom (by omega) (mkSSP T n) (mkSSP_ok T n (by omega)) ACT asg recs _ _ _ _ _
        (rdList_lt _ _) (rdList_lt _ _) hd1 ?_ b c hinv
      intro p hp b' c' hinv'
      obtain ⟨S', hS'⟩ := kidsS_ok _ _ _ _ _ _ hkr p hp
      exact ih _ _ _ S' hS' b' c' hinv'
    · rw [cond_true]
      intro hchk
      exact over_step T n dom (by omega) (mkSSP T n) (mkSSP_ok T n (by omega)) ACT asg recs _
        (lt_of_lt_of_eq (rd_lt 9 _) (by norm_num)) hchk b c hinv

end B334.BCP
