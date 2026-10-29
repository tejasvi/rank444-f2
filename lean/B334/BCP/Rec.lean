import B334.BCP.Root
import B334.BCP.Rec0

/-! # Records and slack data: what the checker's lists certify (second part of the port of `S5/Rec.lean`)

⟨3,3,3⟩ release `rank333-f2`, Apache-2.0. `mkRec_sound`, `mkSl_sound`: an accepted NT claim gives a valid tight record
(masks containing the factors of the hit terms, and `⟨c_s, x(b_t)⟩ = δ_st` by `delta_of_tight`), an
accepted SL claim gives `b_t ∈ col R(X)` or `c_t ∈ row R(X)`; `updRec_ok`: the update after an assignment keeps
every record valid. -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core Matrix

/-- `F2^12` vector → 12-bit number -/
def natOf (v : Fin 12 → F2) : Nat := mkB (fun i => if h : i < 12 then decide (v ⟨i, h⟩ = 1) else false) 12

theorem natOf_lt (v : Fin 12 → F2) : natOf v < 4096 := lt_of_lt_of_eq (mkB_lt _ 12) (by norm_num)

theorem nv_natOf (v : Fin 12 → F2) : nv (natOf v) = v := by
  funext i
  show bf ((natOf v).testBit i.val) = v i
  rw [natOf, mkB_bit]
  simp only [i.isLt, decide_true, Bool.true_and, dif_pos]
  rcases zmod2_cases (v i) with h | h <;> rw [h] <;> decide

theorem bf_eq_one (x : Bool) : decide (bf x = 1) = x := by cases x <;> decide

theorem natOf_nv (w : Nat) (hw : w < 4096) : natOf (nv w) = w := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [natOf, mkB_bit]
  by_cases hj : j < 12
  · simp only [hj, decide_true, Bool.true_and, dif_pos, nv, bitF_bf]
    exact bf_eq_one (w.testBit j)
  · rw [lt4096_bit w j hw (by omega)]; simp [hj]

/-- data of an accepted computed record -/
theorem mkRec_cases (SS ACT : Nat) (asg : Asg) (X : Nat) (hX : X < 512) (hok : (mkRec SS ACT asg X).1 = true) :
    ∃ s : ES, s = elim (resC X asg) ∧ elimOk s = true ∧ ucnt SS ACT X ≤ s.rk ∧
      (mkRec SS ACT asg X).2 = ⟨X, s.P, s.PM, lmC s.P s.PM, kerM s.M⟩ := by
  unfold mkRec at hok ⊢
  revert hok
  cases hna : noasg X asg
  · rw [cond_false]
    intro hok
    simp only [Bool.and_eq_true, Nat.ble_eq] at hok
    exact ⟨_, rfl, hok.1, hok.2, rfl⟩
  · rw [cond_true]
    intro hok
    have hroot := root_fact X hX
    simp only [rootOK, Bool.and_eq_true, Nat.beq_eq] at hroot
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hroot
    have hc : resC X asg = Nat.xor (txc24 X) ID24 := (noasg_spec X asg hna).1
    simp only [Nat.ble_eq] at hok
    refine ⟨elim (Nat.xor (txc24 X) ID24), by rw [hc], h6, ?_, ?_⟩
    · rw [← h5]; exact hok
    · rw [h1, h2, h3, h4]

theorem tight_or_slack {ι : Type*} [DecidableEq ι] (S : Finset ι) (β γ : ι → Fin 12 → F2)
    (h : S.card ≤ (∑ s ∈ S, vecMulVec (β s) (γ s)).rank + 1) (t : ι) (ht : t ∈ S) :
    β t ∈ LinearMap.range (∑ s ∈ S, vecMulVec (β s) (γ s)).mulVecLin ∨
      γ t ∈ LinearMap.range (∑ s ∈ S, vecMulVec (β s) (γ s))ᵀ.mulVecLin := by
  have hle := rank_sum_le S β γ
  rcases (by omega : (∑ s ∈ S, vecMulVec (β s) (γ s)).rank = S.card ∨
      (∑ s ∈ S, vecMulVec (β s) (γ s)).rank + 1 = S.card) with e | e
  · exact Or.inl (tight_fs S β γ e t ht).1
  · exact slack_fs S β γ e t ht

section
variable {T n dom ACT : Nat} {asg : Asg} {b c : Nat → Nat}

theorem mkRec_sound (hn : n ≤ 32) {SS : Nat} (hSS : SSok T n SS) (hact : ∀ t, ACT.testBit t = true → t < n) (hbc : BC n b c)
    (hasg : ∀ e ∈ asg, e.2.1 < 4096 ∧ e.2.2 < 4096) (hd : HD T n dom b c ACT asg) (X : Nat) (hX : X < 512)
    (hdom : dom.testBit X = true) (hok : (mkRec SS ACT asg X).1 = true) :
    RecOK T n b c ACT (mkRec SS ACT asg X).2 := by
  obtain ⟨s, hs, hok', hle, hrec⟩ := mkRec_cases _ ACT asg X hX hok
  rw [hrec]
  obtain ⟨hA, hRI⟩ := resC_sem X hX asg hasg
  have hf : ElimFacts (resM X asg) s := by
    have := elim_facts (resC X asg) hRI (hs ▸ hok'); rw [hA] at this; rw [hs]; exact this
  have hR := hd X hX hdom
  have hcard : (hitS T n ACT X).card ≤ s.rk := by rw [← ucnt_eq' T n ACT X SS hSS hn hX hact]; exact hle
  have hrk := rank_ge_elim hf
  rw [hR] at hrk
  have htight : (∑ t ∈ hitS T n ACT X, vecMulVec (nv (b t)) (nv (c t))).rank = (hitS T n ACT X).card :=
    le_antisymm (rank_sum_le _ _ _) (by omega)
  have hbt : ∀ t ∈ hitS T n ACT X, t < n := fun t ht => (mem_hitS.mp ht).1
  refine ⟨hX, ?_, ?_⟩
  · intro s' t hs' ht
    have hδ := delta_of_tight (hitS T n ACT X) (fun t => nv (b t)) (fun t => nv (c t)) htight
      (fun v => nv (xof s.P (natOf v))) (by
        intro v hv
        rw [← hR] at hv ⊢
        have := xof_inv hf (natOf v) (natOf_lt v) (by rw [nv_natOf]; exact hv)
        rw [nv_natOf] at this; exact this) s' t hs' ht
    simp only [natOf_nv _ (hbc t (hbt t ht)).2.1] at hδ
    rw [dot_nv12] at hδ
    apply bf_inj
    show bf (par12 (c s' &&& xof s.P (b t))) = bf (decide (s' = t))
    rw [hδ]
    by_cases e : s' = t <;> simp [e, bf]
  · intro t ht
    have h3 := tight_fs (hitS T n ACT X) (fun t => nv (b t)) (fun t => nv (c t)) htight t ht
    rw [← hR] at h3
    exact ⟨lmC_of_range hf _ (hbc t (hbt t ht)).2.1 h3.1, kerM_of_range hf _ (hbc t (hbt t ht)).2.2.2 h3.2.1⟩

/-- an accepted slack datum: `b_t` in the column-space mask or `c_t` in the row-space mask -/
theorem mkSl_sound (hn : n ≤ 32) {SS : Nat} (hSS : SSok T n SS) (hact : ∀ t, ACT.testBit t = true → t < n) (hbc : BC n b c)
    (hasg : ∀ e ∈ asg, e.2.1 < 4096 ∧ e.2.2 < 4096) (hd : HD T n dom b c ACT asg) (X : Nat) (hX : X < 512)
    (hdom : dom.testBit X = true) (hok : (mkSl SS ACT asg X).1 = true) (t : Nat)
    (ht : t ∈ hitS T n ACT X) :
    (mkSl SS ACT asg X).2.1.testBit (b t) = true ∨ (mkSl SS ACT asg X).2.2.testBit (c t) = true := by
  have htn := (mem_hitS.mp ht).1
  obtain ⟨_, hb, _, hc⟩ := hbc t htn
  have hR := hd X hX hdom
  obtain ⟨hA, hRI⟩ := resC_sem X hX asg hasg
  obtain ⟨hA2, hRI2⟩ := resR_sem X hX asg hasg
  -- masks containing col R and row R, and the count bound
  have key : ∀ (bm cm rk : Nat), (∀ w, w < 4096 → nv w ∈ LinearMap.range (resM X asg).mulVecLin → bm.testBit w = true) →
      (∀ w, w < 4096 → nv w ∈ LinearMap.range (resM X asg)ᵀ.mulVecLin → cm.testBit w = true) →
      rk ≤ (resM X asg).rank → ucnt SS ACT X ≤ rk + 1 → bm.testBit (b t) = true ∨ cm.testBit (c t) = true := by
    intro bm cm rk hbm hcm hrk hu
    rw [ucnt_eq' T n ACT X SS hSS hn hX hact] at hu
    rw [hR] at hrk hbm hcm
    have hc' : (hitS T n ACT X).card ≤ (∑ t ∈ hitS T n ACT X, vecMulVec (nv (b t)) (nv (c t))).rank + 1 := by
      omega
    rcases tight_or_slack (hitS T n ACT X) (fun t => nv (b t)) (fun t => nv (c t)) hc' t ht with h | h
    · exact Or.inl (hbm _ hb h)
    · exact Or.inr (hcm _ hc h)
  unfold mkSl at hok ⊢
  revert hok
  cases hna : noasg X asg
  · rw [cond_false]
    intro hok
    simp only [Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨⟨h1, h2⟩, h3⟩ := hok
    have hf : ElimFacts (resM X asg) (elim (resC X asg)) := by
      have := elim_facts (resC X asg) hRI h1; rwa [hA] at this
    have hf2 : ElimFacts (resM X asg)ᵀ (elim (resR X asg)) := by
      have := elim_facts (resR X asg) hRI2 h2; rwa [hA2] at this
    exact key _ _ _ (fun w hw hv => kerM_of_range hf2 w hw (by rw [Matrix.transpose_transpose]; exact hv))
      (fun w hw hv => kerM_of_range hf w hw hv) (rank_ge_elim hf) h3
  · rw [cond_true]
    intro hok
    have hroot := root_fact X hX
    simp only [rootOK, Bool.and_eq_true, Nat.beq_eq] at hroot
    obtain ⟨⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hroot
    have hc' : resC X asg = Nat.xor (txc24 X) ID24 := (noasg_spec X asg hna).1
    have hf : ElimFacts (resM X asg) (elim (Nat.xor (txc24 X) ID24)) := by
      have := elim_facts (resC X asg) hRI (by rw [hc']; exact h6); rw [hA, hc'] at this; exact this
    simp only [Nat.ble_eq] at hok
    refine key _ _ _ (fun w hw hv => ?_) (fun w hw hv => ?_) (rank_ge_elim hf) (by rw [← h5]; exact hok)
    · show (rlm X).testBit w = true
      rw [h3]; exact lmC_of_range hf w hw hv
    · show (rrm X).testBit w = true
      rw [h4]; exact kerM_of_range hf w hw hv

end

/-- **(I).** The update after `t ↦ (b_t, c_t)` keeps a valid record valid: unchanged if its `X` misses `a_t`, with the
masks `lm ∧ perp(g(c_t))` and `rm ∧ perp(x(b_t))` if it hits `a_t`. -/
theorem updRec_ok {T n : Nat} {b c : Nat → Nat} {ACT : Nat} (hbc : BC n b c) (t : Nat) (htn : t < n)
    (htact : ACT.testBit t = true) (r0 : Rec) (hr0 : RecOK T n b c ACT r0) :
    (par (Nat.land r0.X (aT T t)) = false → RecOK T n b c (ACT ^^^ 1 <<< t) r0) ∧
    (par (Nat.land r0.X (aT T t)) = true → RecOK T n b c (ACT ^^^ 1 <<< t) ⟨r0.X, r0.P, r0.PM,
      Nat.land r0.lm (perp (gof r0.P (c t))), Nat.land r0.rm (perp (xof r0.P (b t)))⟩) := by
  obtain ⟨hX, hδ, hm⟩ := hr0
  have hsub : ∀ u, u ∈ hitS T n (ACT ^^^ 1 <<< t) r0.X → u ∈ hitS T n ACT r0.X ∧ u ≠ t := by
    intro u hu
    rw [mem_hitS] at hu ⊢
    rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow] at hu
    by_cases e : u = t
    · subst e; simp [htact] at hu
    · have e' : ¬ (t = u) := fun x => e x.symm
      simp only [e', decide_false, Bool.xor_false] at hu
      exact ⟨hu, e⟩
  constructor
  · intro _
    exact ⟨hX, fun s u hs hu => hδ s u (hsub s hs).1 (hsub u hu).1, fun u hu => hm u (hsub u hu).1⟩
  · intro hp
    have ht : t ∈ hitS T n ACT r0.X := by
      rw [mem_hitS]; refine ⟨htn, htact, ?_⟩
      show par (aT T t &&& r0.X) = true
      rw [Nat.and_comm]; exact hp
    have hbt := hbc t htn
    refine ⟨hX, fun s u hs hu => hδ s u (hsub s hs).1 (hsub u hu).1, fun u hu => ?_⟩
    obtain ⟨hu', hne⟩ := hsub u hu
    have hbu := hbc u (mem_hitS.mp hu').1
    obtain ⟨hlm, hrm⟩ := hm u hu'
    constructor
    · show (r0.lm &&& perp (gof r0.P (c t))).testBit (b u) = true
      rw [Nat.testBit_and, hlm, perp_bit _ _ (gof_lt _ _) hbu.2.1, par12_comm, par_gof_xof _ _ _ hbu.2.1 hbt.2.2.2,
        hδ t u ht hu']
      have : ¬ (t = u) := fun x => hne x.symm
      simp [this]
    · show (r0.rm &&& perp (xof r0.P (b t))).testBit (c u) = true
      rw [Nat.testBit_and, hrm, perp_bit _ _ (xof_lt _ _) hbu.2.2.2, par12_comm, hδ u t hu' ht]
      simp [hne]

end B334.BCP
