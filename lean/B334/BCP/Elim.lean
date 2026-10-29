import B334.BCP.Count
import B334.Core.Branch334

/-! # The bit-sliced elimination `elim`: one step on slots, the structural invariant, and the span invariant

Port of `S5/Elim.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to BranchCheck334. A packed
matrix holds twelve 24-bit slots (`slot z` = bits `24z … 24z+23`: 12 data bits, then the identity half). `stepE h`
takes the first slot of `M` with data bit `h` set as pivot row `p`, moves it to slot `h` of `P`, and adds `p` to every
other slot of `M` and `P` with bit `h` set. So the F₂-span of all twenty-four slots never changes (`span_step`), and
the structural data `PM`, `rk`, `DG`, `D24` stay what `elimOk` expects (`Pre`). -/

namespace B334.BCP

open B334.BC B334.BCT B334.Core Matrix

/-! ## One step -/

/-- the pivot branch of `stepE` -/
def pstep (h : Nat) (s : ES) : ES :=
  let cand := Nat.land (Nat.shiftRight s.M h) REP24
  let p := Nat.land (Nat.div s.M (Nat.xor cand (Nat.land cand (Nat.pred cand)))) M24
  { P := Nat.lor (Nat.xor s.P (Nat.mul (Nat.land (Nat.shiftRight s.P h) REP24) p)) (Nat.shiftLeft p (Nat.mul 24 h)),
    PM := Nat.lor s.PM (Nat.shiftLeft 1 h), rk := Nat.succ s.rk,
    DG := Nat.lor s.DG (Nat.shiftLeft 1 (Nat.mul 25 h)), D24 := Nat.lor s.D24 (Nat.shiftLeft 1 (Nat.mul 24 h)),
    M := Nat.xor s.M (Nat.mul cand p) }

theorem stepE_eq (h : Nat) (s : ES) :
    stepE h s = cond (Nat.beq (Nat.land (Nat.shiftRight s.M h) REP24) 0) s (pstep h s) := rfl

theorem cand_bit (M h i : Nat) :
    ((M >>> h) &&& REP24).testBit i = (M.testBit (h + i) && decide (i % 24 = 0 ∧ i < 288)) := by
  rw [Nat.testBit_and, Nat.testBit_shiftRight, rep24_bit]

theorem cand_sparse (M h : Nat) : ∀ i, ((M >>> h) &&& REP24).testBit i = true → i % 24 = 0 := by
  intro i hi; rw [cand_bit] at hi; simp at hi; omega

theorem sparse24_slot {m v : Nat} (hm : ∀ j, m.testBit j = true → j % 24 = 0) (hv : v < 2 ^ 24) (z i : Nat)
    (hi : i < 24) : (m * v).testBit (24 * z + i) = (m.testBit (24 * z) && v.testBit i) := by
  rw [testBit_sparse_mul (by norm_num) m v hv hm]
  have e1 : (24 * z + i) / 24 = z := by omega
  have e2 : (24 * z + i) % 24 = i := by omega
  rw [e1, e2]

theorem shl_slot {p : Nat} (hp : p < 2 ^ 24) (h z i : Nat) (hi : i < 24) :
    (p <<< (24 * h)).testBit (24 * z + i) = (decide (z = h) && p.testBit i) := by
  rw [Nat.testBit_shiftLeft]
  rcases lt_trichotomy z h with hz | hz | hz
  · have : ¬ (24 * z + i ≥ 24 * h) := by omega
    have hz' : z ≠ h := by omega
    simp [this, hz']
  · subst hz; simp [show 24 * z + i - 24 * z = i by omega]
  · have hz' : z ≠ h := by omega
    have : p.testBit (24 * z + i - 24 * h) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this, hz']

theorem land_m24_lt (x : Nat) : x &&& M24 < 2 ^ 24 := by rw [m24_eq]; exact lt_of_land_mask

/-- **Pivot step on slots.** -/
theorem pstep_bits (h : Nat) (hh : h < 12) (s : ES) (hc : (s.M >>> h) &&& REP24 ≠ 0) :
    ∃ z0, z0 < 12 ∧ s.M.testBit (24 * z0 + h) = true ∧
      (∀ z i, z < 12 → i < 24 → (pstep h s).M.testBit (24 * z + i) =
        xor (s.M.testBit (24 * z + i)) (s.M.testBit (24 * z + h) && s.M.testBit (24 * z0 + i))) ∧
      (∀ z i, z < 12 → i < 24 → (pstep h s).P.testBit (24 * z + i) =
        ((xor (s.P.testBit (24 * z + i)) (s.P.testBit (24 * z + h) && s.M.testBit (24 * z0 + i))) ||
          (decide (z = h) && s.M.testBit (24 * z0 + i)))) ∧
      (pstep h s).PM = s.PM ||| 2 ^ h ∧ (pstep h s).rk = s.rk + 1 ∧
      (pstep h s).DG = s.DG ||| 2 ^ (25 * h) ∧ (pstep h s).D24 = s.D24 ||| 2 ^ (24 * h) := by
  obtain ⟨k, hk, hlow⟩ := low_bit_exists hc
  have hk' := hk
  rw [cand_bit] at hk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk'
  obtain ⟨hMk, hk24, hk288⟩ := hk'
  obtain ⟨_, hlb⟩ := low_bit_spec hk hlow
  -- the pivot row
  have hp : Nat.land (Nat.div s.M (Nat.xor ((s.M >>> h) &&& REP24) (Nat.land ((s.M >>> h) &&& REP24)
      (Nat.pred ((s.M >>> h) &&& REP24))))) M24 = (s.M / 2 ^ k) &&& M24 := by
    show (s.M / (((s.M >>> h) &&& REP24) ^^^ (((s.M >>> h) &&& REP24) &&& (((s.M >>> h) &&& REP24) - 1)))) &&& M24 = _
    rw [hlb]
  have hpb : ∀ i, i < 24 → ((s.M / 2 ^ k) &&& M24).testBit i = s.M.testBit (24 * (k / 24) + i) := by
    intro i hi
    rw [Nat.testBit_and, Nat.testBit_div_two_pow, m24_eq, Nat.testBit_two_pow_sub_one]
    have : i + k = 24 * (k / 24) + i := by omega
    simp [hi, this]
  have hplt := land_m24_lt (s.M / 2 ^ k)
  refine ⟨k / 24, by omega, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · have : h + k = 24 * (k / 24) + h := by omega
    rw [← this]; exact hMk
  · intro z i hz hi
    show (s.M ^^^ ((s.M >>> h) &&& REP24) * Nat.land (Nat.div s.M (Nat.xor ((s.M >>> h) &&& REP24)
      (Nat.land ((s.M >>> h) &&& REP24) (Nat.pred ((s.M >>> h) &&& REP24))))) M24).testBit (24 * z + i) = _
    rw [hp, Nat.testBit_xor, sparse24_slot (cand_sparse s.M h) hplt z i hi, hpb i hi, cand_bit]
    have : h + 24 * z = 24 * z + h := by omega
    simp [this, show 24 * z % 24 = 0 by omega, show 24 * z < 288 by omega]
  · intro z i hz hi
    show ((s.P ^^^ ((s.P >>> h) &&& REP24) * Nat.land (Nat.div s.M (Nat.xor ((s.M >>> h) &&& REP24)
      (Nat.land ((s.M >>> h) &&& REP24) (Nat.pred ((s.M >>> h) &&& REP24))))) M24) |||
      (Nat.land (Nat.div s.M (Nat.xor ((s.M >>> h) &&& REP24)
      (Nat.land ((s.M >>> h) &&& REP24) (Nat.pred ((s.M >>> h) &&& REP24))))) M24 <<< (24 * h))).testBit (24 * z + i) = _
    rw [hp, Nat.testBit_or, Nat.testBit_xor, sparse24_slot (cand_sparse s.P h) hplt z i hi, hpb i hi, cand_bit,
      shl_slot hplt h z i hi, hpb i hi]
    have : h + 24 * z = 24 * z + h := by omega
    simp [this, show 24 * z % 24 = 0 by omega, show 24 * z < 288 by omega]
  · show s.PM ||| 1 <<< h = _
    rw [Nat.one_shiftLeft]
  · show s.DG ||| 1 <<< (25 * h) = _
    rw [Nat.one_shiftLeft]
  · show s.D24 ||| 1 <<< (24 * h) = _
    rw [Nat.one_shiftLeft]

/-! ## Structural invariant -/

/-- before step `h - 1` (steps `11 … h` done) -/
structure Pre (h : Nat) (s : ES) : Prop where
  pm : ∀ j, s.PM.testBit j = true → h ≤ j ∧ j < 12
  pz : ∀ z i, z < 12 → s.PM.testBit z = false → i < 24 → s.P.testBit (24 * z + i) = false
  rk : s.rk = cntB s.PM 12
  dg : ∀ i, s.DG.testBit i = (decide (i % 25 = 0) && s.PM.testBit (i / 25))
  d24 : ∀ i, s.D24.testBit i = (decide (i % 24 = 0) && s.PM.testBit (i / 24))

theorem cntB_set (x y h : Nat) (hxy : ∀ i, y.testBit i = (x.testBit i || decide (i = h))) (hx : x.testBit h = false) :
    ∀ k, cntB y k = cntB x k + (decide (h < k)).toNat := by
  intro k
  induction k with
  | zero => simp [cntB]
  | succ k ih =>
    show cntB y k + (y.testBit k).toNat = cntB x k + (x.testBit k).toNat + (decide (h < k + 1)).toNat
    rw [ih, hxy k]
    rcases lt_trichotomy k h with hk | hk | hk
    · have h1 : ¬ h < k := by omega
      have h2 : ¬ h < k + 1 := by omega
      have h3 : k ≠ h := by omega
      simp [h1, h2, h3]
    · subst hk; simp [hx]
    · have h1 : h < k := hk
      have h2 : h < k + 1 := by omega
      have h3 : k ≠ h := by omega
      simp [h1, h2, h3]; omega

theorem pre_step (h : Nat) (hh : h < 12) (s : ES) (hpre : Pre (h + 1) s) : Pre h (stepE h s) := by
  rw [stepE_eq]
  cases hb : Nat.beq (Nat.land (Nat.shiftRight s.M h) REP24) 0
  · have hc : (s.M >>> h) &&& REP24 ≠ 0 := by
      intro e; have : Nat.beq (Nat.land (Nat.shiftRight s.M h) REP24) 0 = true := by
        show Nat.beq ((s.M >>> h) &&& REP24) 0 = true; rw [e]; rfl
      rw [this] at hb; exact absurd hb (by decide)
    obtain ⟨z0, hz0, _, _, hP, hPM, hrk, hDG, hD24⟩ := pstep_bits h hh s hc
    show Pre h (pstep h s)
    have hpm' : ∀ j, (pstep h s).PM.testBit j = (s.PM.testBit j || decide (j = h)) := by
      intro j; rw [hPM, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases e : j = h
      · subst e; simp
      · have : h ≠ j := fun x => e x.symm
        simp [e, this]
    have hph : s.PM.testBit h = false := by
      cases e : s.PM.testBit h
      · rfl
      · have := hpre.pm h e; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [hpm'] at hj
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hj
      rcases hj with hj | hj
      · have := hpre.pm j hj; omega
      · omega
    · intro z i hz hzpm hi
      rw [hpm'] at hzpm
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hzpm
      rw [hP z i hz hi, hpre.pz z i hz hzpm.1 hi, hpre.pz z h hz hzpm.1 (by omega)]
      simp [hzpm.2]
    · rw [hrk, hpre.rk, cntB_set s.PM (pstep h s).PM h hpm' hph 12]
      simp [hh]
    · intro i
      rw [hDG, Nat.testBit_or, hpre.dg, Nat.testBit_two_pow, hpm']
      by_cases h1 : i % 25 = 0
      · by_cases h2 : i / 25 = h
        · have : 25 * h = i := by omega
          simp [h1, h2, this]
        · have : 25 * h ≠ i := by omega
          simp [h1, h2, this]
      · have : 25 * h ≠ i := by omega
        simp [h1, this]
    · intro i
      rw [hD24, Nat.testBit_or, hpre.d24, Nat.testBit_two_pow, hpm']
      by_cases h1 : i % 24 = 0
      · by_cases h2 : i / 24 = h
        · have : 24 * h = i := by omega
          simp [h1, h2, this]
        · have : 24 * h ≠ i := by omega
          simp [h1, h2, this]
      · have : 24 * h ≠ i := by omega
        simp [h1, this]
  · show Pre h s
    exact ⟨fun j hj => by have := hpre.pm j hj; omega, hpre.pz, hpre.rk, hpre.dg, hpre.d24⟩

/-! ## Span invariant -/

/-- slot `z` of a packed matrix as a vector of `F2^24` -/
def sv (N z : Nat) : Fin 24 → F2 := fun i => bitF N (24 * z + i.val)

/-- the twenty-four slots of a state -/
def fam (s : ES) : Fin 12 ⊕ Fin 12 → (Fin 24 → F2) := Sum.elim (fun h => sv s.P h.val) (fun z => sv s.M z.val)

def spanS (s : ES) : Submodule F2 (Fin 24 → F2) := Submodule.span F2 (Set.range (fam s))

theorem sv_mem (s : ES) (z : Fin 12) : sv s.M z.val ∈ spanS s :=
  Submodule.subset_span ⟨Sum.inr z, rfl⟩
theorem sv_memP (s : ES) (z : Fin 12) : sv s.P z.val ∈ spanS s :=
  Submodule.subset_span ⟨Sum.inl z, rfl⟩

theorem span_step (h : Nat) (hh : h < 12) (s : ES) (hpre : Pre (h + 1) s) : spanS (stepE h s) = spanS s := by
  rw [stepE_eq]
  cases hb : Nat.beq (Nat.land (Nat.shiftRight s.M h) REP24) 0
  · have hc : (s.M >>> h) &&& REP24 ≠ 0 := by
      intro e; have : Nat.beq (Nat.land (Nat.shiftRight s.M h) REP24) 0 = true := by
        show Nat.beq ((s.M >>> h) &&& REP24) 0 = true; rw [e]; rfl
      rw [this] at hb; exact absurd hb (by decide)
    obtain ⟨z0, hz0, hpiv, hM, hP, hPM, _, _, _⟩ := pstep_bits h hh s hc
    have hph : s.PM.testBit h = false := by
      cases e : s.PM.testBit h
      · rfl
      · have := hpre.pm h e; omega
    show spanS (pstep h s) = spanS s
    set s' := pstep h s with hs'
    -- new slots from old ones
    have nM : ∀ z : Fin 12, sv s'.M z.val = sv s.M z.val + bitF s.M (24 * z.val + h) • sv s.M z0 := by
      intro z; funext i
      simp only [sv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, bitF_bf]
      rw [hM z.val i.val z.isLt i.isLt, bf_xor, bf_and]
    have nP : ∀ z : Fin 12, sv s'.P z.val =
        if z.val = h then sv s.M z0 else sv s.P z.val + bitF s.P (24 * z.val + h) • sv s.M z0 := by
      intro z; funext i
      by_cases e : z.val = h
      · simp only [e, if_true, sv, bitF_bf]
        rw [hP h i.val hh i.isLt, hpre.pz h i.val hh hph i.isLt, hpre.pz h h hh hph (by omega)]
        simp
      · simp only [e, if_false, sv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, bitF_bf]
        rw [hP z.val i.val z.isLt i.isLt]
        simp only [e, decide_false, Bool.false_and, Bool.or_false, bf_xor, bf_and]
    -- old slots from new ones
    have oM : ∀ z : Fin 12, sv s.M z.val = sv s'.M z.val + bitF s.M (24 * z.val + h) • sv s'.P h := by
      intro z
      rw [nM z, nP ⟨h, hh⟩]
      simp only [if_true]
      rw [add_assoc, ← add_smul, f2_add_self, zero_smul, add_zero]
    have oP : ∀ z : Fin 12, sv s.P z.val =
        if z.val = h then 0 else sv s'.P z.val + bitF s.P (24 * z.val + h) • sv s'.P h := by
      intro z
      by_cases e : z.val = h
      · simp only [e, if_true]
        funext i; simp only [sv, Pi.zero_apply, bitF_bf]
        rw [hpre.pz h i.val hh hph i.isLt]; rfl
      · simp only [e, if_false]
        rw [nP z, nP ⟨h, hh⟩]
        simp only [e, if_false, if_true]
        rw [add_assoc, ← add_smul, f2_add_self, zero_smul, add_zero]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rcases i with z | z
      · show sv s'.P z.val ∈ spanS s
        rw [nP z]
        split_ifs
        · exact sv_mem s ⟨z0, hz0⟩
        · exact Submodule.add_mem _ (sv_memP s z) (Submodule.smul_mem _ _ (sv_mem s ⟨z0, hz0⟩))
      · show sv s'.M z.val ∈ spanS s
        rw [nM z]
        exact Submodule.add_mem _ (sv_mem s z) (Submodule.smul_mem _ _ (sv_mem s ⟨z0, hz0⟩))
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rcases i with z | z
      · show sv s.P z.val ∈ spanS s'
        rw [oP z]
        split_ifs
        · exact Submodule.zero_mem _
        · exact Submodule.add_mem _ (sv_memP s' z) (Submodule.smul_mem _ _ (sv_memP s' ⟨h, hh⟩))
      · show sv s.M z.val ∈ spanS s'
        rw [oM z]
        exact Submodule.add_mem _ (sv_mem s' z) (Submodule.smul_mem _ _ (sv_memP s' ⟨h, hh⟩))
  · rfl

/-! ## The whole elimination -/

theorem elimAux_spec : ∀ k s, k ≤ 12 → Pre k s → Pre 0 (elimAux k s) ∧ spanS (elimAux k s) = spanS s := by
  intro k
  induction k with
  | zero => intro s _ hp; exact ⟨hp, rfl⟩
  | succ k ih =>
    intro s hk hp
    have e : elimAux (k + 1) s = elimAux k (stepE k s) := rfl
    rw [e]
    obtain ⟨h1, h2⟩ := ih (stepE k s) (by omega) (pre_step k (by omega) s hp)
    exact ⟨h1, h2.trans (span_step k (by omega) s hp)⟩

theorem pre_init (M : Nat) : Pre 12 ⟨0, 0, 0, 0, 0, M⟩ where
  pm := by intro j hj; simp at hj
  pz := by intro z i _ _ _; simp
  rk := by
    show 0 = cntB 0 12
    have : ∀ k, cntB 0 k = 0 := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => show cntB 0 k + (Nat.testBit 0 k).toNat = 0; rw [ih]; simp
    rw [this]
  dg := by intro i; simp
  d24 := by intro i; simp

theorem elim_spec (M : Nat) : Pre 0 (elim M) ∧ spanS (elim M) = spanS ⟨0, 0, 0, 0, 0, M⟩ :=
  elimAux_spec 12 _ le_rfl (pre_init M)

/-! ## What `elimOk` certifies -/

theorem pm_lt (s : ES) (hp : Pre 0 s) : s.PM < 2 ^ 12 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  cases e : s.PM.testBit i
  · rfl
  · have := hp.pm i e; omega

theorem elimOk_spec (s : ES) (hp : Pre 0 s) (hok : elimOk s = true) :
    (∀ z y, z < 12 → y < 12 → s.M.testBit (24 * z + y) = false) ∧
    (∀ h j, h < 12 → j < 12 → h < j → s.P.testBit (24 * h + j) = false) ∧
    (∀ h j, h < 12 → j < 12 → s.PM.testBit j = true → s.P.testBit (24 * h + j) = decide (h = j)) ∧
    (∀ i, s.P.testBit i = true → s.PM.testBit (i / 24) = true) := by
  simp only [elimOk, Bool.and_eq_true, Nat.beq_eq] at hok
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hok
  have hpm := pm_lt s hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z y hz hy
    have := congrArg (fun x => Nat.testBit x (24 * z + y)) h1
    simp only [Nat.land_eq, Nat.testBit_and, Nat.zero_testBit] at this
    rw [left12_bit, decide_eq_true (by omega : (24 * z + y) % 24 < 12 ∧ 24 * z + y < 288), Bool.and_true] at this
    exact this
  · intro h j hh hj hhj
    have := congrArg (fun x => Nat.testBit x (24 * h + j)) h2
    simp only [Nat.land_eq, Nat.testBit_and, Nat.zero_testBit] at this
    rw [hm12_bit, decide_eq_true (by omega : 24 * h + j < 288 ∧ (24 * h + j) % 24 < 12 ∧
      (24 * h + j) / 24 < (24 * h + j) % 24), Bool.and_true] at this
    exact this
  · intro h j hh hj hpj
    have := congrArg (fun x => Nat.testBit x (24 * h + j)) h3
    simp only [Nat.land_eq, Nat.mul_eq, Nat.testBit_and, hp.dg] at this
    rw [Nat.mul_comm s.PM REP24, sparse24_slot rep24_sparse (lt_of_lt_of_le hpm (by norm_num)) h j (by omega), rep24_bit,
      hpj] at this
    have e24 : 24 * h % 24 = 0 ∧ 24 * h < 288 := by omega
    by_cases e : h = j
    · subst e
      have e1 : (24 * h + h) % 25 = 0 := by omega
      have e2 : (24 * h + h) / 25 = h := by omega
      simp [e24, e1, e2, hpj] at this
      simp [this]
    · have e1 : (24 * h + j) % 25 ≠ 0 := by omega
      simp [e24, e1] at this
      simp [this, e]
  · intro i hi
    have := congrArg (fun x => Nat.testBit x i) h4
    simp only [Nat.land_eq, Nat.mul_eq, Nat.testBit_and, hi, Bool.true_and] at this
    have hs : ∀ j, s.D24.testBit j = true → j % 24 = 0 := by
      intro j hj; rw [hp.d24] at hj; simp at hj; exact hj.1
    rw [testBit_sparse_mul (by norm_num) s.D24 M24 (by rw [m24_eq]; omega) hs, hp.d24] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    have e : 24 * (i / 24) / 24 = i / 24 := by omega
    rw [e] at this
    exact this.1.2

end B334.BCP
