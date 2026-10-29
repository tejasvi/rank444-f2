import B334.E1x.RT9P
import B334.E1x.TransBits
import B334.E1x.Fact
import B334.Bind.Span

/-! # The verified row table for ⟨3,3,4⟩: entries, their kernel check, `entry_sound`

Port of `RT/Defs.lean` and `RT/Sound.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to ⟨3,3,4⟩.

A **row** is a subspace `U` of `A = F₂⁹` with a cap. An **entry** (layout in `RT9.lean`) proves the row's bound from the
class table: a class `c` whose subspace `K_c` has the bound `lb c`, and a G₀ element `(P, Q)` (`actF P Q v = P v Q`; no
transpose for ⟨3,3,4⟩) with `(P, Q)(U) ⊆ K_c`.
* The class table `CL` has 96-bit slots: `[4] n`, `[5] lb`, `n` 9-bit vectors spanning `K_c^⊥` (`K_c` = their common
  kernel); class indices are `< 1024` (710 classes).
* `entryOK R CL e`: the span of the primal basis equals the common kernel of the dual one (as point masks), `P`, `Q`
  invertible, `(P, Q)` maps the primal basis into `K_c`, and `R ≤ cap + lb c`.
* **`entry_sound`**: `Fact (kM CL c) (cLB CL c)` and `entryOK R CL e` give `Fact (dualM e) (R - eCap e)`.
* `classFact_of_quotLB`: a class's `Fact` from a `QuotLB` row (e.g. `RowValid basis lb`), when the class's point mask is
  the span of the basis (`spanEq`: the doubling mask `spanL` of the basis, equal to `B334.Bind.inSpan` on every
  mask by `spanL_testBit`; a brute-force `inSpan` test per mask ran out of kernel memory for 38 classes). -/

namespace B334.E1x.RT

open B334.BC B334.BCP B334.Core Finset

/-! ## Class table fields -/
def cN (CL c : Nat) : Nat := (CL >>> (96 * c)) % 16
def cLB (CL c : Nat) : Nat := (CL >>> (96 * c + 4)) % 32
def cV (CL c j : Nat) : Nat := (CL >>> (96 * c + 9 + 9 * j)) % 512

/-- `w` lies in the class subspace `K_c` -/
def inK (CL c w : Nat) : Bool := Nat.rec (motive := fun _ => Bool) true (fun j b => b && !par (w &&& cV CL c j)) (cN CL c)
/-- the point mask of `K_c` -/
def kM (CL c : Nat) : Nat := kerM9 (cV CL c) (cN CL c)

/-- the span of the first `d` vectors by doubling (`S ∪ (S + u)`), cut to 512 bits -/
def spanM (e : Nat) : Nat :=
  M512 &&& Nat.rec (motive := fun _ => Nat) 1 (fun i S => S ||| TransBits.trans S (eV e i)) (eD e)

/-- all primal vectors map into `K_c` under `(P, Q)` -/
def mapsIn (CL e : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i b => b && inK CL (eCls e) (actF (eP e) (eQ e) (eV e i))) (eD e)

/-- **the entry check** -/
def entryOK (R CL e : Nat) : Bool :=
  Nat.ble (eD e) 9 && spanM e == dualM e && isGL (eP e) && isGL (eQ e) && mapsIn CL e &&
    Nat.ble R (eCap e + cLB CL (eCls e))

/-! ## Class subspaces -/

theorem cV_lt (CL c j : Nat) : cV CL c j < 512 := Nat.mod_lt _ (by norm_num)
theorem eV_lt (e i : Nat) : eV e i < 512 := Nat.mod_lt _ (by norm_num)

theorem inK_spec (CL c w : Nat) : inK CL c w = true ↔ ∀ j < cN CL c, par (w &&& cV CL c j) = false := by
  unfold inK
  generalize cN CL c = n
  induction n with
  | zero => simp
  | succ n ih =>
    show (Nat.rec (motive := fun _ => Bool) true (fun j b => b && !par (w &&& cV CL c j)) n &&
      !par (w &&& cV CL c n)) = true ↔ _
    rw [Bool.and_eq_true, ih, Bool.not_eq_true']
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact h1 j h
      · rw [h]; exact h2
    · intro h; exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

theorem inK_xor {CL c x y : Nat} (hx : x < 512) (hy : y < 512) (h1 : inK CL c x = true) (h2 : inK CL c y = true) :
    inK CL c (x ^^^ y) = true := by
  rw [inK_spec] at h1 h2 ⊢
  intro j hj
  rw [par_xor9 x y _ hx hy, h1 j hj, h2 j hj]; rfl

theorem inK_zero (CL c : Nat) : inK CL c 0 = true := by
  rw [inK_spec]; intro j _; exact par_zero_and _

theorem kM_testBit (CL c w : Nat) (hw : w < 512) : (kM CL c).testBit w = inK CL c w := by
  have h := kerM9_testBit (cV CL c) (cV_lt CL c) (cN CL c) w hw
  cases e : inK CL c w
  · cases e2 : (kM CL c).testBit w
    · rfl
    · exact absurd ((inK_spec CL c w).mpr (h.mp e2)) (by rw [e]; exact Bool.false_ne_true)
  · exact h.mpr ((inK_spec CL c w).mp e)

/-! ## Span induction -/

theorem spanRec_ind (e : Nat) (Pr : Nat → Prop) (h0 : Pr 0) (hgen : ∀ i < eD e, Pr (eV e i))
    (hxor : ∀ x y, x < 512 → y < 512 → Pr x → Pr y → Pr (x ^^^ y)) :
    ∀ k ≤ eD e, ∀ w < 512,
      (Nat.rec (motive := fun _ => Nat) 1 (fun i S => S ||| TransBits.trans S (eV e i)) k).testBit w = true →
      Pr w := by
  intro k
  induction k with
  | zero =>
    intro _ w _ h
    simp only [Nat.rec_zero] at h
    have hw0 : w = 0 := by
      by_contra hne
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h; exact hne h
    rw [hw0]; exact h0
  | succ k ih =>
    intro hk w hw h
    have h' : (Nat.rec (motive := fun _ => Nat) 1 (fun i S => S ||| TransBits.trans S (eV e i)) k |||
        TransBits.trans (Nat.rec (motive := fun _ => Nat) 1
          (fun i S => S ||| TransBits.trans S (eV e i)) k) (eV e k)).testBit w = true := h
    rw [Nat.testBit_or, Bool.or_eq_true, TransBits.trans_testBit _ _ _ (eV_lt e k) hw] at h'
    have hk' : k ≤ eD e := Nat.le_of_succ_le hk
    rcases h' with h1 | h2
    · exact ih hk' w hw h1
    · have hx : w ^^^ eV e k < 512 := xor_lt512 hw (eV_lt e k)
      have := hxor _ _ hx (eV_lt e k) (ih hk' _ hx h2) (hgen k (Nat.lt_of_succ_le hk))
      rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this

theorem spanM_ind (e : Nat) (Pr : Nat → Prop) (h0 : Pr 0) (hgen : ∀ i < eD e, Pr (eV e i))
    (hxor : ∀ x y, x < 512 → y < 512 → Pr x → Pr y → Pr (x ^^^ y)) (w : Nat) (h : (spanM e).testBit w = true) :
    w < 512 ∧ Pr w := by
  have h' : (M512 &&& Nat.rec (motive := fun _ => Nat) 1
      (fun i S => S ||| TransBits.trans S (eV e i)) (eD e)).testBit w = true := h
  rw [Nat.testBit_and, Bool.and_eq_true, M512_bit, decide_eq_true_eq] at h'
  exact ⟨h'.1, spanRec_ind e Pr h0 hgen hxor (eD e) le_rfl w h'.1 h'.2⟩

/-! ## The entry theorem -/

theorem mapsIn_spec (CL e : Nat) (h : mapsIn CL e = true) :
    ∀ i < eD e, inK CL (eCls e) (actF (eP e) (eQ e) (eV e i)) = true := by
  unfold mapsIn at h
  revert h
  generalize eD e = n
  induction n with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro h i hi
    have h' : (Nat.rec (motive := fun _ => Bool) true
        (fun i b => b && inK CL (eCls e) (actF (eP e) (eQ e) (eV e i))) n &&
        inK CL (eCls e) (actF (eP e) (eQ e) (eV e n))) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih h'.1 i hlt
    · rw [heq]; exact h'.2

/-- **Entry theorem.** -/
theorem entry_sound (R CL e : Nat) (hcls : Fact (kM CL (eCls e)) (cLB CL (eCls e))) (h : entryOK R CL e = true) :
    Fact (dualM e) (R - eCap e) := by
  unfold entryOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hsd⟩, hP⟩, hQ⟩, hmap⟩, hR⟩ := h
  have hgen := mapsIn_spec CL e hmap
  intro n av b c hav hd
  have hk := hcls n (fun s => actF (eP e) (eQ e) (av s)) _ _ (fun s => actF_lt _ _ _) (isDecomp_actF hd hP hQ)
  refine le_trans (by omega) (le_trans hk (Finset.card_le_card ?_))
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  cases e2 : (dualM e).testBit (av s)
  · rfl
  · exfalso
    rw [← hsd] at e2
    obtain ⟨_, hin⟩ := spanM_ind e (fun w => inK CL (eCls e) (actF (eP e) (eQ e) w) = true)
      (by show inK CL (eCls e) (actF (eP e) (eQ e) 0) = true
          rw [actF_zero]; exact inK_zero _ _) hgen
      (fun x y hx hy h1 h2 => by
        show inK CL (eCls e) (actF (eP e) (eQ e) (x ^^^ y)) = true
        rw [actF_xor _ _ _ _ hx hy]; exact inK_xor (actF_lt _ _ _) (actF_lt _ _ _) h1 h2)
      (av s) e2
    have hin' : inK CL (eCls e) (actF (eP e) (eQ e) (av s)) = true := hin
    rw [kM_testBit _ _ _ (actF_lt _ _ _), hin'] at hs
    exact absurd hs (by decide)

/-! ## Class facts from `QuotLB` rows -/

/-- the span of `B` as a point mask, by doubling (`S ∪ (S + b)`) -/
def spanL : List Nat → Nat
  | [] => 1
  | b :: B => spanL B ||| TransBits.trans (spanL B) b

theorem inSpan_cons (b : Nat) (B : List Nat) (w : Nat) :
    B334.Bind.inSpan (b :: B) w = (B334.Bind.inSpan B w || B334.Bind.inSpan B (w ^^^ b)) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true]
  unfold B334.Bind.inSpan
  rw [B334.Bind.anyLT_iff, B334.Bind.anyLT_iff, B334.Bind.anyLT_iff]
  simp only [List.length_cons, beq_iff_eq]
  constructor
  · rintro ⟨s, hs, h⟩
    change (if s.testBit 0 = true then b else 0) ^^^ B334.Bind.xorSub B (s / 2) = w at h
    have hs2 : s / 2 < 2 ^ B.length := by rw [Nat.pow_succ] at hs; omega
    by_cases h0 : s.testBit 0 = true
    · rw [if_pos h0] at h
      refine Or.inr ⟨s / 2, hs2, ?_⟩
      subst h
      rw [Nat.xor_comm b, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · rw [if_neg h0, Nat.zero_xor] at h
      exact Or.inl ⟨s / 2, hs2, h⟩
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
    · refine ⟨2 * s, by rw [Nat.pow_succ]; omega, ?_⟩
      have e0 : (2 * s).testBit 0 = false := by rw [Nat.testBit_zero, decide_eq_false_iff_not]; omega
      have e1 : 2 * s / 2 = s := by omega
      change (if (2 * s).testBit 0 = true then b else 0) ^^^ B334.Bind.xorSub B (2 * s / 2) = w
      rw [e0, e1, if_neg (show ¬(false = true) by decide), Nat.zero_xor]
      exact h
    · refine ⟨2 * s + 1, by rw [Nat.pow_succ]; omega, ?_⟩
      have e0 : (2 * s + 1).testBit 0 = true := by rw [Nat.testBit_zero, decide_eq_true_iff]; omega
      have e1 : (2 * s + 1) / 2 = s := by omega
      change (if (2 * s + 1).testBit 0 = true then b else 0) ^^^ B334.Bind.xorSub B ((2 * s + 1) / 2) = w
      rw [e0, e1, if_pos rfl, h, Nat.xor_comm w b, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem spanL_testBit : ∀ (B : List Nat), (∀ b ∈ B, b < 2 ^ 9) → ∀ w < 512,
    (spanL B).testBit w = B334.Bind.inSpan B w
  | [], _ => by decide +kernel
  | b :: B, hB => by
    intro w hw
    have hb : b < 512 := hB b List.mem_cons_self
    have hB' : ∀ b' ∈ B, b' < 2 ^ 9 := fun b' h => hB b' (List.mem_cons_of_mem _ h)
    have hwb : w ^^^ b < 512 := B334.E1x.xor_lt512 hw hb
    show (spanL B ||| TransBits.trans (spanL B) b).testBit w = _
    rw [Nat.testBit_or, TransBits.trans_testBit _ _ _ hb hw, spanL_testBit B hB' w hw,
      spanL_testBit B hB' _ hwb, inSpan_cons]

/-- the point mask `m` is the span of the basis `B` (the doubling mask `spanL B`, 512 bit comparisons) -/
def spanEq (m : Nat) (B : List Nat) : Bool := allLT 512 (fun w => m.testBit w == (spanL B).testBit w)

theorem spanEq_spec {m : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < 2 ^ 9) (h : spanEq m B = true) :
    ∀ w < 512, m.testBit w = true ↔ vecOfMask (3 * 3) w ∈ spanMasks B := by
  intro w hw
  have h1 := allLT_spec h w hw
  rw [beq_iff_eq] at h1
  rw [h1, spanL_testBit B hB w hw, B334.Bind.mem_spanMasks_iff B hB w (by omega)]

/-- **A class's `Fact` from its `QuotLB` row**, e.g. `RowValid basis lb` (`B334.Statement`) -/
theorem classFact_of_quotLB {CL c lb : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < 2 ^ 9)
    (hrow : QuotLB T334 (spanMasks B) lb) (hspan : spanEq (kM CL c) B = true) (hlb : cLB CL c ≤ lb) :
    Fact (kM CL c) (cLB CL c) :=
  fact_mono hlb (fun _ _ h => h) (fact_of_quotLB hrow (spanEq_spec hB hspan))

/-! ## The rows of an IP from the classes' `RowValid` facts (the interface: `basisOf`, `lbOf` from the table
data module, `hcls` discharged at assembly by induction on dimension) -/

/-- class `c` of the class table is backed by the class data: its bound is 0, or its point mask is the span of
`basisOf c` and its bound is at most `lbOf c ≠ 0` (`c < 711`) -/
def classOK (CL : Nat) (basisOf : Nat → List Nat) (lbOf : Nat → Nat) (c : Nat) : Bool :=
  Nat.beq (cLB CL c) 0 ||
    (Nat.blt c 711 && !(Nat.beq (lbOf c) 0) && Nat.ble (cLB CL c) (lbOf c) && spanEq (kM CL c) (basisOf c))

/-- `classFact_of_ok` for one class, with that class's data facts only -/
theorem classFact_of_ok1 {CL : Nat} {basisOf : Nat → List Nat} {lbOf : Nat → Nat} {c : Nat}
    (hB : ∀ b ∈ basisOf c, b < 2 ^ 9) (hcls : c < 711 → lbOf c ≠ 0 → RowValid (basisOf c) (lbOf c))
    (h : classOK CL basisOf lbOf c = true) : Fact (kM CL c) (cLB CL c) := by
  unfold classOK at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h
  · have e : cLB CL c = 0 := Nat.eq_of_beq_eq_true h0
    rw [e]
    intro n av b c' hav hd
    exact Nat.zero_le _
  · simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨hc, hlb0⟩, hle⟩, hspan⟩ := h
    have hne : lbOf c ≠ 0 := fun e => by rw [e] at hlb0; exact absurd hlb0 (by decide)
    exact classFact_of_quotLB hB (hcls hc hne) hspan hle

theorem classFact_of_ok {CL : Nat} {basisOf : Nat → List Nat} {lbOf : Nat → Nat}
    (hB : ∀ c, ∀ b ∈ basisOf c, b < 2 ^ 9)
    (hcls : ∀ c, c < 711 → lbOf c ≠ 0 → RowValid (basisOf c) (lbOf c)) {c : Nat}
    (h : classOK CL basisOf lbOf c = true) : Fact (kM CL c) (cLB CL c) :=
  classFact_of_ok1 (hB c) (hcls c) h

/-- **The rows of an IP**: every slot's row bound from the classes' `RowValid` facts, given `entryOK` and `classOK`
for every slot (decide facts) -/
theorem rows_of_classes (R CL Ntab : Nat) (tab : Nat → Nat) (basisOf : Nat → List Nat) (lbOf : Nat → Nat)
    (hB : ∀ c, ∀ b ∈ basisOf c, b < 2 ^ 9)
    (hcls : ∀ c, c < 711 → lbOf c ≠ 0 → RowValid (basisOf c) (lbOf c))
    (hent : ∀ i < Ntab, entryOK R CL (tab i) = true ∧ classOK CL basisOf lbOf (eCls (tab i)) = true) :
    ∀ i < Ntab, Fact (dualM (tab i)) (R - eCap (tab i)) :=
  fun i hi => entry_sound R CL (tab i) (classFact_of_ok hB hcls (hent i hi).2) (hent i hi).1

/-- **The rows of one run's IP** from the facts of the classes its slots use only (`P`: for a run of class `c`, the
classes `c' < nCls` of larger dimension, the `RunHyp`): `P` of every slot's class is a decide fact of the IP -/
theorem rows_of_classes' (R CL Ntab : Nat) (tab : Nat → Nat) (basisOf : Nat → List Nat) (lbOf : Nat → Nat)
    (P : Nat → Prop) (hB : ∀ c, P c → ∀ b ∈ basisOf c, b < 2 ^ 9)
    (hcls : ∀ c, P c → c < 711 → lbOf c ≠ 0 → RowValid (basisOf c) (lbOf c))
    (hent : ∀ i < Ntab, entryOK R CL (tab i) = true ∧ classOK CL basisOf lbOf (eCls (tab i)) = true ∧
      P (eCls (tab i))) :
    ∀ i < Ntab, Fact (dualM (tab i)) (R - eCap (tab i)) := fun i hi =>
  entry_sound R CL (tab i)
    (classFact_of_ok1 (hB _ (hent i hi).2.2) (hcls _ (hent i hi).2.2) (hent i hi).2.1) (hent i hi).1

end B334.E1x.RT
