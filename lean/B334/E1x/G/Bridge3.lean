import B334.E1x.G.Bridge2
import B334.E1x.Pad
/-! # Canonicity by the orbit minimum, and the E1 theorem for one coset IP

Port of `E1G/Bridge3.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to ⟨3,3,4⟩: the group elements are G₀'s
`(P, Q)` with `actF P Q v = P v Q` (no transpose; `E1x/Act.lean`, `E1x/Decomp.lean`), the decompositions have 3×4 second
and 4×3 third factors, and the conclusion is `B334.E1x.E1Concl Em C.R` (`E1x/Pad.lean`), which the padding and the
`QuotLB` bridge (`E1x/Bridge.lean`) turn into `QuotLB T334 E (C.R + 1)`.

* `isDecomp_actF_nz`: the group action on first factors comes with nonzero second and third factors.
* `xOf_act`: a group element fixing `E` permutes the cosets as the IP's label permutation says, so the multiplicity
  vector of the transformed decomposition is the image of the old one (`push`).
* `e1_sound`: given the IP facts (checked once by `decide`), the verified rows, the leaf facts, and an accepted, glued
  chain of blocks whose first block is the root (empty prefix), no decomposition has exactly `R` first factors outside
  `E`. If a decomposition's multiplicity vector is not canonical, a group element makes it larger in the reversed
  packing; this is bounded, so a canonical decomposition exists, and `chain_sound` refutes it. -/
set_option maxRecDepth 20000
namespace B334.E1x.E1GS
open Finset B334.Core Matrix
set_option exponentiation.threshold 600

theorem isDecomp_actF_nz {n : ℕ} {av : Fin n → ℕ} {b : Fin n → M34} {c : Fin n → M43}
    (hd : IsDecomp (fun s => toM3 (av s)) b c) (hbc : ∀ s, b s ≠ 0 ∧ c s ≠ 0) {P Q : Nat}
    (hP : isGL P = true) (hQ : isGL Q = true) :
    ∃ (b' : Fin n → M34) (c' : Fin n → M43), IsDecomp (fun s => toM3 (actF P Q (av s))) b' c' ∧
      ∀ s, b' s ≠ 0 ∧ c' s ≠ 0 :=
  ⟨_, _, isDecomp_actF hd hP hQ, actF_nz hbc hP hQ⟩

/-- the double count behind `msum_xOf`, for any predicate on labels -/
theorem sum_xOf_pred {n : ℕ} (av : Fin n → ℕ) (Em VT N : ℕ) (p : ℕ → Prop) [DecidablePred p] (hN : N ≤ 127)
    (hC : Cosets Em VT N) (hav : ∀ s, av s < 512) :
    ∑ l ∈ range 127, (if p l then xOf av Em VT N l else 0) =
      (univ.filter (fun s : Fin n => Em.testBit (av s) = false ∧ ∃ l < N, p l ∧ Em.testBit (av s ^^^ vt VT l) = true)).card := by
  have e1 : ∀ l ∈ range 127, (if p l then xOf av Em VT N l else 0) =
      ∑ s : Fin n, (if l < N ∧ p l ∧ Em.testBit (av s) = false ∧ Em.testBit (av s ^^^ vt VT l) = true then 1 else 0) := by
    intro l _
    unfold xOf
    rw [Finset.card_filter]
    by_cases h1 : p l <;> by_cases h2 : l < N <;> simp [h1, h2]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm, Finset.card_filter]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : Em.testBit (av s) = false ∧ ∃ l < N, p l ∧ Em.testBit (av s ^^^ vt VT l) = true
  · obtain ⟨h0, l, hl, hp, hE⟩ := hs
    rw [if_pos ⟨h0, l, hl, hp, hE⟩, Finset.sum_eq_single l]
    · rw [if_pos ⟨hl, hp, h0, hE⟩]
    · intro l' _ hne
      rw [if_neg]
      rintro ⟨hl', _, _, hE'⟩
      exact hne (coset_unique hC (av s) (hav s) l' l hl' hl hE' hE)
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hs]
    apply Finset.sum_eq_zero; intro l _
    rw [if_neg]
    rintro ⟨hl, hp, h0, hE⟩; exact hs ⟨h0, l, hl, hp, hE⟩

/-- the group element `(P, Q)` of G₀ fixes `E` and moves coset `l` to coset `gpf gp l` -/
structure GElt (Em VT N gp : ℕ) (P Q : ℕ) : Prop where
  glP : isGL P = true
  glQ : isGL Q = true
  fixE : ∀ a < 512, Em.testBit (actF P Q a) = Em.testBit a
  lab : ∀ l < N, gpf gp l < N ∧ Em.testBit (actF P Q (vt VT l) ^^^ vt VT (gpf gp l)) = true

theorem xOf_act {Em VT N gp : ℕ} {P Q : ℕ} (hN : N ≤ 127) (hC : Cosets Em VT N) (hg : GElt Em VT N gp P Q)
    {n : ℕ} (av : Fin n → ℕ) (hav : ∀ s, av s < 512) (l' : ℕ) (hl' : l' < 127) :
    xOf (fun s => actF P Q (av s)) Em VT N l' = push gp (xOf av Em VT N) l' := by
  have hact : ∀ s l, Em.testBit (av s) = false → l < N → Em.testBit (av s ^^^ vt VT l) = true →
      Em.testBit (actF P Q (av s) ^^^ vt VT (gpf gp l)) = true := by
    intro s l h0 hl hE
    have e : actF P Q (av s) ^^^ vt VT (gpf gp l) =
        actF P Q (av s ^^^ vt VT l) ^^^ (actF P Q (vt VT l) ^^^ vt VT (gpf gp l)) := by
      rw [actF_xor P Q _ _ (hav s) (vt_lt VT l), Nat.xor_assoc, ← Nat.xor_assoc (actF P Q (vt VT l)),
        Nat.xor_self, Nat.zero_xor]
    rw [e]
    apply hC.xor_mem _ (actF_lt _ _ _) _ (xor_lt512 (actF_lt _ _ _) (vt_lt VT _))
    · rw [hg.fixE _ (xor_lt512 (hav s) (vt_lt VT l))]; exact hE
    · exact (hg.lab l hl).2
  -- both sides count the factors outside `E` whose coset maps to `l'`
  unfold push
  by_cases hl'N : l' < N
  · rw [show xOf (fun s => actF P Q (av s)) Em VT N l' =
        (univ.filter (fun s : Fin n => Em.testBit (av s) = false ∧
          ∃ l < N, gpf gp l = l' ∧ Em.testBit (av s ^^^ vt VT l) = true)).card by
      unfold xOf; rw [if_pos hl'N]
      apply congrArg Finset.card; apply Finset.filter_congr; intro s _
      rw [hg.fixE _ (hav s)]
      constructor
      · rintro ⟨h0, hE⟩
        obtain ⟨l, hl, hEl⟩ := hC.cover (av s) (hav s) h0
        refine ⟨h0, l, hl, ?_, hEl⟩
        exact coset_unique hC _ (actF_lt _ _ _) _ _ (hg.lab l hl).1 hl'N (hact s l h0 hl hEl) hE
      · rintro ⟨h0, l, hl, rfl, hEl⟩
        exact ⟨h0, hact s l h0 hl hEl⟩]
    exact (sum_xOf_pred av Em VT N (fun l => gpf gp l = l') hN hC hav).symm
  · rw [xOf_ge _ _ _ _ _ (by omega)]
    symm
    apply Finset.sum_eq_zero; intro l hl
    rw [Finset.mem_range] at hl
    split
    · next h' =>
      by_cases hlN : l < N
      · have := (hg.lab l hlN).1; omega
      · exact xOf_ge _ _ _ _ _ (by omega)
    · rfl

/-! ## The theorem for one coset IP -/

/-- the facts about one coset IP that are checked once (by `decide`) -/
structure IPOK (C : E1G.Ctx) (Em LB LBR UB UBR Ntab nrows : ℕ) (sl tab : ℕ → ℕ) (GE : ℕ → ℕ × ℕ) : Prop where
  N_le : C.N ≤ 127
  R_le : C.R ≤ 31
  R_pos : 1 ≤ C.R
  DOM_lt : C.DOM < 2 ^ 512
  cosets : Cosets Em C.VT C.N
  domperp : DomPerp C.DOM Em
  planes : Planes LB C.VT C.N
  planesR : PlanesR LB LBR
  sl_spec : ∀ i < Ntab, sl i = SlotG.slot LB LBR (tab i) ∧ SlotG.dualIn C.DOM (tab i) = true
  sl_zero : ∀ i, Ntab ≤ i → i < 2 ^ 15 → sl i = 0
  Ntab_le : Ntab ≤ 2 ^ 15
  UB_eq : UB = V (fun l => E1G.fld UB l)
  UBR_eq : UBR = VR (fun l => E1G.fld UB l)
  UB_le : ∀ l < 127, E1G.fld UB l ≤ 2 ^ 32
  capslot : ∀ l < C.N, nrows + l < Ntab ∧ (∀ j < C.N, (smask (sl (nrows + l))).testBit j = decide (j = l)) ∧
    scap (sl (nrows + l)) = E1G.fld UB l
  grp : ∀ g < 2048, GElt Em C.VT C.N (C.GP g) (GE g).1 (GE g).2

theorem msum_single (x : ℕ → ℕ) (l : ℕ) (hl : l < 127) : msum x (2 ^ l) = x l := by
  unfold msum
  rw [Finset.sum_eq_single l]
  · rw [Nat.testBit_two_pow_self, if_pos rfl]
  · intro j _ hj; rw [Nat.testBit_two_pow, if_neg (by simp; omega)]
  · intro h; exact absurd (Finset.mem_range.mpr hl) h

/-- a label-cap mask: among the real labels only `l` (labels `≥ N` carry no copies) -/
theorem msum_cap (x : ℕ → ℕ) (M l N : ℕ) (hN : N ≤ 127) (hl : l < N) (hx : ∀ j, N ≤ j → x j = 0)
    (hM : ∀ j < N, M.testBit j = decide (j = l)) : msum x M = x l := by
  unfold msum
  rw [Finset.sum_eq_single l]
  · rw [hM l hl, decide_eq_true rfl, if_pos rfl]
  · intro j hj hne
    rw [Finset.mem_range] at hj
    by_cases hjN : j < N
    · rw [hM j hjN, decide_eq_false hne, if_neg (by simp)]
    · rw [hx j (by omega)]; simp
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem VR_lt (a : ℕ → ℕ) (h : ∀ l < 127, a l < 2 ^ 128) : VR a < 2 ^ 16256 :=
  pk_lt 128 _ 127 (fun j hj => h _ (by omega))

/-- **E1 for one coset IP.** -/
theorem e1_sound (C : E1G.Ctx) (Em LB LBR UB UBR Ntab nrows : ℕ) (sl tab : ℕ → ℕ) (GE : ℕ → ℕ × ℕ)
    (h : IPOK C Em LB LBR UB UBR Ntab nrows sl tab GE)
    (hrow : ∀ i < Ntab, Fact (RT.dualM (tab i)) (C.R - RT.eCap (tab i)))
    (hLF : ∀ pl, C.LF pl = true → B334.BCP.NoDecomp (termsOf C.R C.VT pl) C.R C.DOM)
    (Ss : List ℕ) (hne : 0 < Ss.length) (hroot : Ss.getD 0 0 % 2 ^ 13 = 0)
    (hblk : ∀ i < Ss.length, E1G.block C sl UB UBR (Ss.getD i 0) = true)
    (hglue : ∀ i < Ss.length, ∀ j < E1G.rd 8 (E1G.bS2 (Ss.getD i 0)), ∃ i', i < i' ∧ i' < Ss.length ∧
      (E1G.glue ((E1G.hdr (E1G.bS2 (Ss.getD i 0))).2.1 / 2 ^ (695 * j) % 2 ^ 695) (Ss.getD i' 0) = true ∨
       E1G.glue0 ((E1G.hdr (E1G.bS2 (Ss.getD i 0))).2.1 / 2 ^ (695 * j) % 2 ^ 695) (Ss.getD i' 0) = true)) :
    E1Concl Em C.R := by
  have hN := h.N_le
  -- induction on how far the reversed packing of the multiplicity vector is below its bound
  suffices key : ∀ m, ∀ (n : ℕ) (av : Fin n → ℕ) (b : Fin n → M34) (c : Fin n → M43), (∀ s, av s < 512) →
      IsDecomp (fun s => toM3 (av s)) b c → (∀ s, b s ≠ 0 ∧ c s ≠ 0) →
      (univ.filter (fun s : Fin n => Em.testBit (av s) = false)).card = C.R →
      2 ^ 16256 - VR (xOf av Em C.VT C.N) = m → False from
    fun n av b c hav hd hbc hR => key _ n av b c hav hd hbc hR rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n av b c hav hd hbc hR hm
  set x := xOf av Em C.VT C.N with hxdef
  have hsum : ∑ l ∈ range 127, x l = C.R := by rw [hxdef, sum_xOf av Em C.VT C.N hN h.cosets hav, hR]
  have hxle : ∀ l < 127, x l ≤ C.R := by
    intro l hl
    rw [← hsum]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hl)
  have hxb : ∀ l < 127, x l < 2 ^ 128 := fun l hl => lt_of_le_of_lt (hxle l hl) (by have := h.R_le; omega)
  by_cases hcan : ∀ g < 2048, ¬ (VR x < VR (push (C.GP g) x))
  · -- canonical: the chain refutes it
    have hslot : ∀ i < 2 ^ 15, SlotV x (sl i) := by
      intro i hi
      by_cases hiN : i < Ntab
      · obtain ⟨e1, e2⟩ := h.sl_spec i hiN
        rw [e1]
        exact slot_valid LB LBR C.VT C.N Em C.DOM C.R hN h.planes h.planesR h.cosets h.domperp (tab i) (hrow i hiN) e2
          av b c hav hd hR
      · rw [h.sl_zero i (by omega) hi]; exact slotV_zero x
    have hxub : ∀ l < 127, x l ≤ E1G.fld UB l := by
      intro l hl
      by_cases hlN : l < C.N
      · obtain ⟨h1, h2, h3⟩ := h.capslot l hlN
        have := (hslot (nrows + l) (by have := h.Ntab_le; omega)).1
        rw [h3, msum_cap x _ l C.N hN hlN (fun j hj => xOf_ge _ _ _ _ _ hj) h2] at this
        exact this
      · rw [hxdef, xOf_ge _ _ _ _ _ (by omega)]; exact Nat.zero_le _
    have hglob : Glob C x := {
      N_le := hN
      R_le := h.R_le
      xN := fun l hl => xOf_ge _ _ _ _ _ hl
      xR := hsum
      leaf := fun pl hx hleaf =>
        leafOK_bridge C Em hN h.cosets h.domperp hLF av b c hav hd hbc hR pl hx hleaf
      canon := hcan
      gp := fun g hg l hl => ((h.grp g hg).lab l hl).1 }
    have hx0 : ∃ l < 127, 0 < x l := by
      by_contra hc
      push_neg at hc
      have : ∑ l ∈ range 127, x l = 0 := Finset.sum_eq_zero (fun l hl => by
        have := hc l (Finset.mem_range.mp hl); omega)
      have := h.R_pos; omega
    apply chain_sound C sl UB UBR (fun l => E1G.fld UB l) x hglob hslot h.UB_eq h.UBR_eq h.UB_le hxub hx0 Ss hblk hglue 0 hne
    -- the root block's start state: empty prefix, mode 0
    have h0 : Ss.getD 0 0 % 2 = 0 := by
      have := Nat.mod_mod_of_dvd (Ss.getD 0 0) (show 2 ∣ 2 ^ 13 by norm_num); rw [hroot] at this; omega
    have hd0 : Ss.getD 0 0 / 2 % 2 ^ 5 = 0 := by
      have a := mod_div_mod (Ss.getD 0 0) 13 1 5 (by omega)
      rw [hroot] at a; simpa using a.symm
    have hp0 : Ss.getD 0 0 / 2 ^ 6 % 2 ^ 7 = 0 := by
      have a := mod_div_mod (Ss.getD 0 0) 13 6 7 (by omega)
      rw [hroot] at a; simpa using a.symm
    unfold StartOK
    rw [hd0, hp0, if_neg (by omega)]
    refine ⟨fun l => by simp [multR], fun l hl => by omega, fun l _ => by simp [multR], fun l hl => ?_⟩
    simp only [multR, Nat.zero_add, Nat.sub_zero]
    exact hxub l hl
  · -- not canonical: a group element makes the multiplicity vector larger
    push_neg at hcan
    obtain ⟨g, hg16, hlt⟩ := hcan
    have hG := h.grp g hg16
    obtain ⟨b', c', hd', hbc'⟩ := isDecomp_actF_nz hd hbc hG.glP hG.glQ
    have hav' : ∀ s, actF (GE g).1 (GE g).2 (av s) < 512 := fun s => actF_lt _ _ _
    have hR' : (univ.filter (fun s : Fin n => Em.testBit (actF (GE g).1 (GE g).2 (av s)) = false)).card = C.R := by
      rw [← hR]; apply congrArg Finset.card; apply Finset.filter_congr; intro s _; rw [hG.fixE _ (hav s)]
    have hx' : VR (xOf (fun s => actF (GE g).1 (GE g).2 (av s)) Em C.VT C.N) = VR (push (C.GP g) x) :=
      VR_congr _ _ (fun l hl => xOf_act hN h.cosets hG av hav l hl)
    have hbound : VR (push (C.GP g) x) < 2 ^ 16256 := by
      apply VR_lt; intro l hl
      have : push (C.GP g) x l ≤ ∑ j ∈ range 127, x j := by
        unfold push; apply Finset.sum_le_sum; intro j _; split
        · exact le_rfl
        · exact Nat.zero_le _
      have := h.R_le; omega
    have hVx : VR x < 2 ^ 16256 := VR_lt x hxb
    exact ih (2 ^ 16256 - VR (push (C.GP g) x)) (by omega) n _ b' c' hav' hd' hbc' hR' (by rw [hx'])

end B334.E1x.E1GS
