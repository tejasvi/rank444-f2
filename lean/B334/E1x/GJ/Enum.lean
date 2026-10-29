import B334.E1x.G.Compose

/-! # E1 for one coset IP from the canonical-point statement, E1G

E1G copy of `Pts/Enum.lean`: `E1GS.e1_sound_ext` (`G/Compose.lean`) with its chain argument replaced by a
hypothesis, the canonical-point statement `henum` (no `x` with the global facts, the slot facts and the label bounds,
and some positive entry). `E1GS.enum_of_chain_w` (`G/Hdr.lean`) gives `henum` from a top chain from the root glued to
search jobs, each with its `JobOK`. The orbit argument is that of `e1_sound_ext`, unchanged. -/

set_option maxRecDepth 20000
namespace B334.E1x.GJ
open Finset B334.Core Matrix B334.E1x.E1GS

/-- **E1 for one coset IP, from the canonical-point statement.** -/
theorem e1_sound_enum (C : E1G.Ctx) (Em LB LBR UB UBR Ntab nrows : ℕ) (sl tab : ℕ → ℕ) (GE : ℕ → ℕ × ℕ)
    (h : IPOK C Em LB LBR UB UBR Ntab nrows sl tab GE)
    (hrow : ∀ i < Ntab, Fact (RT.dualM (tab i)) (C.R - RT.eCap (tab i)))
    (hLF : ∀ pl, C.LF pl = true → B334.BCP.NoDecomp (termsOf C.R C.VT pl) C.R C.DOM)
    (henum : ∀ x : ℕ → ℕ, Glob C x → (∀ i < 2 ^ 15, SlotV x (sl i)) → (∀ l < 127, x l ≤ E1G.fld UB l) →
      (∃ l < 127, 0 < x l) → False) :
    E1Concl Em C.R := by
  have hN := h.N_le
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
  · have hslot : ∀ i < 2 ^ 15, SlotV x (sl i) := by
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
    exact henum x hglob hslot hxub hx0
  · push_neg at hcan
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

end B334.E1x.GJ
