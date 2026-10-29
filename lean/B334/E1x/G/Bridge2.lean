import B334.E1x.G.Bridge1
import B334.BCP.Leaf
/-! # The leaf bridge: an E1 leaf refutes every decomposition with its multiset of cosets

Port of `E1G/Bridge2.lean` (⟨3,3,3⟩ release `rank333-f2`, Apache-2.0) to ⟨3,3,4⟩ and BranchCheck334.

`leaf_bridge_nd`: if the multiplicity vector of a decomposition (exactly `R` first factors outside `E`, nonzero second and
third factors) equals the prefix multiset of a leaf `pl`, and the leaf's tensor has no decomposition on the domain
(`B334.BCP.NoDecomp (termsOf R VT pl) R DOM`), we have a contradiction. On the domain `E^⊥` a functional sees only the
coset of a first factor (`par_coset`) and factors in `E` are invisible, so the `R` factors outside `E`, reordered like the
leaf's labels, decompose the leaf's tensor on its domain.

The leaf test of E1 is `Ctx.LF` on the prefix (`CheckG.lean`): `leafOK_bridge` takes `hLF : ∀ pl, C.LF pl = true →
NoDecomp (termsOf C.R C.VT pl) C.R C.DOM`, which `noDecomp_of_leafS` gives from a BranchCheck334 certificate accepted on
the leaf record `E1G.leafRec C.R C.VT C.DOM pl cert` (`B334.BCP.leafS_sound` and the record decoding lemmas). -/
set_option maxRecDepth 20000
namespace B334.E1x.E1GS
open Finset B334.Core Matrix
set_option exponentiation.threshold 600

/-! ## The leaf record -/

/-- the leaf's terms: representative `vt (label i)` at `9 i` -/
def termsOf (R VT pl : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun acc _ _ => acc)
    (fun _ ih acc i pl => ih (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight VT (Nat.mul 9 (E1G.rd 7 pl))) 511) (Nat.mul 9 i)))
      (Nat.succ i) (E1G.sk 7 pl)) R 0 0 pl

theorem leafRec_eq (R VT DOM pl cert : ℕ) : E1G.leafRec R VT DOM pl cert =
    Nat.lor R (Nat.lor (Nat.shiftLeft (termsOf R VT pl) 6) (Nat.shiftLeft (Nat.lor 1 (Nat.lor (Nat.shiftLeft DOM 2)
      (Nat.shiftLeft cert 514))) (Nat.add 6 (Nat.mul 9 R)))) := rfl

/-- label `i` of a packed prefix -/
def lab (pl i : ℕ) : ℕ := pl / 2 ^ (7 * i) % 128

theorem terms_gen (VT : ℕ) (R : ℕ) : ∀ acc i pl, acc < 2 ^ (9 * i) →
    (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun acc _ _ => acc)
      (fun _ ih acc i pl => ih (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight VT (Nat.mul 9 (E1G.rd 7 pl))) 511) (Nat.mul 9 i)))
        (Nat.succ i) (E1G.sk 7 pl)) R acc i pl) = acc + ∑ t ∈ range R, vt VT (lab pl t) * 2 ^ (9 * (i + t)) := by
  induction R with
  | zero => intro acc i pl _; simp
  | succ R ih =>
    intro acc i pl hacc
    have hv : Nat.land (Nat.shiftRight VT (Nat.mul 9 (E1G.rd 7 pl))) 511 = vt VT (lab pl 0) := by
      show (VT >>> (9 * E1G.rd 7 pl)) &&& (2 ^ 9 - 1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, rd_eq]; unfold vt lab; norm_num
    have hor : Nat.lor acc (Nat.shiftLeft (vt VT (lab pl 0)) (Nat.mul 9 i)) = acc + vt VT (lab pl 0) * 2 ^ (9 * i) := by
      show acc ||| vt VT (lab pl 0) <<< (9 * i) = _
      rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hacc, Nat.shiftLeft_eq]; ring
    show (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun acc _ _ => acc)
      (fun _ ih acc i pl => ih (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight VT (Nat.mul 9 (E1G.rd 7 pl))) 511) (Nat.mul 9 i)))
        (Nat.succ i) (E1G.sk 7 pl)) R (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight VT (Nat.mul 9 (E1G.rd 7 pl))) 511) (Nat.mul 9 i)))
        (Nat.succ i) (E1G.sk 7 pl)) = _
    have hlt : acc + vt VT (lab pl 0) * 2 ^ (9 * i) < 2 ^ (9 * (i + 1)) := by
      have h1 := vt_lt VT (lab pl 0)
      have : vt VT (lab pl 0) * 2 ^ (9 * i) ≤ 511 * 2 ^ (9 * i) := Nat.mul_le_mul_right _ (by omega)
      have h2 : 2 ^ (9 * (i + 1)) = 512 * 2 ^ (9 * i) := by rw [Nat.mul_succ, pow_add]; norm_num; ring
      omega
    rw [hv, hor, ih _ _ _ (by rw [Nat.succ_eq_add_one]; exact hlt), Finset.sum_range_succ']
    simp only [lab, sk_eq, Nat.div_div_eq_div_mul, ← pow_add]
    rw [show 7 * 0 = 0 from rfl, pow_zero, Nat.div_one, Nat.add_zero]
    have e : ∀ t, 7 + 7 * t = 7 * (t + 1) := fun t => by ring
    simp only [e, show ∀ t, i + 1 + t = i + (t + 1) from fun t => by ring]
    ring

theorem termsOf_eq (R VT pl : ℕ) : termsOf R VT pl = ∑ t ∈ range R, vt VT (lab pl t) * 2 ^ (9 * t) := by
  have := terms_gen VT R 0 0 pl (by norm_num)
  simpa using this

theorem termsOf_lt (R VT pl : ℕ) : termsOf R VT pl < 2 ^ (9 * R) := by
  rw [termsOf_eq, show ∑ t ∈ range R, vt VT (lab pl t) * 2 ^ (9 * t) = pk 9 (fun t => vt VT (lab pl t)) R from rfl]
  exact pk_lt 9 _ R (fun t _ => vt_lt VT _)

theorem aT_terms (R VT pl t : ℕ) (ht : t < R) : B334.BCP.aT (termsOf R VT pl) t = vt VT (lab pl t) := by
  show (termsOf R VT pl >>> (9 * t)) &&& (2 ^ 9 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, termsOf_eq,
    show ∑ t ∈ range R, vt VT (lab pl t) * 2 ^ (9 * t) = pk 9 (fun t => vt VT (lab pl t)) R from rfl]
  exact dig_pk 9 _ R (fun t _ => vt_lt VT _) t ht

theorem lor_add (a b k : ℕ) (ha : a < 2 ^ k) : a ||| b <<< k = a + 2 ^ k * b := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]; ring

theorem rd5_eq (k S : ℕ) : B334.BC.rd k S = S % 2 ^ k := by
  show Nat.land S (Nat.pred (Nat.shiftLeft 1 k)) = _
  rw [show Nat.shiftLeft 1 k = 2 ^ k from Nat.one_shiftLeft k, Nat.pred_eq_sub_one]
  exact Nat.and_two_pow_sub_one_eq_mod S k
theorem sk5_eq (k S : ℕ) : B334.BC.sk k S = S / 2 ^ k := Nat.shiftRight_eq_div_pow S k

theorem leafRec_val (R VT DOM pl cert : ℕ) (hR : R < 64) (hDOM : DOM < 2 ^ 512) :
    E1G.leafRec R VT DOM pl cert = R + 2 ^ 6 * (termsOf R VT pl + 2 ^ (9 * R) * (1 + 2 ^ 2 * (DOM + 2 ^ 512 * cert))) := by
  rw [leafRec_eq]
  show R ||| (termsOf R VT pl <<< 6 ||| (1 ||| (DOM <<< 2 ||| cert <<< 514)) <<< (6 + 9 * R)) = _
  have h1 : DOM <<< 2 ||| cert <<< 514 = (DOM + 2 ^ 512 * cert) <<< 2 := by
    rw [show (514 : ℕ) = 512 + 2 from rfl, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, lor_add _ _ _ hDOM]
  have h2 : 1 ||| (DOM + 2 ^ 512 * cert) <<< 2 = 1 + 2 ^ 2 * (DOM + 2 ^ 512 * cert) := lor_add _ _ _ (by norm_num)
  have h3 : termsOf R VT pl <<< 6 ||| (1 + 2 ^ 2 * (DOM + 2 ^ 512 * cert)) <<< (6 + 9 * R) =
      (termsOf R VT pl + 2 ^ (9 * R) * (1 + 2 ^ 2 * (DOM + 2 ^ 512 * cert))) <<< 6 := by
    rw [show 6 + 9 * R = 9 * R + 6 by ring, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, lor_add _ _ _ (termsOf_lt R VT pl)]
  rw [h1, h2, h3, lor_add _ _ _ (show R < 2 ^ 6 by omega)]

theorem leafN_rec (R VT DOM pl cert : ℕ) (hR : R < 64) (hDOM : DOM < 2 ^ 512) :
    B334.BCP.leafN (E1G.leafRec R VT DOM pl cert) = R := by
  show B334.BC.rd 6 _ = R
  rw [rd5_eq, leafRec_val R VT DOM pl cert hR hDOM, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem leafT_rec (R VT DOM pl cert : ℕ) (hR : R < 64) (hDOM : DOM < 2 ^ 512) :
    B334.BCP.leafT (E1G.leafRec R VT DOM pl cert) = termsOf R VT pl := by
  show B334.BC.rd (Nat.mul 9 (B334.BC.rd 6 _)) (B334.BC.sk 6 _) = _
  rw [show B334.BC.rd 6 (E1G.leafRec R VT DOM pl cert) = R from leafN_rec R VT DOM pl cert hR hDOM, rd5_eq, sk5_eq,
    leafRec_val R VT DOM pl cert hR hDOM, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), Nat.zero_add,
    show Nat.mul 9 R = 9 * R from rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (termsOf_lt R VT pl)]

theorem leafDom_rec (R VT DOM pl cert : ℕ) (hR : R < 64) (hDOM : DOM < 2 ^ 512) :
    B334.BCP.leafDom (E1G.leafRec R VT DOM pl cert) = DOM := by
  have hsk : B334.BC.sk (Nat.add 6 (Nat.mul 9 (B334.BC.rd 6 (E1G.leafRec R VT DOM pl cert)))) (E1G.leafRec R VT DOM pl cert) =
      1 + 2 ^ 2 * (DOM + 2 ^ 512 * cert) := by
    rw [show B334.BC.rd 6 (E1G.leafRec R VT DOM pl cert) = R from leafN_rec R VT DOM pl cert hR hDOM, sk5_eq,
      leafRec_val R VT DOM pl cert hR hDOM, show Nat.add 6 (Nat.mul 9 R) = 6 + 9 * R from rfl, pow_add,
      ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (show R < 2 ^ 6 by omega),
      Nat.zero_add, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (termsOf_lt R VT pl), Nat.zero_add]
  show B334.BC.rd 512 (B334.BC.sk 2 (B334.BC.sk (Nat.add 6 (Nat.mul 9 (B334.BC.rd 6 (E1G.leafRec R VT DOM pl cert))))
    (E1G.leafRec R VT DOM pl cert))) = DOM
  rw [hsk, rd5_eq, sk5_eq]
  have e2 : (1 + 2 ^ 2 * (DOM + 2 ^ 512 * cert)) / 2 ^ 2 = DOM + 2 ^ 512 * cert := by
    rw [Nat.add_mul_div_left _ _ (by norm_num)]; norm_num
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hDOM]

/-- a BranchCheck334 certificate accepted on the leaf record of `pl` refutes the leaf -/
theorem noDecomp_of_leafS (R VT DOM pl cert : ℕ) (hR : R < 64) (hDOM : DOM < 2 ^ 512)
    (h : B334.BC.leafS (E1G.leafRec R VT DOM pl cert) = true) : B334.BCP.NoDecomp (termsOf R VT pl) R DOM := by
  have := B334.BCP.leafS_sound _ h
  rwa [leafN_rec _ _ _ _ _ hR hDOM, leafT_rec _ _ _ _ _ hR hDOM, leafDom_rec _ _ _ _ _ hR hDOM] at this
/-! ## List helpers (as in S5.TmodE) -/

theorem perm_map_exists' {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ (cl : List β) (L : List α), (L.map f).Perm cl → ∃ L' : List α, L'.Perm L ∧ L'.map f = cl := by
  intro cl
  induction cl with
  | nil =>
    intro L h
    have : L.map f = [] := List.perm_nil.mp h
    rw [List.map_eq_nil_iff] at this
    exact ⟨[], by rw [this], rfl⟩
  | cons c cl ih =>
    intro L h
    have hc : c ∈ L.map f := h.symm.subset List.mem_cons_self
    obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hc
    have hp : L.Perm (x :: L.erase x) := List.perm_cons_erase hx
    have h2 : (c :: (L.erase x).map f).Perm (c :: cl) := by
      have := (hp.map f).symm.trans h
      simpa [hfx] using this
    obtain ⟨L1, hL1, hm⟩ := ih (L.erase x) h2.cons_inv
    exact ⟨x :: L1, (hL1.cons x).trans hp.symm, by simp [hm, hfx]⟩

theorem list_sum_range' {α M : Type*} [AddCommMonoid M] (d : α) (g : α → M) :
    ∀ L : List α, (L.map g).sum = ∑ t ∈ Finset.range L.length, g (L.getD t d) := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

theorem multR_count (d : ℕ) : ∀ pl l, multR d pl l = ((List.range d).map (lab pl)).count l := by
  induction d with
  | zero => intro pl l; simp [multR]
  | succ d ih =>
    intro pl l
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.count_cons, multR, ih (pl / 128) l]
    have e : (lab pl ∘ Nat.succ) = lab (pl / 128) := by
      funext i; simp only [Function.comp, lab, Nat.div_div_eq_div_mul]
      congr 2; rw [show 7 * i.succ = 7 * i + 7 by rw [Nat.mul_succ], pow_add]; norm_num; ring
    rw [e]
    simp only [lab, pow_zero, Nat.mul_zero, Nat.div_one, beq_iff_eq]
    omega

/-- **The leaf bridge** from the leaf's `NoDecomp` -/
theorem leaf_bridge_nd (VT N Em DOM R : ℕ) (hN : N ≤ 127) (hC : Cosets Em VT N) (hD : DomPerp DOM Em)
    {n : ℕ} (av : Fin n → ℕ) (b : Fin n → M34) (c : Fin n → M43) (hav : ∀ s, av s < 512)
    (hd0 : IsDecomp (fun s => toM3 (av s)) b c) (hbc : ∀ s, b s ≠ 0 ∧ c s ≠ 0)
    (hRn : (univ.filter (fun s : Fin n => Em.testBit (av s) = false)).card = R)
    (pl : ℕ) (hx : ∀ l, multR R pl l = xOf av Em VT N l)
    (hnd : B334.BCP.NoDecomp (termsOf R VT pl) R DOM) : False := by
  -- `B334.E1x.toM3` and `B334.BCP.toM3` have the same body
  have hd : IsDecomp (fun s => B334.BCP.toM3 (av s)) b c := hd0
  apply hnd
  classical
  -- the coset label of a factor outside `E`
  let cs : Fin n → ℕ := fun s => if h : ∃ l, l < N ∧ Em.testBit (av s ^^^ vt VT l) = true then Nat.find h else 0
  have hcs : ∀ s, Em.testBit (av s) = false → cs s < N ∧ Em.testBit (av s ^^^ vt VT (cs s)) = true := by
    intro s h0
    have hex : ∃ l, l < N ∧ Em.testBit (av s ^^^ vt VT l) = true := by
      obtain ⟨l, hl, hE⟩ := hC.cover (av s) (hav s) h0; exact ⟨l, hl, hE⟩
    have := Nat.find_spec hex
    simp only [cs, dif_pos hex]; exact this
  have hcs_eq : ∀ s l, Em.testBit (av s) = false → l < N → Em.testBit (av s ^^^ vt VT l) = true → cs s = l := by
    intro s l h0 hl hE
    obtain ⟨h1, h2⟩ := hcs s h0
    exact coset_unique hC (av s) (hav s) _ _ h1 hl h2 hE
  let Lout := (List.finRange n).filter (fun s => Em.testBit (av s) == false)
  have hLnd : Lout.Nodup := (List.nodup_finRange n).filter _
  have hmemL : ∀ s, s ∈ Lout ↔ Em.testBit (av s) = false := by
    intro s; simp [Lout, List.mem_filter, List.mem_finRange]
  have hcount : ∀ l, (Lout.map cs).count l = ((List.range R).map (lab pl)).count l := by
    intro l
    rw [← multR_count, hx l, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    unfold xOf
    split
    · next hl =>
      rw [← List.toFinset_card_of_nodup (hLnd.filter _)]
      apply congrArg Finset.card
      ext s
      simp only [List.mem_toFinset, List.mem_filter, hmemL, mem_filter, mem_univ, true_and, Function.comp, beq_iff_eq]
      constructor
      · rintro ⟨h0, hcl⟩; refine ⟨h0, ?_⟩; rw [← hcl]; exact (hcs s h0).2
      · rintro ⟨h0, hE⟩; exact ⟨h0, hcs_eq s l h0 hl hE⟩
    · next hl =>
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro s hs
      simp only [Function.comp, beq_iff_eq]
      intro hcl
      have := (hcs s ((hmemL s).mp hs)).1
      omega
  obtain ⟨L', hperm, hmap⟩ := perm_map_exists' cs _ Lout (List.perm_iff_count.mpr hcount)
  have hlen : L'.length = R := by
    have := congrArg List.length hmap; simpa using this
  have hmemL' : ∀ s ∈ L', Em.testBit (av s) = false := fun s hs => (hmemL s).mp (hperm.subset hs)
  -- a factor exists (the decomposition is not empty)
  have hn : 0 < n := by
    by_contra h0
    have h := hd 0 0 0 0 0 0
    have : n = 0 := by omega
    subst this
    simp at h
  let s0 : Fin n := ⟨0, hn⟩
  let bb : ℕ → ℕ := fun t => B334.BCP.natOf (vecB (b (L'.getD t s0)))
  let cc : ℕ → ℕ := fun t => B334.BCP.natOf (vecC (c (L'.getD t s0)))
  have hget : ∀ t < R, L'.getD t s0 ∈ L' := by
    intro t ht; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hlabt : ∀ t < R, cs (L'.getD t s0) = lab pl t := by
    intro t ht
    have h1 := congrArg (fun L => L[t]?) hmap
    simp only [List.getElem?_map, List.getElem?_range ht, Option.map_some] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [List.getElem?_eq_getElem (by omega)] at h1
    simpa using h1
  refine ⟨bb, cc, fun t ht => ?_, fun X hX hdom => ?_⟩
  · obtain ⟨h1, h2⟩ := hbc (L'.getD t s0)
    have p1 : 0 < B334.BCP.natOf (vecB (b (L'.getD t s0))) := by
      apply Nat.pos_of_ne_zero; intro e
      apply h1; apply B334.BCP.vecB_inj; rw [← B334.BCP.nv_natOf (vecB _), e]; funext i; simp [B334.BCP.nv, bitF]
    have p2 : 0 < B334.BCP.natOf (vecC (c (L'.getD t s0))) := by
      apply Nat.pos_of_ne_zero; intro e
      apply h2; apply B334.BCP.vecC_inj; rw [← B334.BCP.nv_natOf (vecC _), e]; funext i; simp [B334.BCP.nv, bitF]
    exact ⟨p1, B334.BCP.natOf_lt _, p2, B334.BCP.natOf_lt _⟩
  · rw [TX_eq_sum hd (B334.BCP.toM3 X)]
    let F : Fin n → Matrix (Fin 12) (Fin 12) F2 := fun s => vecMulVec (vecB (b s)) (vecC (c s))
    let G : Fin n → Matrix (Fin 12) (Fin 12) F2 := fun s => if B334.BC.par (av s &&& X) = true then F s else 0
    have e1 : ∑ s ∈ hitSet (fun s => B334.BCP.toM3 (av s)) (B334.BCP.toM3 X), F s = ∑ s : Fin n, G s := by
      rw [hitSet, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro s _
      simp only [G]
      rw [B334.BCP.pair_par X (av s) hX (hav s)]
      cases B334.BC.par (av s &&& X) <;> simp [bf]
    have e2 : ∑ s : Fin n, G s = (Lout.map G).sum := by
      rw [Fin.sum_univ_def]
      have : ∀ L : List (Fin n), (L.map G).sum = ((L.filter (fun s => Em.testBit (av s) == false)).map G).sum := by
        intro L
        induction L with
        | nil => rfl
        | cons x L ih =>
          rw [List.map_cons, List.sum_cons, ih]
          cases hx : Em.testBit (av x)
          · rw [List.filter_cons_of_pos (by simp [hx]), List.map_cons, List.sum_cons]
          · rw [List.filter_cons_of_neg (by simp [hx])]
            have : G x = 0 := by
              simp only [G]
              rw [hD X hX hdom (av x) (hav x) hx]; simp
            rw [this, zero_add]
      exact this _
    have e3 : (Lout.map G).sum = (L'.map G).sum := (hperm.map G).sum_eq.symm
    have e4 : (L'.map G).sum = ∑ t ∈ range R, G (L'.getD t s0) := by rw [list_sum_range' s0 G L', hlen]
    rw [e1, e2, e3, e4, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro t ht
    rw [Finset.mem_range] at ht
    have hpar : B334.BC.par (av (L'.getD t s0) &&& X) = B334.BC.par (B334.BCP.aT (termsOf R VT pl) t &&& X) := by
      rw [aT_terms R VT pl t ht, ← hlabt t ht]
      have h0 := hmemL' _ (hget t ht)
      exact par_coset hD X hX hdom _ _ (hav _) (vt_lt VT _) (hcs _ h0).2
    simp only [G, F]
    rw [hpar]
    split
    · simp only [bb, cc, B334.BCP.nv_natOf]
    · rfl

/-- membership in a list by a `List.rec` loop of `Nat.beq` tests (kernel-cheap; e.g. the run's leaf list as `C.LF`) -/
theorem extMem_spec (pl : ℕ) : ∀ L : List ℕ,
    (@List.rec ℕ (fun _ => Bool) false (fun e _ ih => @Bool.rec (fun _ => Bool) ih true (Nat.beq e pl)) L) = true → pl ∈ L := by
  intro L
  induction L with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons e L ih =>
    intro h
    have h' : @Bool.rec (fun _ => Bool) (@List.rec ℕ (fun _ => Bool) false
        (fun e _ ih => @Bool.rec (fun _ => Bool) ih true (Nat.beq e pl)) L) true (Nat.beq e pl) = true := h
    cases he : Nat.beq e pl
    · rw [he] at h'; exact List.mem_cons_of_mem _ (ih h')
    · rw [Nat.eq_of_beq_eq_true he]; exact List.mem_cons_self

/-- **The leaf bridge for `E1G.leafOK`**: every prefix the leaf test accepts has no decomposition on the domain (`hLF`;
from `noDecomp_of_leafS` per listed leaf) -/
theorem leafOK_bridge (C : E1G.Ctx) (Em : ℕ) (hN : C.N ≤ 127) (hC : Cosets Em C.VT C.N) (hD : DomPerp C.DOM Em)
    (hLF : ∀ pl, C.LF pl = true → B334.BCP.NoDecomp (termsOf C.R C.VT pl) C.R C.DOM)
    {n : ℕ} (av : Fin n → ℕ) (b : Fin n → M34) (c : Fin n → M43) (hav : ∀ s, av s < 512)
    (hd : IsDecomp (fun s => toM3 (av s)) b c) (hbc : ∀ s, b s ≠ 0 ∧ c s ≠ 0)
    (hRn : (univ.filter (fun s : Fin n => Em.testBit (av s) = false)).card = C.R)
    (pl : ℕ) (hx : ∀ l, multR C.R pl l = xOf av Em C.VT C.N l) (hleaf : E1G.leafOK C pl = true) : False :=
  leaf_bridge_nd C.VT C.N Em C.DOM C.R hN hC hD av b c hav hd hbc hRn pl hx (hLF pl hleaf)

/-- `hLF` from the leaf-list form: every prefix the leaf test accepts has a BranchCheck334
certificate `certOf pl` accepted on its leaf record -/
theorem hLF_of_leafS (C : E1G.Ctx) (hR : C.R < 64) (hDOM : C.DOM < 2 ^ 512) (certOf : ℕ → ℕ)
    (h : ∀ pl, C.LF pl = true → B334.BC.leafS (E1G.leafRec C.R C.VT C.DOM pl (certOf pl)) = true) :
    ∀ pl, C.LF pl = true → B334.BCP.NoDecomp (termsOf C.R C.VT pl) C.R C.DOM :=
  fun pl hpl => noDecomp_of_leafS C.R C.VT C.DOM pl (certOf pl) hR hDOM (h pl hpl)

end B334.E1x.E1GS
