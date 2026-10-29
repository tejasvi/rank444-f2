import B334.Bind.Transport
import B334.MethodK.Cert

/-! # Table binding helpers: images of spans, masks of vectors, unique cosets (row 44)

* `map_spanMasks_eq`: `g(spanMasks B) = spanMasks B'` from mask data — every `g(b)` (as a listed mask) lies in
  `spanMasks B'` and every `g⁻¹(b')` lies in `spanMasks B`;
* `exists_mask`: every vector of `F₂⁹` is `vecOfMask 9 m` for some `m < 2 ^ 9`;
* `existsUnique_of_masks`: the "exactly one coset space contains v" condition from a finite check on masks (brute force
  over subsets; too heavy for the kernel on 512 masks × 7 spaces);
* `existsUnique_of_certs`: the same condition from per-mask certificates, the form row 44 uses: for a mask in a space, the
  subset of its generators with that XOR; for a mask outside a space, a dual vector vanishing on the generators and not on
  the mask (`dual_notMem`); `chkAll` checks a certificate list in one walk. -/

namespace B334.Bind

open Finset

/-- a 3×3 matrix from a 9-bit mask (entry `(i, j)` at bit `3i + j`, as `mat3`) -/
def mat3m (m : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => if m.testBit (3 * i.val + j.val) then 1 else 0

theorem map_spanMasks_eq (P Q Pi Qi : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hP : P * Pi = 1) (hQ : Q * Qi = 1)
    (B B' img invimg : List ℕ)
    (himg : ∀ j < B.length, actA P Q (vecOfMask (3 * 3) (B.getD j 0)) = vecOfMask (3 * 3) (img.getD j 0))
    (h1 : ∀ j < B.length, vecOfMask (3 * 3) (img.getD j 0) ∈ spanMasks B')
    (hinv : ∀ j < B'.length, actA Pi Qi (vecOfMask (3 * 3) (B'.getD j 0)) = vecOfMask (3 * 3) (invimg.getD j 0))
    (h2 : ∀ j < B'.length, vecOfMask (3 * 3) (invimg.getD j 0) ∈ spanMasks B) :
    (spanMasks B).map (actAL P Q) = spanMasks B' := by
  have hQ' : Qi * Q = 1 := mul_eq_one_comm.mp hQ
  apply le_antisymm
  · unfold spanMasks
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨w, ⟨m, hm, rfl⟩, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    have := himg j hj
    rw [List.getD_eq_getElem _ _ hj] at this
    rw [actAL_apply, this]
    exact h1 j hj
  · unfold spanMasks
    rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    refine Submodule.mem_map.mpr ⟨actA Pi Qi (vecOfMask (3 * 3) (B'[j])), ?_, ?_⟩
    · have := hinv j hj
      rw [List.getD_eq_getElem _ _ hj] at this
      rw [this]; exact h2 j hj
    · rw [actAL_apply, actA_actA, hP, hQ', actA_one]

/-- every vector of F₂⁹ is a mask (`vecOfMask` is `mvec`, and `maskOf` inverts it) -/
theorem exists_mask (v : Fin (3 * 3) → ZMod 2) : ∃ m < 2 ^ 9, vecOfMask (3 * 3) m = v := by
  refine ⟨B334.MethodK.maskOf v, B334.MethodK.maskOf_lt v, ?_⟩
  have h : vecOfMask (3 * 3) (B334.MethodK.maskOf v) = B334.MethodK.mvec (3 * 3) (B334.MethodK.maskOf v) := by
    funext p; rfl
  rw [h, B334.MethodK.mvec_maskOf]

/-- "exactly one `C i` contains v" for every v outside `spanMasks B`, from a finite check on masks -/
theorem existsUnique_of_masks {N : ℕ} (B : List ℕ) (C : Fin N → List ℕ) (hB : ∀ b ∈ B, b < 2 ^ 9)
    (hC : ∀ i, ∀ b ∈ C i, b < 2 ^ 9)
    (h : ∀ m < 2 ^ 9, inSpan B m = false → (Finset.univ.filter (fun i => inSpan (C i) m = true)).card = 1) :
    ∀ v, v ∉ spanMasks B → ∃! i, v ∈ spanMasks (C i) := by
  intro v hv
  obtain ⟨m, hm, rfl⟩ := exists_mask v
  have hB' : inSpan B m = false := by
    cases e : inSpan B m
    · rfl
    · exact absurd ((mem_spanMasks_iff B hB m hm).mpr e) hv
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (h m hm hB')
  refine ⟨i, ?_, ?_⟩
  · have : i ∈ Finset.univ.filter (fun i => inSpan (C i) m = true) := by rw [hi]; exact Finset.mem_singleton_self i
    exact (mem_spanMasks_iff (C i) (hC i) m hm).mpr (Finset.mem_filter.mp this).2
  · intro j hj
    have : j ∈ Finset.univ.filter (fun i => inSpan (C i) m = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_spanMasks_iff (C j) (hC j) m hm).mp hj⟩
    rw [hi] at this
    exact Finset.mem_singleton.mp this

end B334.Bind

namespace B334.Bind

/-- parity of `y &&& x` over the 9 low bits (the dot product of the two masks) -/
def parAnd (y x : ℕ) : Bool := B334.MethodK.xorFold (3 * 3) (fun j => (y &&& x).testBit j)

/-- a dual vector `y` that vanishes on `B` and not on `m` shows `m ∉ span B` -/
theorem dual_notMem (B : List ℕ) (y m : ℕ) (hB : ∀ b ∈ B, parAnd y b = false) (hm : parAnd y m = true) :
    vecOfMask (3 * 3) m ∉ spanMasks B := by
  intro hmem
  have key : ∀ v ∈ spanMasks B, B334.MethodK.mvec (3 * 3) y ⬝ᵥ v = 0 := by
    intro v hv
    unfold spanMasks at hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, hb, rfl⟩ := hw
      show B334.MethodK.mvec (3 * 3) y ⬝ᵥ B334.MethodK.mvec (3 * 3) b = 0
      rw [B334.MethodK.dot_mvec]
      have h := hB b hb
      unfold parAnd at h
      rw [h]; rfl
    | zero => simp
    | add x z _ _ hx hz => rw [dotProduct_add, hx, hz, add_zero]
    | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
  have h0 := key _ hmem
  have h1 : B334.MethodK.mvec (3 * 3) y ⬝ᵥ vecOfMask (3 * 3) m = 1 := by
    show B334.MethodK.mvec (3 * 3) y ⬝ᵥ B334.MethodK.mvec (3 * 3) m = 1
    rw [B334.MethodK.dot_mvec]
    unfold parAnd at hm
    rw [hm]; rfl
  rw [h0] at h1
  exact zero_ne_one h1

/-- `y` is a dual witness for `m ∉ span B` -/
def dualOK (y m : ℕ) (B : List ℕ) : Bool := B.all (fun b => !(parAnd y b)) && parAnd y m

theorem dualOK_spec {y m : ℕ} {B : List ℕ} (h : dualOK y m B = true) :
    (∀ b ∈ B, parAnd y b = false) ∧ parAnd y m = true := by
  unfold dualOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun b hb => ?_, h.2⟩
  have hb' := h.1 b hb
  revert hb'
  cases parAnd y b <;> simp

/-- the per-mask certificate check: kind 0 = `m ∈ span basis` (a subset), kind 1 = `m` lies in `Cl i0` (a subset)
and in no other `Cl j` (a dual witness for each `j ≠ i0`) -/
def chkC (basis : List ℕ) (Cl : ℕ → List ℕ) (N : ℕ) (c : ℕ × ℕ × ℕ × List ℕ) (m : ℕ) : Bool :=
  if c.1 = 0 then xorSub basis c.2.2.1 == m
  else decide (c.2.1 < N) && (xorSub (Cl c.2.1) c.2.2.1 == m) &&
    (List.range N).all (fun j => j == c.2.1 || dualOK (c.2.2.2.getD j 0) m (Cl j))

theorem existsUnique_of_certs (basis : List ℕ) (Cl : ℕ → List ℕ) (N : ℕ) (cert : ℕ → ℕ × ℕ × ℕ × List ℕ)
    (h : ∀ m < 2 ^ 9, chkC basis Cl N (cert m) m = true) :
    ∀ v, v ∉ spanMasks basis → ∃! i : Fin N, v ∈ spanMasks (Cl i.val) := by
  intro v hv
  obtain ⟨m, hm, rfl⟩ := exists_mask v
  have hc := h m hm
  unfold chkC at hc
  by_cases hk : (cert m).1 = 0
  · rw [if_pos hk, beq_iff_eq] at hc
    have h1 := xorSub_mem basis (cert m).2.2.1
    rw [hc] at h1
    exact absurd h1 hv
  · rw [if_neg hk, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hc
    obtain ⟨⟨hlt, hsub⟩, hall⟩ := hc
    refine ⟨⟨(cert m).2.1, hlt⟩, ?_, ?_⟩
    · show vecOfMask (3 * 3) m ∈ spanMasks (Cl (cert m).2.1)
      have h1 := xorSub_mem (Cl (cert m).2.1) (cert m).2.2.1
      rw [hsub] at h1
      exact h1
    · intro j hj
      apply Fin.ext
      by_contra hne
      have hj' := hall j.val (List.mem_range.mpr j.isLt)
      rw [Bool.or_eq_true] at hj'
      rcases hj' with he | hd
      · exact hne (beq_iff_eq.mp he)
      · have hd' := dualOK_spec hd
        exact dual_notMem (Cl j.val) _ m hd'.1 hd'.2 hj

/-- `f` holds at every entry of `l`, the `i`-th entry with the index `i + k` (one walk over the list, by the recursor:
kernel-friendly for long certificate lists) -/
def chkAll {α : Type} (f : α → ℕ → Bool) (l : List α) : ℕ → Bool :=
  @List.rec α (fun _ => ℕ → Bool) (fun _ => true) (fun c _ ih k => f c k && ih (k + 1)) l

theorem chkAll_spec {α : Type} (f : α → ℕ → Bool) (d : α) :
    ∀ (l : List α) (k : ℕ), chkAll f l k = true → ∀ i < l.length, f (l.getD i d) (i + k) = true := by
  intro l
  induction l with
  | nil => intro k _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons c cs ih =>
    intro k h i hi
    change (f c k && chkAll f cs (k + 1)) = true at h
    rw [Bool.and_eq_true] at h
    cases i with
    | zero => rw [List.getD_cons_zero, Nat.zero_add]; exact h.1
    | succ i =>
      rw [List.getD_cons_succ, show i + 1 + k = i + (k + 1) by omega]
      exact ih (k + 1) h.2 i (by simpa using hi)

end B334.Bind
