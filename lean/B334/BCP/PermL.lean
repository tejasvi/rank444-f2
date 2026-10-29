import B334.BCP.Perm

/-! # From a T2 leaf record to an E1 leaf: the permutation as a list, checked by the kernel

An E1 leaf (packed first factors `T'` in the E1 order, `n` terms, dom mask `dom`) is covered by a T2 record `R` with
the same terms in another order. `permL p n`: `p` lists a permutation of `0, …, n-1` (length `n`, entries `< n`, no
repeats). `t2match R T' n dom p` checks `leafN R = n`, `leafDom R = dom`, `permL p n`, and term `s` of `T'` equals term
`p[s]` of `leafT R` for every `s < n`; all of it is decidable, so the kernel checks it per leaf. `noDecomp_of_t2`: with
`leafS R = true` (a T2 fact `ok_c`), the E1 leaf has no decomposition. -/

namespace B334.BCP

open B334.BC B334.Core

/-- `p` is a permutation of `0, …, n-1` -/
def permL (p : List Nat) (n : Nat) : Bool :=
  p.length == n && p.all (fun x => Nat.blt x n) && decide p.Nodup

theorem noDecomp_permL {T T' n dom : Nat} (p : List Nat) (hp : permL p n = true)
    (hσ : ∀ s, s < n → aT T' s = aT T (p.getD s 0)) (h : NoDecomp T n dom) : NoDecomp T' n dom := by
  simp only [permL, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq, decide_eq_true_eq] at hp
  obtain ⟨⟨hlen, hlt⟩, hnd⟩ := hp
  have hgd : ∀ i (hi : i < p.length), p.getD i 0 = p[i] := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hget : ∀ s : Fin n, p.getD s.val 0 < n := fun s => by
    have hs : s.val < p.length := hlen ▸ s.isLt
    rw [hgd _ hs]
    exact hlt _ (List.getElem_mem hs)
  let f : Fin n → Fin n := fun s => ⟨p.getD s.val 0, hget s⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : p.getD a.val 0 = p.getD b.val 0 := congrArg Fin.val hab
    have ha : a.val < p.length := hlen ▸ a.isLt
    have hb : b.val < p.length := hlen ▸ b.isLt
    rw [hgd _ ha, hgd _ hb] at h1
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)
  exact noDecomp_perm (Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)) (fun s => hσ s.val s.isLt) h

/-- the per-leaf check: T2 record `R` covers the E1 leaf `(T', n, dom)` through the permutation list `p` -/
def t2match (R T' n dom : Nat) (p : List Nat) : Bool :=
  leafN R == n && leafDom R == dom && permL p n &&
    (List.range n).all (fun s => aT T' s == aT (leafT R) (p.getD s 0))

/-- **The T2 → E1 leaf bridge.** -/
theorem noDecomp_of_t2 {R T' n dom : Nat} (p : List Nat) (hm : t2match R T' n dom p = true) (hR : leafS R = true) :
    NoDecomp T' n dom := by
  simp only [t2match, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hm
  obtain ⟨⟨⟨hn, hd⟩, hp⟩, hσ⟩ := hm
  have h := leafS_sound R hR
  rw [hn, hd] at h
  exact noDecomp_permL p hp (fun s hs => by simpa using hσ s hs) h

end B334.BCP
