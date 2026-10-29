import B334.BCP.Sym

/-! # The checker's pair-symmetry tables are the kernel-checked ones

BranchCheck334 (core Lean) carries its own copies of the orbit tables (`B334.BCT`, generated from the same source
table as `B334.Tab`). The literals are identical, so the kernel checks the equalities directly;
`sym_transform334` (stated with `B334.Tab`) then gives the masks the checker uses at a `sym` node. -/

namespace B334.BCP

theorem orbm_bind : B334.BCT.ORBM = B334.Tab.ORBM := by decide +kernel

theorem orbl_bind : B334.BCT.ORBL = B334.Tab.ORBL := by decide +kernel

theorem corbM_bind : ∀ o ∈ B334.Tab.ORBL, B334.BCT.corbM o = B334.Tab.CORB o := by decide +kernel

/-- **GL₄ pair step, checker form.** At the root, any decomposition can be moved so that the checker's `sym` masks hold for
the term branched first: `b_t ∈ ORBM` and `c_t ∈ corbM b_t`. -/
theorem sym_transform_bc {T n dom ACT : Nat} {b c : Nat → Nat} (hbc : BC n b c) (hd : HD T n dom b c ACT []) (t : Nat)
    (ht : t < n) : ∃ b' c' : Nat → Nat, BC n b' c' ∧ HD T n dom b' c' ACT [] ∧
      B334.BCT.ORBM.testBit (b' t) = true ∧ (B334.BCT.corbM (b' t)).testBit (c' t) = true := by
  obtain ⟨b', c', hbc', hd', ho, hc⟩ := sym_transform334 hbc hd t ht
  refine ⟨b', c', hbc', hd', ?_, ?_⟩
  · rw [orbm_bind]
    exact (B334.Tab.orbm_iff (b' t) (hbc' t ht).2.1).mpr ho
  · rw [corbM_bind _ ho]; exact hc

end B334.BCP
