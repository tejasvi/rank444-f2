import B334.Tables.SymTabWC

/-! # The pair-symmetry tables as existence statements (for the GL₄ pair step)

The kernel facts of `SymTabOrb` and `SymTabWC_<o>` say, entry by entry, that every listed `(S, S⁻¹)` is an inverse pair
with the orbit or stabilizer property. Here they become the statements the symmetry step uses:
- `wb_exists`: every nonzero 3×4 matrix `b` is moved by some invertible `S` into `ORBM`;
- `wc_exists`: for each `o ∈ ORBL`, every nonzero 4×3 matrix `c` is moved by some `S` with `o S = o` into `CORB o`.
Both give `Si * S = 1` as matrices, the hypothesis of `sym_sum334`. -/

namespace B334.Tab
open B334.Core

theorem orbm_iff (v : Nat) (hv : v < 4096) : ORBM.testBit v = true ↔ v ∈ ORBL := by
  have h := allLT_spec orbm_fact v hv
  rw [beq_iff_eq] at h
  rw [h, List.contains_iff_mem]

/-- **Witness table `WB`.** Every nonzero `b` has an inverse pair `(S, Si)` with `b S ∈ ORBM`. -/
theorem wb_exists (b : Nat) (hb : b < 4096) (h0 : b ≠ 0) :
    ∃ S Si : Nat, toM44 Si * toM44 S = 1 ∧ mulBS b S ∈ ORBL := by
  have h := allLT_spec wb_fact b hb
  simp only [wbOK, Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true] at h
  obtain ⟨hinv, horb⟩ := h
  refine ⟨pS WB b, pSi WB b, inv_of_mul44 hinv, ?_⟩
  exact (orbm_iff _ (lt_of_lt_of_eq (mkB_lt _ 12) (by norm_num))).mp horb

/-- one orbit minimum's `WC` fact, unpacked -/
theorem wc_unpack {o W C : Nat} (hf : wcOK o W C = true) (c : Nat) (hc : c < 4096) (h0 : c ≠ 0) :
    ∃ S Si : Nat, toM44 Si * toM44 S = 1 ∧ mulBS o S = o ∧ C.testBit (mulSC Si c) = true := by
  have h := allLT_spec hf c hc
  simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true] at h
  obtain ⟨⟨hinv, hfix⟩, hcorb⟩ := h
  exact ⟨pS W c, pSi W c, inv_of_mul44 hinv, hfix, hcorb⟩

/-- **Witness tables `WC`.** For each `o ∈ ORBL`, every nonzero `c` has an inverse pair `(S, Si)` with `o S = o` and
`Si c ∈ CORB o`. -/
theorem wc_exists (o : Nat) (ho : o ∈ ORBL) (c : Nat) (hc : c < 4096) (h0 : c ≠ 0) :
    ∃ S Si : Nat, toM44 Si * toM44 S = 1 ∧ mulBS o S = o ∧ (CORB o).testBit (mulSC Si c) = true := by
  simp only [ORBL, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wc_unpack wc_fact_1 c hc h0
  · exact wc_unpack wc_fact_16 c hc h0
  · exact wc_unpack wc_fact_17 c hc h0
  · exact wc_unpack wc_fact_18 c hc h0
  · exact wc_unpack wc_fact_256 c hc h0
  · exact wc_unpack wc_fact_257 c hc h0
  · exact wc_unpack wc_fact_258 c hc h0
  · exact wc_unpack wc_fact_272 c hc h0
  · exact wc_unpack wc_fact_273 c hc h0
  · exact wc_unpack wc_fact_274 c hc h0
  · exact wc_unpack wc_fact_288 c hc h0
  · exact wc_unpack wc_fact_289 c hc h0
  · exact wc_unpack wc_fact_290 c hc h0
  · exact wc_unpack wc_fact_291 c hc h0
  · exact wc_unpack wc_fact_292 c hc h0

end B334.Tab
