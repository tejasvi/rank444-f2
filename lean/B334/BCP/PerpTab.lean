import B334.BC.BranchCheck334

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! # The perp tables of BranchCheck334 equal the doubling definitions

`B334.BC.nperp` and `B334.BC.perp` read two 64-entry tables (`B334.BCT.npl`, `pl`, `nph`); `nperpD` and `perpD` are the
doubling recursion. A kernel check over all `v < 4096` makes them equal, so every lemma proved for the doubling
definitions holds for the tables. -/

namespace B334.BCP
open B334.BC

theorem nperp_tab : (List.range 4096).all (fun v => Nat.beq (nperp v) (nperpD v)) = true := by decide +kernel
theorem perp_tab : (List.range 4096).all (fun v => Nat.beq (perp v) (perpD v)) = true := by decide +kernel

theorem nperp_eq : ∀ v < 4096, nperp v = nperpD v := fun v hv =>
  Nat.eq_of_beq_eq_true (List.all_eq_true.mp nperp_tab v (List.mem_range.mpr hv))

theorem perp_eq : ∀ v < 4096, perp v = perpD v := fun v hv =>
  Nat.eq_of_beq_eq_true (List.all_eq_true.mp perp_tab v (List.mem_range.mpr hv))

end B334.BCP
