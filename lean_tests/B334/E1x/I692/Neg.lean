import B334.E1x.I692.Fin

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Negative controls for the line-692 facts (test module, not part of the library)

Each mutant is rejected by the same check that accepts the real data (`decide +kernel`). -/

namespace B334.E1x.I692
open B334.E1x.E1GS

/-- slot 29083 (the whole space: cap 22, class 0 with bound 0) with its cap lowered by one -/
theorem neg_cap : RT.entryOK R ClsTab.CL (tab 29083 - 2 ^ 85) = false := by decide +kernel
/-- slot 0 with the zero matrix as `P` (not invertible) -/
theorem neg_P : RT.entryOK R ClsTab.CL (tab 0 - RT.eP (tab 0) * 2 ^ 100) = false := by decide +kernel
/-- slot 0 with a dual vector outside the domain (its first dual vector replaced by 0) -/
theorem neg_dual : SlotG.dualIn DOM (tab 0 - RT.eV (tab 0) (RT.eD (tab 0)) * 2 ^ (4 + 9 * RT.eD (tab 0))) = false := by
  decide +kernel
/-- group element 1 with the witness of element 0 (the identity) -/
theorem neg_ge : geltB Em VT N (GP 1) (GE 0).1 (GE 0).2 = false := by decide +kernel
/-- class 692 with its bound raised above the class data's bound (23 to 24) -/
theorem neg_lb : RT.classOK (ClsTab.CL + 2 ^ (96 * 692 + 4)) Tab2.basisOf Tab2.lbOf 692 = false := by decide +kernel
/-- class 100 against a wrong basis -/
theorem neg_span : RT.classOK ClsTab.CL (fun c => if c = 100 then [1] else Tab2.basisOf c) Tab2.lbOf 100 = false := by
  decide +kernel
/-- slot 0 checked as if the run were of a class of dimension 7 (class 4): its class is not above that -/
theorem neg_hi : Nat.blt (Tab2.basisOf 4).length (Tab2.basisOf (RT.eCls (tab 0))).length = false := by decide +kernel
/-- the converter's block mutants, replayed under the IP's own slots -/
theorem neg_g0 : E1G.block C sl UB UBR Rep692b.S_neg_g0 = false := by decide +kernel
theorem neg_yhalf : E1G.block C sl UB UBR Rep692b.S_neg_yhalf = false := by decide +kernel
theorem neg_cut2 : E1G.block C sl UB UBR Rep692b.S_neg_cut2 = false := by decide +kernel

end B334.E1x.I692
