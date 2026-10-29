import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K973L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 973 of `S707`, parts 1462 … 1473, re-packed by predicted kernel memory (0.68 of 8.19 GB;
stage707_v5; the theorems are v3's `K973C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_973_1462 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K973.lits.getD i 0)) 1462 12 = true := by
  decide +kernel
theorem kg_973_1462 : IPChk.allR (Pts.glueIB K973.lits KW_973) 1462 12 = true := by decide +kernel

end B334.E1x.Pts.S707
