import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1462L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1462 of `S707`, parts 610 … 626, re-packed by predicted kernel memory (0.24 of 8.19 GB;
stage707_v5; the theorems are v3's `K1462C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1462_610 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1462.lits.getD i 0)) 610 17 = true := by
  decide +kernel
theorem kg_1462_610 : IPChk.allR (Pts.glueIB K1462.lits KW_1462) 610 17 = true := by decide +kernel

end B334.E1x.Pts.S707
