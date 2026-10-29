import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6254L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6254 of `S707`, parts 0 … 1, re-packed by predicted kernel memory (1.05 of 8.19 GB;
stage707_v5; the theorems are v3's `K6254C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6254_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6254.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_6254_0 : IPChk.allR (Pts.glueIB K6254.lits KW_6254) 0 1 = true := by decide +kernel
theorem kb_6254_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6254.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_6254_1 : IPChk.allR (Pts.glueIB K6254.lits KW_6254) 1 1 = true := by decide +kernel

end B334.E1x.Pts.S707
