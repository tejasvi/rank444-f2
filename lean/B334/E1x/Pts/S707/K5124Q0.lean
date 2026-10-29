import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5124L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5124 of `S707`, parts 0 … 50, re-packed by predicted kernel memory (2.61 of 8.19 GB;
stage707_v5; the theorems are v3's `K5124C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5124_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5124.lits.getD i 0)) 0 5 = true := by
  decide +kernel
theorem kg_5124_0 : IPChk.allR (Pts.glueIB K5124.lits KW_5124) 0 5 = true := by decide +kernel
theorem kb_5124_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5124.lits.getD i 0)) 5 12 = true := by
  decide +kernel
theorem kg_5124_5 : IPChk.allR (Pts.glueIB K5124.lits KW_5124) 5 12 = true := by decide +kernel
theorem kb_5124_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5124.lits.getD i 0)) 17 34 = true := by
  decide +kernel
theorem kg_5124_17 : IPChk.allR (Pts.glueIB K5124.lits KW_5124) 17 34 = true := by decide +kernel

end B334.E1x.Pts.S707
