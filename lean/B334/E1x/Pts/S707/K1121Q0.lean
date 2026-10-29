import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1121L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1121 of `S707`, parts 0 … 44, re-packed by predicted kernel memory (2.81 of 8.19 GB;
stage707_v5; the theorems are v3's `K1121C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1121_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_1121_0 : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 0 9 = true := by decide +kernel
theorem kb_1121_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 9 2 = true := by
  decide +kernel
theorem kg_1121_9 : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 9 2 = true := by decide +kernel
theorem kb_1121_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 11 14 = true := by
  decide +kernel
theorem kg_1121_11 : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 11 14 = true := by decide +kernel
theorem kb_1121_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1121.lits.getD i 0)) 25 20 = true := by
  decide +kernel
theorem kg_1121_25 : IPChk.allR (Pts.glueIB K1121.lits KW_1121) 25 20 = true := by decide +kernel

end B334.E1x.Pts.S707
