import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1542L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1542 of `S707`, parts 115 … 297, re-packed by predicted kernel memory (4.45 of 8.19 GB;
stage707_v5; the theorems are v3's `K1542C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1542_115 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1542.lits.getD i 0)) 115 38 = true := by
  decide +kernel
theorem kg_1542_115 : IPChk.allR (Pts.glueIB K1542.lits KW_1542) 115 38 = true := by decide +kernel
theorem kb_1542_153 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1542.lits.getD i 0)) 153 13 = true := by
  decide +kernel
theorem kg_1542_153 : IPChk.allR (Pts.glueIB K1542.lits KW_1542) 153 13 = true := by decide +kernel
theorem kb_1542_166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1542.lits.getD i 0)) 166 38 = true := by
  decide +kernel
theorem kg_1542_166 : IPChk.allR (Pts.glueIB K1542.lits KW_1542) 166 38 = true := by decide +kernel
theorem kb_1542_204 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1542.lits.getD i 0)) 204 24 = true := by
  decide +kernel
theorem kg_1542_204 : IPChk.allR (Pts.glueIB K1542.lits KW_1542) 204 24 = true := by decide +kernel
theorem kb_1542_228 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1542.lits.getD i 0)) 228 36 = true := by
  decide +kernel
theorem kg_1542_228 : IPChk.allR (Pts.glueIB K1542.lits KW_1542) 228 36 = true := by decide +kernel
theorem kb_1542_264 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1542.lits.getD i 0)) 264 34 = true := by
  decide +kernel
theorem kg_1542_264 : IPChk.allR (Pts.glueIB K1542.lits KW_1542) 264 34 = true := by decide +kernel

end B334.E1x.Pts.S707
