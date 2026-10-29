import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3121L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3121 of `S707`, parts 249 … 359, re-packed by predicted kernel memory (3.57 of 8.19 GB;
stage707_v5; the theorems are v3's `K3121C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3121_249 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3121.lits.getD i 0)) 249 8 = true := by
  decide +kernel
theorem kg_3121_249 : IPChk.allR (Pts.glueIB K3121.lits KW_3121) 249 8 = true := by decide +kernel
theorem kb_3121_257 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3121.lits.getD i 0)) 257 24 = true := by
  decide +kernel
theorem kg_3121_257 : IPChk.allR (Pts.glueIB K3121.lits KW_3121) 257 24 = true := by decide +kernel
theorem kb_3121_281 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3121.lits.getD i 0)) 281 26 = true := by
  decide +kernel
theorem kg_3121_281 : IPChk.allR (Pts.glueIB K3121.lits KW_3121) 281 26 = true := by decide +kernel
theorem kb_3121_307 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3121.lits.getD i 0)) 307 42 = true := by
  decide +kernel
theorem kg_3121_307 : IPChk.allR (Pts.glueIB K3121.lits KW_3121) 307 42 = true := by decide +kernel
theorem kb_3121_349 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3121.lits.getD i 0)) 349 11 = true := by
  decide +kernel
theorem kg_3121_349 : IPChk.allR (Pts.glueIB K3121.lits KW_3121) 349 11 = true := by decide +kernel

end B334.E1x.Pts.S707
