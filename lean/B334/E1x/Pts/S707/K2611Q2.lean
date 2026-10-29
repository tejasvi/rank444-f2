import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2611L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2611 of `S707`, parts 290 … 311, re-packed by predicted kernel memory (2.71 of 8.19 GB;
stage707_v5; the theorems are v3's `K2611C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2611_290 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2611.lits.getD i 0)) 290 5 = true := by
  decide +kernel
theorem kg_2611_290 : IPChk.allR (Pts.glueIB K2611.lits KW_2611) 290 5 = true := by decide +kernel
theorem kb_2611_295 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2611.lits.getD i 0)) 295 10 = true := by
  decide +kernel
theorem kg_2611_295 : IPChk.allR (Pts.glueIB K2611.lits KW_2611) 295 10 = true := by decide +kernel
theorem kb_2611_305 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2611.lits.getD i 0)) 305 3 = true := by
  decide +kernel
theorem kg_2611_305 : IPChk.allR (Pts.glueIB K2611.lits KW_2611) 305 3 = true := by decide +kernel
theorem kb_2611_308 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2611.lits.getD i 0)) 308 4 = true := by
  decide +kernel
theorem kg_2611_308 : IPChk.allR (Pts.glueIB K2611.lits KW_2611) 308 4 = true := by decide +kernel

end B334.E1x.Pts.S707
