import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5867L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5867 of `S707`, parts 369 … 385, re-packed by predicted kernel memory (2.67 of 8.19 GB;
stage707_v5; the theorems are v3's `K5867C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5867_369 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5867.lits.getD i 0)) 369 3 = true := by
  decide +kernel
theorem kg_5867_369 : IPChk.allR (Pts.glueIB K5867.lits KW_5867) 369 3 = true := by decide +kernel
theorem kb_5867_372 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5867.lits.getD i 0)) 372 3 = true := by
  decide +kernel
theorem kg_5867_372 : IPChk.allR (Pts.glueIB K5867.lits KW_5867) 372 3 = true := by decide +kernel
theorem kb_5867_375 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5867.lits.getD i 0)) 375 7 = true := by
  decide +kernel
theorem kg_5867_375 : IPChk.allR (Pts.glueIB K5867.lits KW_5867) 375 7 = true := by decide +kernel
theorem kb_5867_382 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5867.lits.getD i 0)) 382 4 = true := by
  decide +kernel
theorem kg_5867_382 : IPChk.allR (Pts.glueIB K5867.lits KW_5867) 382 4 = true := by decide +kernel

end B334.E1x.Pts.S707
