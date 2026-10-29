import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4544L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4544 of `S707`, parts 353 … 365, re-packed by predicted kernel memory (3.54 of 8.19 GB;
stage707_v5; the theorems are v3's `K4544C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4544_353 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4544.lits.getD i 0)) 353 1 = true := by
  decide +kernel
theorem kg_4544_353 : IPChk.allR (Pts.glueIB K4544.lits KW_4544) 353 1 = true := by decide +kernel
theorem kb_4544_354 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4544.lits.getD i 0)) 354 2 = true := by
  decide +kernel
theorem kg_4544_354 : IPChk.allR (Pts.glueIB K4544.lits KW_4544) 354 2 = true := by decide +kernel
theorem kb_4544_356 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4544.lits.getD i 0)) 356 4 = true := by
  decide +kernel
theorem kg_4544_356 : IPChk.allR (Pts.glueIB K4544.lits KW_4544) 356 4 = true := by decide +kernel
theorem kb_4544_360 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4544.lits.getD i 0)) 360 3 = true := by
  decide +kernel
theorem kg_4544_360 : IPChk.allR (Pts.glueIB K4544.lits KW_4544) 360 3 = true := by decide +kernel
theorem kb_4544_363 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4544.lits.getD i 0)) 363 3 = true := by
  decide +kernel
theorem kg_4544_363 : IPChk.allR (Pts.glueIB K4544.lits KW_4544) 363 3 = true := by decide +kernel

end B334.E1x.Pts.S707
