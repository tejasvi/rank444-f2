import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K6303L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 6303 of `S707`, parts 397 … 414, re-packed by predicted kernel memory (3.38 of 8.19 GB;
stage707_v5; the theorems are v3's `K6303C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_6303_397 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6303.lits.getD i 0)) 397 1 = true := by
  decide +kernel
theorem kg_6303_397 : IPChk.allR (Pts.glueIB K6303.lits KW_6303) 397 1 = true := by decide +kernel
theorem kb_6303_398 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6303.lits.getD i 0)) 398 2 = true := by
  decide +kernel
theorem kg_6303_398 : IPChk.allR (Pts.glueIB K6303.lits KW_6303) 398 2 = true := by decide +kernel
theorem kb_6303_400 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6303.lits.getD i 0)) 400 5 = true := by
  decide +kernel
theorem kg_6303_400 : IPChk.allR (Pts.glueIB K6303.lits KW_6303) 400 5 = true := by decide +kernel
theorem kb_6303_405 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6303.lits.getD i 0)) 405 9 = true := by
  decide +kernel
theorem kg_6303_405 : IPChk.allR (Pts.glueIB K6303.lits KW_6303) 405 9 = true := by decide +kernel
theorem kb_6303_414 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K6303.lits.getD i 0)) 414 1 = true := by
  decide +kernel
theorem kg_6303_414 : IPChk.allR (Pts.glueIB K6303.lits KW_6303) 414 1 = true := by decide +kernel

end B334.E1x.Pts.S707
