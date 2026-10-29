import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5816L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5816 of `S707`, parts 370 … 387, re-packed by predicted kernel memory (3.43 of 8.19 GB;
stage707_v5; the theorems are v3's `K5816C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5816_370 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5816.lits.getD i 0)) 370 5 = true := by
  decide +kernel
theorem kg_5816_370 : IPChk.allR (Pts.glueIB K5816.lits KW_5816) 370 5 = true := by decide +kernel
theorem kb_5816_375 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5816.lits.getD i 0)) 375 2 = true := by
  decide +kernel
theorem kg_5816_375 : IPChk.allR (Pts.glueIB K5816.lits KW_5816) 375 2 = true := by decide +kernel
theorem kb_5816_377 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5816.lits.getD i 0)) 377 6 = true := by
  decide +kernel
theorem kg_5816_377 : IPChk.allR (Pts.glueIB K5816.lits KW_5816) 377 6 = true := by decide +kernel
theorem kb_5816_383 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5816.lits.getD i 0)) 383 3 = true := by
  decide +kernel
theorem kg_5816_383 : IPChk.allR (Pts.glueIB K5816.lits KW_5816) 383 3 = true := by decide +kernel
theorem kb_5816_386 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5816.lits.getD i 0)) 386 2 = true := by
  decide +kernel
theorem kg_5816_386 : IPChk.allR (Pts.glueIB K5816.lits KW_5816) 386 2 = true := by decide +kernel

end B334.E1x.Pts.S707
