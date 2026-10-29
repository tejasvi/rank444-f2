import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K989L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 989 of `S707`, parts 341 … 394, re-packed by predicted kernel memory (5.69 of 8.19 GB;
stage707_v5; the theorems are v3's `K989C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_989_341 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 341 1 = true := by
  decide +kernel
theorem kg_989_341 : IPChk.allR (Pts.glueIB K989.lits KW_989) 341 1 = true := by decide +kernel
theorem kb_989_342 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 342 2 = true := by
  decide +kernel
theorem kg_989_342 : IPChk.allR (Pts.glueIB K989.lits KW_989) 342 2 = true := by decide +kernel
theorem kb_989_344 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 344 1 = true := by
  decide +kernel
theorem kg_989_344 : IPChk.allR (Pts.glueIB K989.lits KW_989) 344 1 = true := by decide +kernel
theorem kb_989_345 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 345 3 = true := by
  decide +kernel
theorem kg_989_345 : IPChk.allR (Pts.glueIB K989.lits KW_989) 345 3 = true := by decide +kernel
theorem kb_989_348 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 348 3 = true := by
  decide +kernel
theorem kg_989_348 : IPChk.allR (Pts.glueIB K989.lits KW_989) 348 3 = true := by decide +kernel
theorem kb_989_351 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 351 19 = true := by
  decide +kernel
theorem kg_989_351 : IPChk.allR (Pts.glueIB K989.lits KW_989) 351 19 = true := by decide +kernel
theorem kb_989_370 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 370 18 = true := by
  decide +kernel
theorem kg_989_370 : IPChk.allR (Pts.glueIB K989.lits KW_989) 370 18 = true := by decide +kernel
theorem kb_989_388 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K989.lits.getD i 0)) 388 7 = true := by
  decide +kernel
theorem kg_989_388 : IPChk.allR (Pts.glueIB K989.lits KW_989) 388 7 = true := by decide +kernel

end B334.E1x.Pts.S707
