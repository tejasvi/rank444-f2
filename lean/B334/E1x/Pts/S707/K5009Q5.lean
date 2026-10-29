import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5009L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5009 of `S707`, parts 348 … 395, re-packed by predicted kernel memory (5.15 of 8.19 GB;
stage707_v5; the theorems are v3's `K5009C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5009_348 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5009.lits.getD i 0)) 348 9 = true := by
  decide +kernel
theorem kg_5009_348 : IPChk.allR (Pts.glueIB K5009.lits KW_5009) 348 9 = true := by decide +kernel
theorem kb_5009_357 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5009.lits.getD i 0)) 357 5 = true := by
  decide +kernel
theorem kg_5009_357 : IPChk.allR (Pts.glueIB K5009.lits KW_5009) 357 5 = true := by decide +kernel
theorem kb_5009_362 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5009.lits.getD i 0)) 362 24 = true := by
  decide +kernel
theorem kg_5009_362 : IPChk.allR (Pts.glueIB K5009.lits KW_5009) 362 24 = true := by decide +kernel
theorem kb_5009_386 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5009.lits.getD i 0)) 386 2 = true := by
  decide +kernel
theorem kg_5009_386 : IPChk.allR (Pts.glueIB K5009.lits KW_5009) 386 2 = true := by decide +kernel
theorem kb_5009_388 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5009.lits.getD i 0)) 388 3 = true := by
  decide +kernel
theorem kg_5009_388 : IPChk.allR (Pts.glueIB K5009.lits KW_5009) 388 3 = true := by decide +kernel
theorem kb_5009_391 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5009.lits.getD i 0)) 391 3 = true := by
  decide +kernel
theorem kg_5009_391 : IPChk.allR (Pts.glueIB K5009.lits KW_5009) 391 3 = true := by decide +kernel
theorem kb_5009_394 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5009.lits.getD i 0)) 394 2 = true := by
  decide +kernel
theorem kg_5009_394 : IPChk.allR (Pts.glueIB K5009.lits KW_5009) 394 2 = true := by decide +kernel

end B334.E1x.Pts.S707
