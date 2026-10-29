import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3080L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3080 of `S707`, parts 410 … 468, re-packed by predicted kernel memory (5.08 of 8.19 GB;
stage707_v5; the theorems are v3's `K3080C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3080_410 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3080.lits.getD i 0)) 410 14 = true := by
  decide +kernel
theorem kg_3080_410 : IPChk.allR (Pts.glueIB K3080.lits KW_3080) 410 14 = true := by decide +kernel
theorem kb_3080_424 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3080.lits.getD i 0)) 424 7 = true := by
  decide +kernel
theorem kg_3080_424 : IPChk.allR (Pts.glueIB K3080.lits KW_3080) 424 7 = true := by decide +kernel
theorem kb_3080_431 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3080.lits.getD i 0)) 431 16 = true := by
  decide +kernel
theorem kg_3080_431 : IPChk.allR (Pts.glueIB K3080.lits KW_3080) 431 16 = true := by decide +kernel
theorem kb_3080_447 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3080.lits.getD i 0)) 447 13 = true := by
  decide +kernel
theorem kg_3080_447 : IPChk.allR (Pts.glueIB K3080.lits KW_3080) 447 13 = true := by decide +kernel
theorem kb_3080_460 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3080.lits.getD i 0)) 460 1 = true := by
  decide +kernel
theorem kg_3080_460 : IPChk.allR (Pts.glueIB K3080.lits KW_3080) 460 1 = true := by decide +kernel
theorem kb_3080_461 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3080.lits.getD i 0)) 461 6 = true := by
  decide +kernel
theorem kg_3080_461 : IPChk.allR (Pts.glueIB K3080.lits KW_3080) 461 6 = true := by decide +kernel
theorem kb_3080_467 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3080.lits.getD i 0)) 467 2 = true := by
  decide +kernel
theorem kg_3080_467 : IPChk.allR (Pts.glueIB K3080.lits KW_3080) 467 2 = true := by decide +kernel

end B334.E1x.Pts.S707
