import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1080L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1080 of `S707`, parts 0 … 39, re-packed by predicted kernel memory (4.82 of 8.19 GB;
stage707_v5; the theorems are v3's `K1080C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1080_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_1080_0 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 0 2 = true := by decide +kernel
theorem kb_1080_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_1080_2 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 2 6 = true := by decide +kernel
theorem kb_1080_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 8 12 = true := by
  decide +kernel
theorem kg_1080_8 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 8 12 = true := by decide +kernel
theorem kb_1080_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 20 5 = true := by
  decide +kernel
theorem kg_1080_20 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 20 5 = true := by decide +kernel
theorem kb_1080_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 25 6 = true := by
  decide +kernel
theorem kg_1080_25 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 25 6 = true := by decide +kernel
theorem kb_1080_31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1080.lits.getD i 0)) 31 9 = true := by
  decide +kernel
theorem kg_1080_31 : IPChk.allR (Pts.glueIB K1080.lits KW_1080) 31 9 = true := by decide +kernel

end B334.E1x.Pts.S707
