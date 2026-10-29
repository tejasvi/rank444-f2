import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4200L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4200 of `S707`, parts 0 … 24, re-packed by predicted kernel memory (6.20 of 8.19 GB;
stage707_v5; the theorems are v3's `K4200C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4200_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4200_0 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 0 2 = true := by decide +kernel
theorem kb_4200_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 2 1 = true := by
  decide +kernel
theorem kg_4200_2 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 2 1 = true := by decide +kernel
theorem kb_4200_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_4200_3 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 3 1 = true := by decide +kernel
theorem kb_4200_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 4 3 = true := by
  decide +kernel
theorem kg_4200_4 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 4 3 = true := by decide +kernel
theorem kb_4200_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 7 1 = true := by
  decide +kernel
theorem kg_4200_7 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 7 1 = true := by decide +kernel
theorem kb_4200_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 8 1 = true := by
  decide +kernel
theorem kg_4200_8 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 8 1 = true := by decide +kernel
theorem kb_4200_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 9 2 = true := by
  decide +kernel
theorem kg_4200_9 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 9 2 = true := by decide +kernel
theorem kb_4200_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 11 4 = true := by
  decide +kernel
theorem kg_4200_11 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 11 4 = true := by decide +kernel
theorem kb_4200_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4200.lits.getD i 0)) 15 10 = true := by
  decide +kernel
theorem kg_4200_15 : IPChk.allR (Pts.glueIB K4200.lits KW_4200) 15 10 = true := by decide +kernel

end B334.E1x.Pts.S707
