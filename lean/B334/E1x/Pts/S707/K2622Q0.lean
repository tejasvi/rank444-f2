import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2622L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2622 of `S707`, parts 0 … 75, re-packed by predicted kernel memory (6.19 of 8.19 GB;
stage707_v5; the theorems are v3's `K2622C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2622_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2622_0 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 0 2 = true := by decide +kernel
theorem kb_2622_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 2 8 = true := by
  decide +kernel
theorem kg_2622_2 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 2 8 = true := by decide +kernel
theorem kb_2622_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 10 22 = true := by
  decide +kernel
theorem kg_2622_10 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 10 22 = true := by decide +kernel
theorem kb_2622_32 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 32 1 = true := by
  decide +kernel
theorem kg_2622_32 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 32 1 = true := by decide +kernel
theorem kb_2622_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 33 3 = true := by
  decide +kernel
theorem kg_2622_33 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 33 3 = true := by decide +kernel
theorem kb_2622_36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 36 17 = true := by
  decide +kernel
theorem kg_2622_36 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 36 17 = true := by decide +kernel
theorem kb_2622_53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 53 9 = true := by
  decide +kernel
theorem kg_2622_53 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 53 9 = true := by decide +kernel
theorem kb_2622_62 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 62 13 = true := by
  decide +kernel
theorem kg_2622_62 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 62 13 = true := by decide +kernel
theorem kb_2622_75 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2622.lits.getD i 0)) 75 1 = true := by
  decide +kernel
theorem kg_2622_75 : IPChk.allR (Pts.glueIB K2622.lits KW_2622) 75 1 = true := by decide +kernel

end B334.E1x.Pts.S707
