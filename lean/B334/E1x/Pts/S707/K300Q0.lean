import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K300L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 300 of `S707`, parts 0 … 58, re-packed by predicted kernel memory (7.92 of 8.19 GB;
stage707_v5; the theorems are v3's `K300C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_300_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_300_0 : IPChk.allR (Pts.glueIB K300.lits KW_300) 0 3 = true := by decide +kernel
theorem kb_300_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 3 4 = true := by
  decide +kernel
theorem kg_300_3 : IPChk.allR (Pts.glueIB K300.lits KW_300) 3 4 = true := by decide +kernel
theorem kb_300_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 7 5 = true := by
  decide +kernel
theorem kg_300_7 : IPChk.allR (Pts.glueIB K300.lits KW_300) 7 5 = true := by decide +kernel
theorem kb_300_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 12 5 = true := by
  decide +kernel
theorem kg_300_12 : IPChk.allR (Pts.glueIB K300.lits KW_300) 12 5 = true := by decide +kernel
theorem kb_300_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 17 8 = true := by
  decide +kernel
theorem kg_300_17 : IPChk.allR (Pts.glueIB K300.lits KW_300) 17 8 = true := by decide +kernel
theorem kb_300_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 25 2 = true := by
  decide +kernel
theorem kg_300_25 : IPChk.allR (Pts.glueIB K300.lits KW_300) 25 2 = true := by decide +kernel
theorem kb_300_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 27 1 = true := by
  decide +kernel
theorem kg_300_27 : IPChk.allR (Pts.glueIB K300.lits KW_300) 27 1 = true := by decide +kernel
theorem kb_300_28 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 28 26 = true := by
  decide +kernel
theorem kg_300_28 : IPChk.allR (Pts.glueIB K300.lits KW_300) 28 26 = true := by decide +kernel
theorem kb_300_54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K300.lits.getD i 0)) 54 5 = true := by
  decide +kernel
theorem kg_300_54 : IPChk.allR (Pts.glueIB K300.lits KW_300) 54 5 = true := by decide +kernel

end B334.E1x.Pts.S707
