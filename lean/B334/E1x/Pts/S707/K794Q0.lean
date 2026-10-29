import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K794L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 794 of `S707`, parts 0 … 33, re-packed by predicted kernel memory (5.17 of 8.19 GB;
stage707_v5; the theorems are v3's `K794C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_794_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K794.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_794_0 : IPChk.allR (Pts.glueIB K794.lits KW_794) 0 2 = true := by decide +kernel
theorem kb_794_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K794.lits.getD i 0)) 2 3 = true := by
  decide +kernel
theorem kg_794_2 : IPChk.allR (Pts.glueIB K794.lits KW_794) 2 3 = true := by decide +kernel
theorem kb_794_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K794.lits.getD i 0)) 5 3 = true := by
  decide +kernel
theorem kg_794_5 : IPChk.allR (Pts.glueIB K794.lits KW_794) 5 3 = true := by decide +kernel
theorem kb_794_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K794.lits.getD i 0)) 8 9 = true := by
  decide +kernel
theorem kg_794_8 : IPChk.allR (Pts.glueIB K794.lits KW_794) 8 9 = true := by decide +kernel
theorem kb_794_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K794.lits.getD i 0)) 17 9 = true := by
  decide +kernel
theorem kg_794_17 : IPChk.allR (Pts.glueIB K794.lits KW_794) 17 9 = true := by decide +kernel
theorem kb_794_26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K794.lits.getD i 0)) 26 7 = true := by
  decide +kernel
theorem kg_794_26 : IPChk.allR (Pts.glueIB K794.lits KW_794) 26 7 = true := by decide +kernel
theorem kb_794_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K794.lits.getD i 0)) 33 1 = true := by
  decide +kernel
theorem kg_794_33 : IPChk.allR (Pts.glueIB K794.lits KW_794) 33 1 = true := by decide +kernel

end B334.E1x.Pts.S707
