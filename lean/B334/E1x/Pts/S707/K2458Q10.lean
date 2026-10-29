import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2458L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2458 of `S707`, parts 1052 … 1087, re-packed by predicted kernel memory (2.83 of 8.19 GB;
stage707_v5; the theorems are v3's `K2458C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2458_1052 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 1052 1 = true := by
  decide +kernel
theorem kg_2458_1052 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 1052 1 = true := by decide +kernel
theorem kb_2458_1053 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 1053 14 = true := by
  decide +kernel
theorem kg_2458_1053 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 1053 14 = true := by decide +kernel
theorem kb_2458_1067 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 1067 17 = true := by
  decide +kernel
theorem kg_2458_1067 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 1067 17 = true := by decide +kernel
theorem kb_2458_1084 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2458.lits.getD i 0)) 1084 4 = true := by
  decide +kernel
theorem kg_2458_1084 : IPChk.allR (Pts.glueIB K2458.lits KW_2458) 1084 4 = true := by decide +kernel

end B334.E1x.Pts.S707
