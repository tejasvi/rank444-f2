import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5950L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5950 of `S707`, parts 0 … 94, re-packed by predicted kernel memory (5.61 of 8.19 GB;
stage707_v5; the theorems are v3's `K5950C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5950_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5950.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_5950_0 : IPChk.allR (Pts.glueIB K5950.lits KW_5950) 0 1 = true := by decide +kernel
theorem kb_5950_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5950.lits.getD i 0)) 1 2 = true := by
  decide +kernel
theorem kg_5950_1 : IPChk.allR (Pts.glueIB K5950.lits KW_5950) 1 2 = true := by decide +kernel
theorem kb_5950_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5950.lits.getD i 0)) 3 24 = true := by
  decide +kernel
theorem kg_5950_3 : IPChk.allR (Pts.glueIB K5950.lits KW_5950) 3 24 = true := by decide +kernel
theorem kb_5950_27 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5950.lits.getD i 0)) 27 17 = true := by
  decide +kernel
theorem kg_5950_27 : IPChk.allR (Pts.glueIB K5950.lits KW_5950) 27 17 = true := by decide +kernel
theorem kb_5950_44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5950.lits.getD i 0)) 44 22 = true := by
  decide +kernel
theorem kg_5950_44 : IPChk.allR (Pts.glueIB K5950.lits KW_5950) 44 22 = true := by decide +kernel
theorem kb_5950_66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5950.lits.getD i 0)) 66 19 = true := by
  decide +kernel
theorem kg_5950_66 : IPChk.allR (Pts.glueIB K5950.lits KW_5950) 66 19 = true := by decide +kernel
theorem kb_5950_85 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5950.lits.getD i 0)) 85 10 = true := by
  decide +kernel
theorem kg_5950_85 : IPChk.allR (Pts.glueIB K5950.lits KW_5950) 85 10 = true := by decide +kernel

end B334.E1x.Pts.S707
