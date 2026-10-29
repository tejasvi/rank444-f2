import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1038L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1038 of `S707`, parts 0 … 83, re-packed by predicted kernel memory (4.84 of 8.19 GB;
stage707_v5; the theorems are v3's `K1038C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1038_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 0 11 = true := by
  decide +kernel
theorem kg_1038_0 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 0 11 = true := by decide +kernel
theorem kb_1038_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 11 1 = true := by
  decide +kernel
theorem kg_1038_11 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 11 1 = true := by decide +kernel
theorem kb_1038_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 12 21 = true := by
  decide +kernel
theorem kg_1038_12 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 12 21 = true := by decide +kernel
theorem kb_1038_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 33 16 = true := by
  decide +kernel
theorem kg_1038_33 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 33 16 = true := by decide +kernel
theorem kb_1038_49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 49 5 = true := by
  decide +kernel
theorem kg_1038_49 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 49 5 = true := by decide +kernel
theorem kb_1038_54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 54 27 = true := by
  decide +kernel
theorem kg_1038_54 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 54 27 = true := by decide +kernel
theorem kb_1038_81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1038.lits.getD i 0)) 81 3 = true := by
  decide +kernel
theorem kg_1038_81 : IPChk.allR (Pts.glueIB K1038.lits KW_1038) 81 3 = true := by decide +kernel

end B334.E1x.Pts.S707
