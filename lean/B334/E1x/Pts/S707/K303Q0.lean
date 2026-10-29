import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K303L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 303 of `S707`, parts 0 … 106, re-packed by predicted kernel memory (7.59 of 8.19 GB;
stage707_v5; the theorems are v3's `K303C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_303_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_303_0 : IPChk.allR (Pts.glueIB K303.lits KW_303) 0 3 = true := by decide +kernel
theorem kb_303_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 3 8 = true := by
  decide +kernel
theorem kg_303_3 : IPChk.allR (Pts.glueIB K303.lits KW_303) 3 8 = true := by decide +kernel
theorem kb_303_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 11 13 = true := by
  decide +kernel
theorem kg_303_11 : IPChk.allR (Pts.glueIB K303.lits KW_303) 11 13 = true := by decide +kernel
theorem kb_303_24 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 24 12 = true := by
  decide +kernel
theorem kg_303_24 : IPChk.allR (Pts.glueIB K303.lits KW_303) 24 12 = true := by decide +kernel
theorem kb_303_36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 36 6 = true := by
  decide +kernel
theorem kg_303_36 : IPChk.allR (Pts.glueIB K303.lits KW_303) 36 6 = true := by decide +kernel
theorem kb_303_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 42 29 = true := by
  decide +kernel
theorem kg_303_42 : IPChk.allR (Pts.glueIB K303.lits KW_303) 42 29 = true := by decide +kernel
theorem kb_303_71 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 71 2 = true := by
  decide +kernel
theorem kg_303_71 : IPChk.allR (Pts.glueIB K303.lits KW_303) 71 2 = true := by decide +kernel
theorem kb_303_73 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 73 6 = true := by
  decide +kernel
theorem kg_303_73 : IPChk.allR (Pts.glueIB K303.lits KW_303) 73 6 = true := by decide +kernel
theorem kb_303_79 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 79 2 = true := by
  decide +kernel
theorem kg_303_79 : IPChk.allR (Pts.glueIB K303.lits KW_303) 79 2 = true := by decide +kernel
theorem kb_303_81 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K303.lits.getD i 0)) 81 26 = true := by
  decide +kernel
theorem kg_303_81 : IPChk.allR (Pts.glueIB K303.lits KW_303) 81 26 = true := by decide +kernel

end B334.E1x.Pts.S707
