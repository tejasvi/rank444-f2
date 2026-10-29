import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K825L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 825 of `S707`, parts 0 … 11, re-packed by predicted kernel memory (4.28 of 8.19 GB;
stage707_v5; the theorems are v3's `K825C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_825_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K825.lits.getD i 0)) 0 3 = true := by
  decide +kernel
theorem kg_825_0 : IPChk.allR (Pts.glueIB K825.lits KW_825) 0 3 = true := by decide +kernel
theorem kb_825_3 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K825.lits.getD i 0)) 3 1 = true := by
  decide +kernel
theorem kg_825_3 : IPChk.allR (Pts.glueIB K825.lits KW_825) 3 1 = true := by decide +kernel
theorem kb_825_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K825.lits.getD i 0)) 4 4 = true := by
  decide +kernel
theorem kg_825_4 : IPChk.allR (Pts.glueIB K825.lits KW_825) 4 4 = true := by decide +kernel
theorem kb_825_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K825.lits.getD i 0)) 8 1 = true := by
  decide +kernel
theorem kg_825_8 : IPChk.allR (Pts.glueIB K825.lits KW_825) 8 1 = true := by decide +kernel
theorem kb_825_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K825.lits.getD i 0)) 9 2 = true := by
  decide +kernel
theorem kg_825_9 : IPChk.allR (Pts.glueIB K825.lits KW_825) 9 2 = true := by decide +kernel
theorem kb_825_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K825.lits.getD i 0)) 11 1 = true := by
  decide +kernel
theorem kg_825_11 : IPChk.allR (Pts.glueIB K825.lits KW_825) 11 1 = true := by decide +kernel

end B334.E1x.Pts.S707
