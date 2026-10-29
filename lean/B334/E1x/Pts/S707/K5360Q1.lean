import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5360L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5360 of `S707`, parts 131 … 169, re-packed by predicted kernel memory (3.65 of 8.19 GB;
stage707_v5; the theorems are v3's `K5360C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5360_131 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5360.lits.getD i 0)) 131 6 = true := by
  decide +kernel
theorem kg_5360_131 : IPChk.allR (Pts.glueIB K5360.lits KW_5360) 131 6 = true := by decide +kernel
theorem kb_5360_137 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5360.lits.getD i 0)) 137 21 = true := by
  decide +kernel
theorem kg_5360_137 : IPChk.allR (Pts.glueIB K5360.lits KW_5360) 137 21 = true := by decide +kernel
theorem kb_5360_158 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5360.lits.getD i 0)) 158 3 = true := by
  decide +kernel
theorem kg_5360_158 : IPChk.allR (Pts.glueIB K5360.lits KW_5360) 158 3 = true := by decide +kernel
theorem kb_5360_161 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5360.lits.getD i 0)) 161 3 = true := by
  decide +kernel
theorem kg_5360_161 : IPChk.allR (Pts.glueIB K5360.lits KW_5360) 161 3 = true := by decide +kernel
theorem kb_5360_164 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5360.lits.getD i 0)) 164 6 = true := by
  decide +kernel
theorem kg_5360_164 : IPChk.allR (Pts.glueIB K5360.lits KW_5360) 164 6 = true := by decide +kernel

end B334.E1x.Pts.S707
