import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K314L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 314 of `S707`, parts 152 … 166, re-packed by predicted kernel memory (5.06 of 8.19 GB;
stage707_v5; the theorems are v3's `K314C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_314_152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 152 3 = true := by
  decide +kernel
theorem kg_314_152 : IPChk.allR (Pts.glueIB K314.lits KW_314) 152 3 = true := by decide +kernel
theorem kb_314_155 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 155 2 = true := by
  decide +kernel
theorem kg_314_155 : IPChk.allR (Pts.glueIB K314.lits KW_314) 155 2 = true := by decide +kernel
theorem kb_314_157 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 157 2 = true := by
  decide +kernel
theorem kg_314_157 : IPChk.allR (Pts.glueIB K314.lits KW_314) 157 2 = true := by decide +kernel
theorem kb_314_159 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 159 1 = true := by
  decide +kernel
theorem kg_314_159 : IPChk.allR (Pts.glueIB K314.lits KW_314) 159 1 = true := by decide +kernel
theorem kb_314_160 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 160 5 = true := by
  decide +kernel
theorem kg_314_160 : IPChk.allR (Pts.glueIB K314.lits KW_314) 160 5 = true := by decide +kernel
theorem kb_314_165 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 165 1 = true := by
  decide +kernel
theorem kg_314_165 : IPChk.allR (Pts.glueIB K314.lits KW_314) 165 1 = true := by decide +kernel
theorem kb_314_166 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K314.lits.getD i 0)) 166 1 = true := by
  decide +kernel
theorem kg_314_166 : IPChk.allR (Pts.glueIB K314.lits KW_314) 166 1 = true := by decide +kernel

end B334.E1x.Pts.S707
