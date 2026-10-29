import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K665L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 665 of `S707`, parts 152 … 210, re-packed by predicted kernel memory (3.21 of 8.19 GB;
stage707_v5; the theorems are v3's `K665C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_665_152 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K665.lits.getD i 0)) 152 24 = true := by
  decide +kernel
theorem kg_665_152 : IPChk.allR (Pts.glueIB K665.lits KW_665) 152 24 = true := by decide +kernel
theorem kb_665_176 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K665.lits.getD i 0)) 176 2 = true := by
  decide +kernel
theorem kg_665_176 : IPChk.allR (Pts.glueIB K665.lits KW_665) 176 2 = true := by decide +kernel
theorem kb_665_178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K665.lits.getD i 0)) 178 20 = true := by
  decide +kernel
theorem kg_665_178 : IPChk.allR (Pts.glueIB K665.lits KW_665) 178 20 = true := by decide +kernel
theorem kb_665_198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K665.lits.getD i 0)) 198 1 = true := by
  decide +kernel
theorem kg_665_198 : IPChk.allR (Pts.glueIB K665.lits KW_665) 198 1 = true := by decide +kernel
theorem kb_665_199 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K665.lits.getD i 0)) 199 12 = true := by
  decide +kernel
theorem kg_665_199 : IPChk.allR (Pts.glueIB K665.lits KW_665) 199 12 = true := by decide +kernel

end B334.E1x.Pts.S707
