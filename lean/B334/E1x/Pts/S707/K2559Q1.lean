import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2559L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2559 of `S707`, parts 178 … 248, re-packed by predicted kernel memory (3.04 of 8.19 GB;
stage707_v5; the theorems are v3's `K2559C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2559_178 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 178 13 = true := by
  decide +kernel
theorem kg_2559_178 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 178 13 = true := by decide +kernel
theorem kb_2559_191 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 191 24 = true := by
  decide +kernel
theorem kg_2559_191 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 191 24 = true := by decide +kernel
theorem kb_2559_215 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 215 30 = true := by
  decide +kernel
theorem kg_2559_215 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 215 30 = true := by decide +kernel
theorem kb_2559_245 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2559.lits.getD i 0)) 245 4 = true := by
  decide +kernel
theorem kg_2559_245 : IPChk.allR (Pts.glueIB K2559.lits KW_2559) 245 4 = true := by decide +kernel

end B334.E1x.Pts.S707
