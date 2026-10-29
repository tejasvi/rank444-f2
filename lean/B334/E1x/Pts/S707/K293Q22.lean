import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K293L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 293 of `S707`, parts 3169 … 3175, re-packed by predicted kernel memory (1.60 of 8.19 GB;
stage707_v5; the theorems are v3's `K293C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_293_3169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 3169 3 = true := by
  decide +kernel
theorem kg_293_3169 : IPChk.allR (Pts.glueIB K293.lits KW_293) 3169 3 = true := by decide +kernel
theorem kb_293_3172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K293.lits.getD i 0)) 3172 4 = true := by
  decide +kernel
theorem kg_293_3172 : IPChk.allR (Pts.glueIB K293.lits KW_293) 3172 4 = true := by decide +kernel

end B334.E1x.Pts.S707
