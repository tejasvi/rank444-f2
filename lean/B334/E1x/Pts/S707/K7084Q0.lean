import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K7084L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 7084 of `S707`, parts 0 … 23, re-packed by predicted kernel memory (2.09 of 8.19 GB;
stage707_v5; the theorems are v3's `K7084C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_7084_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 0 15 = true := by
  decide +kernel
theorem kg_7084_0 : IPChk.allR (Pts.glueIB K7084.lits KW_7084) 0 15 = true := by decide +kernel
theorem kb_7084_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 15 8 = true := by
  decide +kernel
theorem kg_7084_15 : IPChk.allR (Pts.glueIB K7084.lits KW_7084) 15 8 = true := by decide +kernel
theorem kb_7084_23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K7084.lits.getD i 0)) 23 1 = true := by
  decide +kernel
theorem kg_7084_23 : IPChk.allR (Pts.glueIB K7084.lits KW_7084) 23 1 = true := by decide +kernel

end B334.E1x.Pts.S707
