import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5302L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5302 of `S707`, parts 0 … 30, re-packed by predicted kernel memory (2.11 of 8.19 GB;
stage707_v5; the theorems are v3's `K5302C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5302_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5302.lits.getD i 0)) 0 7 = true := by
  decide +kernel
theorem kg_5302_0 : IPChk.allR (Pts.glueIB K5302.lits KW_5302) 0 7 = true := by decide +kernel
theorem kb_5302_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5302.lits.getD i 0)) 7 19 = true := by
  decide +kernel
theorem kg_5302_7 : IPChk.allR (Pts.glueIB K5302.lits KW_5302) 7 19 = true := by decide +kernel
theorem kb_5302_26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5302.lits.getD i 0)) 26 5 = true := by
  decide +kernel
theorem kg_5302_26 : IPChk.allR (Pts.glueIB K5302.lits KW_5302) 26 5 = true := by decide +kernel

end B334.E1x.Pts.S707
