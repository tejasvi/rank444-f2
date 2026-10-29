import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5230L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5230 of `S707`, parts 0 … 28, re-packed by predicted kernel memory (1.38 of 8.19 GB;
stage707_v5; the theorems are v3's `K5230C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5230_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5230.lits.getD i 0)) 0 9 = true := by
  decide +kernel
theorem kg_5230_0 : IPChk.allR (Pts.glueIB K5230.lits KW_5230) 0 9 = true := by decide +kernel
theorem kb_5230_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5230.lits.getD i 0)) 9 20 = true := by
  decide +kernel
theorem kg_5230_9 : IPChk.allR (Pts.glueIB K5230.lits KW_5230) 9 20 = true := by decide +kernel

end B334.E1x.Pts.S707
