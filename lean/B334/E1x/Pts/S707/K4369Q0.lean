import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4369L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4369 of `S707`, parts 0 … 26, re-packed by predicted kernel memory (1.37 of 8.19 GB;
stage707_v5; the theorems are v3's `K4369C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4369_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4369.lits.getD i 0)) 0 5 = true := by
  decide +kernel
theorem kg_4369_0 : IPChk.allR (Pts.glueIB K4369.lits KW_4369) 0 5 = true := by decide +kernel
theorem kb_4369_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4369.lits.getD i 0)) 5 22 = true := by
  decide +kernel
theorem kg_4369_5 : IPChk.allR (Pts.glueIB K4369.lits KW_4369) 5 22 = true := by decide +kernel

end B334.E1x.Pts.S707
