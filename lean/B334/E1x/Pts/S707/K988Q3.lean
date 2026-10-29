import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K988L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 988 of `S707`, parts 477 … 485, re-packed by predicted kernel memory (0.72 of 8.19 GB;
stage707_v5; the theorems are v3's `K988C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_988_477 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K988.lits.getD i 0)) 477 9 = true := by
  decide +kernel
theorem kg_988_477 : IPChk.allR (Pts.glueIB K988.lits KW_988) 477 9 = true := by decide +kernel

end B334.E1x.Pts.S707
