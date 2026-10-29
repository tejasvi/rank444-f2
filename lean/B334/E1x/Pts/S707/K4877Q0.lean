import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4877L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4877 of `S707`, parts 0 … 17, re-packed by predicted kernel memory (1.03 of 8.19 GB;
stage707_v5; the theorems are v3's `K4877C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4877_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4877.lits.getD i 0)) 0 15 = true := by
  decide +kernel
theorem kg_4877_0 : IPChk.allR (Pts.glueIB K4877.lits KW_4877) 0 15 = true := by decide +kernel
theorem kb_4877_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4877.lits.getD i 0)) 15 3 = true := by
  decide +kernel
theorem kg_4877_15 : IPChk.allR (Pts.glueIB K4877.lits KW_4877) 15 3 = true := by decide +kernel

end B334.E1x.Pts.S707
