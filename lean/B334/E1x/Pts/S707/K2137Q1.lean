import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2137L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2137 of `S707`, parts 149 … 284, re-packed by predicted kernel memory (1.38 of 8.19 GB;
stage707_v5; the theorems are v3's `K2137C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2137_149 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2137.lits.getD i 0)) 149 91 = true := by
  decide +kernel
theorem kg_2137_149 : IPChk.allR (Pts.glueIB K2137.lits KW_2137) 149 91 = true := by decide +kernel
theorem kb_2137_240 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2137.lits.getD i 0)) 240 45 = true := by
  decide +kernel
theorem kg_2137_240 : IPChk.allR (Pts.glueIB K2137.lits KW_2137) 240 45 = true := by decide +kernel

end B334.E1x.Pts.S707
