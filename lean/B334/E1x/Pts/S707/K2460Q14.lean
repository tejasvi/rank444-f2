import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2460L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2460 of `S707`, parts 1696 … 1697, re-packed by predicted kernel memory (1.31 of 8.19 GB;
stage707_v5; the theorems are v3's `K2460C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2460_1696 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 1696 1 = true := by
  decide +kernel
theorem kg_2460_1696 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 1696 1 = true := by decide +kernel
theorem kb_2460_1697 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 1697 1 = true := by
  decide +kernel
theorem kg_2460_1697 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 1697 1 = true := by decide +kernel

end B334.E1x.Pts.S707
