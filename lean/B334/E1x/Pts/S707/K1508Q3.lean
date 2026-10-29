import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1508L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1508 of `S707`, parts 323 … 413, re-packed by predicted kernel memory (2.31 of 8.19 GB;
stage707_v5; the theorems are v3's `K1508C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1508_323 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1508.lits.getD i 0)) 323 20 = true := by
  decide +kernel
theorem kg_1508_323 : IPChk.allR (Pts.glueIB K1508.lits KW_1508) 323 20 = true := by decide +kernel
theorem kb_1508_343 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1508.lits.getD i 0)) 343 35 = true := by
  decide +kernel
theorem kg_1508_343 : IPChk.allR (Pts.glueIB K1508.lits KW_1508) 343 35 = true := by decide +kernel
theorem kb_1508_378 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1508.lits.getD i 0)) 378 36 = true := by
  decide +kernel
theorem kg_1508_378 : IPChk.allR (Pts.glueIB K1508.lits KW_1508) 378 36 = true := by decide +kernel

end B334.E1x.Pts.S707
