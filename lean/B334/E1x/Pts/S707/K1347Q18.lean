import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1347L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1347 of `S707`, parts 2048 … 2059, re-packed by predicted kernel memory (1.36 of 8.19 GB;
stage707_v5; the theorems are v3's `K1347C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1347_2048 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 2048 7 = true := by
  decide +kernel
theorem kg_1347_2048 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 2048 7 = true := by decide +kernel
theorem kb_1347_2055 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1347.lits.getD i 0)) 2055 5 = true := by
  decide +kernel
theorem kg_1347_2055 : IPChk.allR (Pts.glueIB K1347.lits KW_1347) 2055 5 = true := by decide +kernel

end B334.E1x.Pts.S707
