import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1406L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1406 of `S707`, parts 1560 … 1602, re-packed by predicted kernel memory (1.21 of 8.19 GB;
stage707_v5; the theorems are v3's `K1406C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1406_1560 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 1560 23 = true := by
  decide +kernel
theorem kg_1406_1560 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 1560 23 = true := by decide +kernel
theorem kb_1406_1583 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1406.lits.getD i 0)) 1583 20 = true := by
  decide +kernel
theorem kg_1406_1583 : IPChk.allR (Pts.glueIB K1406.lits KW_1406) 1583 20 = true := by decide +kernel

end B334.E1x.Pts.S707
