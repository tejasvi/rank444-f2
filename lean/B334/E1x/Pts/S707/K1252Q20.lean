import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1252L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1252 of `S707`, parts 1388 … 1418, re-packed by predicted kernel memory (2.48 of 8.19 GB;
stage707_v5; the theorems are v3's `K1252C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1252_1388 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 1388 18 = true := by
  decide +kernel
theorem kg_1252_1388 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 1388 18 = true := by decide +kernel
theorem kb_1252_1406 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 1406 5 = true := by
  decide +kernel
theorem kg_1252_1406 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 1406 5 = true := by decide +kernel
theorem kb_1252_1411 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1252.lits.getD i 0)) 1411 8 = true := by
  decide +kernel
theorem kg_1252_1411 : IPChk.allR (Pts.glueIB K1252.lits KW_1252) 1411 8 = true := by decide +kernel

end B334.E1x.Pts.S707
