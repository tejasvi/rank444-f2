import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1221L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1221 of `S707`, parts 337 … 417, re-packed by predicted kernel memory (2.78 of 8.19 GB;
stage707_v5; the theorems are v3's `K1221C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1221_337 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 337 12 = true := by
  decide +kernel
theorem kg_1221_337 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 337 12 = true := by decide +kernel
theorem kb_1221_349 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 349 3 = true := by
  decide +kernel
theorem kg_1221_349 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 349 3 = true := by decide +kernel
theorem kb_1221_352 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 352 31 = true := by
  decide +kernel
theorem kg_1221_352 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 352 31 = true := by decide +kernel
theorem kb_1221_383 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1221.lits.getD i 0)) 383 35 = true := by
  decide +kernel
theorem kg_1221_383 : IPChk.allR (Pts.glueIB K1221.lits KW_1221) 383 35 = true := by decide +kernel

end B334.E1x.Pts.S707
