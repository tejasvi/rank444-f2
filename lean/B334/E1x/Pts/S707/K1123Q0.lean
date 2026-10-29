import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1123L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1123 of `S707`, parts 0 … 60, re-packed by predicted kernel memory (3.15 of 8.19 GB;
stage707_v5; the theorems are v3's `K1123C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1123_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 0 8 = true := by
  decide +kernel
theorem kg_1123_0 : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 0 8 = true := by decide +kernel
theorem kb_1123_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 8 7 = true := by
  decide +kernel
theorem kg_1123_8 : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 8 7 = true := by decide +kernel
theorem kb_1123_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 15 8 = true := by
  decide +kernel
theorem kg_1123_15 : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 15 8 = true := by decide +kernel
theorem kb_1123_23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1123.lits.getD i 0)) 23 38 = true := by
  decide +kernel
theorem kg_1123_23 : IPChk.allR (Pts.glueIB K1123.lits KW_1123) 23 38 = true := by decide +kernel

end B334.E1x.Pts.S707
