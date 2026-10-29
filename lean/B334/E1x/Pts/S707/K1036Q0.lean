import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1036L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1036 of `S707`, parts 0 … 54, re-packed by predicted kernel memory (3.37 of 8.19 GB;
stage707_v5; the theorems are v3's `K1036C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1036_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 0 11 = true := by
  decide +kernel
theorem kg_1036_0 : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 0 11 = true := by decide +kernel
theorem kb_1036_11 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 11 1 = true := by
  decide +kernel
theorem kg_1036_11 : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 11 1 = true := by decide +kernel
theorem kb_1036_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 12 21 = true := by
  decide +kernel
theorem kg_1036_12 : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 12 21 = true := by decide +kernel
theorem kb_1036_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1036.lits.getD i 0)) 33 22 = true := by
  decide +kernel
theorem kg_1036_33 : IPChk.allR (Pts.glueIB K1036.lits KW_1036) 33 22 = true := by decide +kernel

end B334.E1x.Pts.S707
