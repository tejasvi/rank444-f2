import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1044L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1044 of `S707`, parts 0 … 158, re-packed by predicted kernel memory (3.41 of 8.19 GB;
stage707_v5; the theorems are v3's `K1044C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1044_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_1044_0 : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 0 1 = true := by decide +kernel
theorem kb_1044_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 1 12 = true := by
  decide +kernel
theorem kg_1044_1 : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 1 12 = true := by decide +kernel
theorem kb_1044_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 13 103 = true := by
  decide +kernel
theorem kg_1044_13 : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 13 103 = true := by decide +kernel
theorem kb_1044_116 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1044.lits.getD i 0)) 116 43 = true := by
  decide +kernel
theorem kg_1044_116 : IPChk.allR (Pts.glueIB K1044.lits KW_1044) 116 43 = true := by decide +kernel

end B334.E1x.Pts.S707
