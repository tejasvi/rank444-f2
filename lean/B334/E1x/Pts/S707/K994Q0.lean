import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K994L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 994 of `S707`, parts 0 … 208, re-packed by predicted kernel memory (6.37 of 8.19 GB;
stage707_v5; the theorems are v3's `K994C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_994_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_994_0 : IPChk.allR (Pts.glueIB K994.lits KW_994) 0 1 = true := by decide +kernel
theorem kb_994_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 1 1 = true := by
  decide +kernel
theorem kg_994_1 : IPChk.allR (Pts.glueIB K994.lits KW_994) 1 1 = true := by decide +kernel
theorem kb_994_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 2 18 = true := by
  decide +kernel
theorem kg_994_2 : IPChk.allR (Pts.glueIB K994.lits KW_994) 2 18 = true := by decide +kernel
theorem kb_994_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 20 46 = true := by
  decide +kernel
theorem kg_994_20 : IPChk.allR (Pts.glueIB K994.lits KW_994) 20 46 = true := by decide +kernel
theorem kb_994_66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 66 103 = true := by
  decide +kernel
theorem kg_994_66 : IPChk.allR (Pts.glueIB K994.lits KW_994) 66 103 = true := by decide +kernel
theorem kb_994_169 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 169 3 = true := by
  decide +kernel
theorem kg_994_169 : IPChk.allR (Pts.glueIB K994.lits KW_994) 169 3 = true := by decide +kernel
theorem kb_994_172 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 172 16 = true := by
  decide +kernel
theorem kg_994_172 : IPChk.allR (Pts.glueIB K994.lits KW_994) 172 16 = true := by decide +kernel
theorem kb_994_188 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K994.lits.getD i 0)) 188 21 = true := by
  decide +kernel
theorem kg_994_188 : IPChk.allR (Pts.glueIB K994.lits KW_994) 188 21 = true := by decide +kernel

end B334.E1x.Pts.S707
