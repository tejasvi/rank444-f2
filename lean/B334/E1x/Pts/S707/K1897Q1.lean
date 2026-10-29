import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K1897L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 1897 of `S707`, parts 186 … 278, re-packed by predicted kernel memory (3.22 of 8.19 GB;
stage707_v5; the theorems are v3's `K1897C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_1897_186 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 186 20 = true := by
  decide +kernel
theorem kg_1897_186 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 186 20 = true := by decide +kernel
theorem kb_1897_206 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 206 20 = true := by
  decide +kernel
theorem kg_1897_206 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 206 20 = true := by decide +kernel
theorem kb_1897_226 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 226 17 = true := by
  decide +kernel
theorem kg_1897_226 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 226 17 = true := by decide +kernel
theorem kb_1897_243 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 243 5 = true := by
  decide +kernel
theorem kg_1897_243 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 243 5 = true := by decide +kernel
theorem kb_1897_248 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K1897.lits.getD i 0)) 248 31 = true := by
  decide +kernel
theorem kg_1897_248 : IPChk.allR (Pts.glueIB K1897.lits KW_1897) 248 31 = true := by decide +kernel

end B334.E1x.Pts.S707
