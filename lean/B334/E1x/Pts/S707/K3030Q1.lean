import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3030L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3030 of `S707`, parts 107 … 275, re-packed by predicted kernel memory (5.31 of 8.19 GB;
stage707_v5; the theorems are v3's `K3030C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3030_107 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 107 26 = true := by
  decide +kernel
theorem kg_3030_107 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 107 26 = true := by decide +kernel
theorem kb_3030_133 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 133 48 = true := by
  decide +kernel
theorem kg_3030_133 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 133 48 = true := by decide +kernel
theorem kb_3030_181 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 181 17 = true := by
  decide +kernel
theorem kg_3030_181 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 181 17 = true := by decide +kernel
theorem kb_3030_198 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 198 31 = true := by
  decide +kernel
theorem kg_3030_198 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 198 31 = true := by decide +kernel
theorem kb_3030_229 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 229 2 = true := by
  decide +kernel
theorem kg_3030_229 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 229 2 = true := by decide +kernel
theorem kb_3030_231 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 231 5 = true := by
  decide +kernel
theorem kg_3030_231 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 231 5 = true := by decide +kernel
theorem kb_3030_236 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3030.lits.getD i 0)) 236 40 = true := by
  decide +kernel
theorem kg_3030_236 : IPChk.allR (Pts.glueIB K3030.lits KW_3030) 236 40 = true := by decide +kernel

end B334.E1x.Pts.S707
