import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K395L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 395 of `S707`, parts 91 … 102, re-packed by predicted kernel memory (3.94 of 8.19 GB;
stage707_v5; the theorems are v3's `K395C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_395_91 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 91 3 = true := by
  decide +kernel
theorem kg_395_91 : IPChk.allR (Pts.glueIB K395.lits KW_395) 91 3 = true := by decide +kernel
theorem kb_395_94 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 94 2 = true := by
  decide +kernel
theorem kg_395_94 : IPChk.allR (Pts.glueIB K395.lits KW_395) 94 2 = true := by decide +kernel
theorem kb_395_96 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 96 1 = true := by
  decide +kernel
theorem kg_395_96 : IPChk.allR (Pts.glueIB K395.lits KW_395) 96 1 = true := by decide +kernel
theorem kb_395_97 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 97 1 = true := by
  decide +kernel
theorem kg_395_97 : IPChk.allR (Pts.glueIB K395.lits KW_395) 97 1 = true := by decide +kernel
theorem kb_395_98 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 98 4 = true := by
  decide +kernel
theorem kg_395_98 : IPChk.allR (Pts.glueIB K395.lits KW_395) 98 4 = true := by decide +kernel
theorem kb_395_102 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K395.lits.getD i 0)) 102 1 = true := by
  decide +kernel
theorem kg_395_102 : IPChk.allR (Pts.glueIB K395.lits KW_395) 102 1 = true := by decide +kernel

end B334.E1x.Pts.S707
