import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3353L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3353 of `S707`, parts 0 … 60, re-packed by predicted kernel memory (5.28 of 8.19 GB;
stage707_v5; the theorems are v3's `K3353C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3353_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3353.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_3353_0 : IPChk.allR (Pts.glueIB K3353.lits KW_3353) 0 2 = true := by decide +kernel
theorem kb_3353_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3353.lits.getD i 0)) 2 8 = true := by
  decide +kernel
theorem kg_3353_2 : IPChk.allR (Pts.glueIB K3353.lits KW_3353) 2 8 = true := by decide +kernel
theorem kb_3353_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3353.lits.getD i 0)) 10 19 = true := by
  decide +kernel
theorem kg_3353_10 : IPChk.allR (Pts.glueIB K3353.lits KW_3353) 10 19 = true := by decide +kernel
theorem kb_3353_29 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3353.lits.getD i 0)) 29 4 = true := by
  decide +kernel
theorem kg_3353_29 : IPChk.allR (Pts.glueIB K3353.lits KW_3353) 29 4 = true := by decide +kernel
theorem kb_3353_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3353.lits.getD i 0)) 33 22 = true := by
  decide +kernel
theorem kg_3353_33 : IPChk.allR (Pts.glueIB K3353.lits KW_3353) 33 22 = true := by decide +kernel
theorem kb_3353_55 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3353.lits.getD i 0)) 55 6 = true := by
  decide +kernel
theorem kg_3353_55 : IPChk.allR (Pts.glueIB K3353.lits KW_3353) 55 6 = true := by decide +kernel

end B334.E1x.Pts.S707
