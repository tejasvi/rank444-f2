import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3025L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3025 of `S707`, parts 0 … 44, re-packed by predicted kernel memory (7.55 of 8.19 GB;
stage707_v5; the theorems are v3's `K3025C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3025_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 0 6 = true := by
  decide +kernel
theorem kg_3025_0 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 0 6 = true := by decide +kernel
theorem kb_3025_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 6 3 = true := by
  decide +kernel
theorem kg_3025_6 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 6 3 = true := by decide +kernel
theorem kb_3025_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 9 10 = true := by
  decide +kernel
theorem kg_3025_9 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 9 10 = true := by decide +kernel
theorem kb_3025_19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 19 2 = true := by
  decide +kernel
theorem kg_3025_19 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 19 2 = true := by decide +kernel
theorem kb_3025_21 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 21 1 = true := by
  decide +kernel
theorem kg_3025_21 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 21 1 = true := by decide +kernel
theorem kb_3025_22 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 22 12 = true := by
  decide +kernel
theorem kg_3025_22 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 22 12 = true := by decide +kernel
theorem kb_3025_34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 34 4 = true := by
  decide +kernel
theorem kg_3025_34 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 34 4 = true := by decide +kernel
theorem kb_3025_38 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3025.lits.getD i 0)) 38 7 = true := by
  decide +kernel
theorem kg_3025_38 : IPChk.allR (Pts.glueIB K3025.lits KW_3025) 38 7 = true := by decide +kernel

end B334.E1x.Pts.S707
