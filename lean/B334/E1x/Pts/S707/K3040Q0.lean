import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3040L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3040 of `S707`, parts 0 … 72, re-packed by predicted kernel memory (4.78 of 8.19 GB;
stage707_v5; the theorems are v3's `K3040C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3040_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_3040_0 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 0 2 = true := by decide +kernel
theorem kb_3040_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_3040_2 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 2 6 = true := by decide +kernel
theorem kb_3040_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 8 22 = true := by
  decide +kernel
theorem kg_3040_8 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 8 22 = true := by decide +kernel
theorem kb_3040_30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 30 4 = true := by
  decide +kernel
theorem kg_3040_30 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 30 4 = true := by decide +kernel
theorem kb_3040_34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 34 22 = true := by
  decide +kernel
theorem kg_3040_34 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 34 22 = true := by decide +kernel
theorem kb_3040_56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3040.lits.getD i 0)) 56 17 = true := by
  decide +kernel
theorem kg_3040_56 : IPChk.allR (Pts.glueIB K3040.lits KW_3040) 56 17 = true := by decide +kernel

end B334.E1x.Pts.S707
