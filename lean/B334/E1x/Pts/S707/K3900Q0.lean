import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3900L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3900 of `S707`, parts 0 … 80, re-packed by predicted kernel memory (2.76 of 8.19 GB;
stage707_v5; the theorems are v3's `K3900C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3900_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3900.lits.getD i 0)) 0 15 = true := by
  decide +kernel
theorem kg_3900_0 : IPChk.allR (Pts.glueIB K3900.lits KW_3900) 0 15 = true := by decide +kernel
theorem kb_3900_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3900.lits.getD i 0)) 15 2 = true := by
  decide +kernel
theorem kg_3900_15 : IPChk.allR (Pts.glueIB K3900.lits KW_3900) 15 2 = true := by decide +kernel
theorem kb_3900_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3900.lits.getD i 0)) 17 28 = true := by
  decide +kernel
theorem kg_3900_17 : IPChk.allR (Pts.glueIB K3900.lits KW_3900) 17 28 = true := by decide +kernel
theorem kb_3900_45 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3900.lits.getD i 0)) 45 36 = true := by
  decide +kernel
theorem kg_3900_45 : IPChk.allR (Pts.glueIB K3900.lits KW_3900) 45 36 = true := by decide +kernel

end B334.E1x.Pts.S707
