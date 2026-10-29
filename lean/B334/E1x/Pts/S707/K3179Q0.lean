import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K3179L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 3179 of `S707`, parts 0 … 20, re-packed by predicted kernel memory (4.50 of 8.19 GB;
stage707_v5; the theorems are v3's `K3179C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_3179_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3179.lits.getD i 0)) 0 12 = true := by
  decide +kernel
theorem kg_3179_0 : IPChk.allR (Pts.glueIB K3179.lits KW_3179) 0 12 = true := by decide +kernel
theorem kb_3179_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3179.lits.getD i 0)) 12 1 = true := by
  decide +kernel
theorem kg_3179_12 : IPChk.allR (Pts.glueIB K3179.lits KW_3179) 12 1 = true := by decide +kernel
theorem kb_3179_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3179.lits.getD i 0)) 13 2 = true := by
  decide +kernel
theorem kg_3179_13 : IPChk.allR (Pts.glueIB K3179.lits KW_3179) 13 2 = true := by decide +kernel
theorem kb_3179_15 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3179.lits.getD i 0)) 15 2 = true := by
  decide +kernel
theorem kg_3179_15 : IPChk.allR (Pts.glueIB K3179.lits KW_3179) 15 2 = true := by decide +kernel
theorem kb_3179_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3179.lits.getD i 0)) 17 2 = true := by
  decide +kernel
theorem kg_3179_17 : IPChk.allR (Pts.glueIB K3179.lits KW_3179) 17 2 = true := by decide +kernel
theorem kb_3179_19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K3179.lits.getD i 0)) 19 2 = true := by
  decide +kernel
theorem kg_3179_19 : IPChk.allR (Pts.glueIB K3179.lits KW_3179) 19 2 = true := by decide +kernel

end B334.E1x.Pts.S707
