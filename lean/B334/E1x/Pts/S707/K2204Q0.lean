import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2204L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2204 of `S707`, parts 0 … 63, re-packed by predicted kernel memory (4.18 of 8.19 GB;
stage707_v5; the theorems are v3's `K2204C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2204_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2204.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2204_0 : IPChk.allR (Pts.glueIB K2204.lits KW_2204) 0 2 = true := by decide +kernel
theorem kb_2204_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2204.lits.getD i 0)) 2 8 = true := by
  decide +kernel
theorem kg_2204_2 : IPChk.allR (Pts.glueIB K2204.lits KW_2204) 2 8 = true := by decide +kernel
theorem kb_2204_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2204.lits.getD i 0)) 10 20 = true := by
  decide +kernel
theorem kg_2204_10 : IPChk.allR (Pts.glueIB K2204.lits KW_2204) 10 20 = true := by decide +kernel
theorem kb_2204_30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2204.lits.getD i 0)) 30 3 = true := by
  decide +kernel
theorem kg_2204_30 : IPChk.allR (Pts.glueIB K2204.lits KW_2204) 30 3 = true := by decide +kernel
theorem kb_2204_33 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2204.lits.getD i 0)) 33 24 = true := by
  decide +kernel
theorem kg_2204_33 : IPChk.allR (Pts.glueIB K2204.lits KW_2204) 33 24 = true := by decide +kernel
theorem kb_2204_57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2204.lits.getD i 0)) 57 7 = true := by
  decide +kernel
theorem kg_2204_57 : IPChk.allR (Pts.glueIB K2204.lits KW_2204) 57 7 = true := by decide +kernel

end B334.E1x.Pts.S707
