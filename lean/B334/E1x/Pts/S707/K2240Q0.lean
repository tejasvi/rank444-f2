import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2240L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2240 of `S707`, parts 0 … 57, re-packed by predicted kernel memory (4.23 of 8.19 GB;
stage707_v5; the theorems are v3's `K2240C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2240_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2240.lits.getD i 0)) 0 7 = true := by
  decide +kernel
theorem kg_2240_0 : IPChk.allR (Pts.glueIB K2240.lits KW_2240) 0 7 = true := by decide +kernel
theorem kb_2240_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2240.lits.getD i 0)) 7 13 = true := by
  decide +kernel
theorem kg_2240_7 : IPChk.allR (Pts.glueIB K2240.lits KW_2240) 7 13 = true := by decide +kernel
theorem kb_2240_20 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2240.lits.getD i 0)) 20 11 = true := by
  decide +kernel
theorem kg_2240_20 : IPChk.allR (Pts.glueIB K2240.lits KW_2240) 20 11 = true := by decide +kernel
theorem kb_2240_31 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2240.lits.getD i 0)) 31 5 = true := by
  decide +kernel
theorem kg_2240_31 : IPChk.allR (Pts.glueIB K2240.lits KW_2240) 31 5 = true := by decide +kernel
theorem kb_2240_36 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2240.lits.getD i 0)) 36 22 = true := by
  decide +kernel
theorem kg_2240_36 : IPChk.allR (Pts.glueIB K2240.lits KW_2240) 36 22 = true := by decide +kernel

end B334.E1x.Pts.S707
