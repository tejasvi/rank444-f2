import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K91L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 91 of `S707`, parts 0 … 59, re-packed by predicted kernel memory (7.66 of 8.19 GB;
stage707_v5; the theorems are v3's `K91C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_91_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 0 1 = true := by
  decide +kernel
theorem kg_91_0 : IPChk.allR (Pts.glueIB K91.lits KW_91) 0 1 = true := by decide +kernel
theorem kb_91_1 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 1 3 = true := by
  decide +kernel
theorem kg_91_1 : IPChk.allR (Pts.glueIB K91.lits KW_91) 1 3 = true := by decide +kernel
theorem kb_91_4 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 4 8 = true := by
  decide +kernel
theorem kg_91_4 : IPChk.allR (Pts.glueIB K91.lits KW_91) 4 8 = true := by decide +kernel
theorem kb_91_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 12 5 = true := by
  decide +kernel
theorem kg_91_12 : IPChk.allR (Pts.glueIB K91.lits KW_91) 12 5 = true := by decide +kernel
theorem kb_91_17 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 17 6 = true := by
  decide +kernel
theorem kg_91_17 : IPChk.allR (Pts.glueIB K91.lits KW_91) 17 6 = true := by decide +kernel
theorem kb_91_23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 23 2 = true := by
  decide +kernel
theorem kg_91_23 : IPChk.allR (Pts.glueIB K91.lits KW_91) 23 2 = true := by decide +kernel
theorem kb_91_25 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 25 5 = true := by
  decide +kernel
theorem kg_91_25 : IPChk.allR (Pts.glueIB K91.lits KW_91) 25 5 = true := by decide +kernel
theorem kb_91_30 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 30 23 = true := by
  decide +kernel
theorem kg_91_30 : IPChk.allR (Pts.glueIB K91.lits KW_91) 30 23 = true := by decide +kernel
theorem kb_91_53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 53 3 = true := by
  decide +kernel
theorem kg_91_53 : IPChk.allR (Pts.glueIB K91.lits KW_91) 53 3 = true := by decide +kernel
theorem kb_91_56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K91.lits.getD i 0)) 56 4 = true := by
  decide +kernel
theorem kg_91_56 : IPChk.allR (Pts.glueIB K91.lits KW_91) 56 4 = true := by decide +kernel

end B334.E1x.Pts.S707
