import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2460L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2460 of `S707`, parts 40 … 74, re-packed by predicted kernel memory (7.63 of 8.19 GB;
stage707_v5; the theorems are v3's `K2460C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2460_40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 40 2 = true := by
  decide +kernel
theorem kg_2460_40 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 40 2 = true := by decide +kernel
theorem kb_2460_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 42 1 = true := by
  decide +kernel
theorem kg_2460_42 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 42 1 = true := by decide +kernel
theorem kb_2460_43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 43 1 = true := by
  decide +kernel
theorem kg_2460_43 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 43 1 = true := by decide +kernel
theorem kb_2460_44 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 44 9 = true := by
  decide +kernel
theorem kg_2460_44 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 44 9 = true := by decide +kernel
theorem kb_2460_53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 53 4 = true := by
  decide +kernel
theorem kg_2460_53 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 53 4 = true := by decide +kernel
theorem kb_2460_57 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 57 1 = true := by
  decide +kernel
theorem kg_2460_57 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 57 1 = true := by decide +kernel
theorem kb_2460_58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 58 8 = true := by
  decide +kernel
theorem kg_2460_58 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 58 8 = true := by decide +kernel
theorem kb_2460_66 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 66 1 = true := by
  decide +kernel
theorem kg_2460_66 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 66 1 = true := by decide +kernel
theorem kb_2460_67 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2460.lits.getD i 0)) 67 8 = true := by
  decide +kernel
theorem kg_2460_67 : IPChk.allR (Pts.glueIB K2460.lits KW_2460) 67 8 = true := by decide +kernel

end B334.E1x.Pts.S707
