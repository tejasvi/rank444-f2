import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K2229L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 2229 of `S707`, parts 0 … 85, re-packed by predicted kernel memory (3.14 of 8.19 GB;
stage707_v5; the theorems are v3's `K2229C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_2229_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2229.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_2229_0 : IPChk.allR (Pts.glueIB K2229.lits KW_2229) 0 2 = true := by decide +kernel
theorem kb_2229_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2229.lits.getD i 0)) 2 6 = true := by
  decide +kernel
theorem kg_2229_2 : IPChk.allR (Pts.glueIB K2229.lits KW_2229) 2 6 = true := by decide +kernel
theorem kb_2229_8 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2229.lits.getD i 0)) 8 26 = true := by
  decide +kernel
theorem kg_2229_8 : IPChk.allR (Pts.glueIB K2229.lits KW_2229) 8 26 = true := by decide +kernel
theorem kb_2229_34 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2229.lits.getD i 0)) 34 31 = true := by
  decide +kernel
theorem kg_2229_34 : IPChk.allR (Pts.glueIB K2229.lits KW_2229) 34 31 = true := by decide +kernel
theorem kb_2229_65 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K2229.lits.getD i 0)) 65 21 = true := by
  decide +kernel
theorem kg_2229_65 : IPChk.allR (Pts.glueIB K2229.lits KW_2229) 65 21 = true := by decide +kernel

end B334.E1x.Pts.S707
