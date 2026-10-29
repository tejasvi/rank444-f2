import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5861L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5861 of `S707`, parts 42 … 66, re-packed by predicted kernel memory (4.59 of 8.19 GB;
stage707_v5; the theorems are v3's `K5861C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5861_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5861.lits.getD i 0)) 42 1 = true := by
  decide +kernel
theorem kg_5861_42 : IPChk.allR (Pts.glueIB K5861.lits KW_5861) 42 1 = true := by decide +kernel
theorem kb_5861_43 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5861.lits.getD i 0)) 43 5 = true := by
  decide +kernel
theorem kg_5861_43 : IPChk.allR (Pts.glueIB K5861.lits KW_5861) 43 5 = true := by decide +kernel
theorem kb_5861_48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5861.lits.getD i 0)) 48 1 = true := by
  decide +kernel
theorem kg_5861_48 : IPChk.allR (Pts.glueIB K5861.lits KW_5861) 48 1 = true := by decide +kernel
theorem kb_5861_49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5861.lits.getD i 0)) 49 7 = true := by
  decide +kernel
theorem kg_5861_49 : IPChk.allR (Pts.glueIB K5861.lits KW_5861) 49 7 = true := by decide +kernel
theorem kb_5861_56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5861.lits.getD i 0)) 56 2 = true := by
  decide +kernel
theorem kg_5861_56 : IPChk.allR (Pts.glueIB K5861.lits KW_5861) 56 2 = true := by decide +kernel
theorem kb_5861_58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5861.lits.getD i 0)) 58 2 = true := by
  decide +kernel
theorem kg_5861_58 : IPChk.allR (Pts.glueIB K5861.lits KW_5861) 58 2 = true := by decide +kernel
theorem kb_5861_60 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5861.lits.getD i 0)) 60 7 = true := by
  decide +kernel
theorem kg_5861_60 : IPChk.allR (Pts.glueIB K5861.lits KW_5861) 60 7 = true := by decide +kernel

end B334.E1x.Pts.S707
