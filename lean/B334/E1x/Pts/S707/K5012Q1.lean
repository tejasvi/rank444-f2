import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K5012L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 5012 of `S707`, parts 40 … 58, re-packed by predicted kernel memory (6.69 of 8.19 GB;
stage707_v5; the theorems are v3's `K5012C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_5012_40 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 40 2 = true := by
  decide +kernel
theorem kg_5012_40 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 40 2 = true := by decide +kernel
theorem kb_5012_42 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 42 6 = true := by
  decide +kernel
theorem kg_5012_42 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 42 6 = true := by decide +kernel
theorem kb_5012_48 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 48 1 = true := by
  decide +kernel
theorem kg_5012_48 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 48 1 = true := by decide +kernel
theorem kb_5012_49 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 49 3 = true := by
  decide +kernel
theorem kg_5012_49 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 49 3 = true := by decide +kernel
theorem kb_5012_52 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 52 1 = true := by
  decide +kernel
theorem kg_5012_52 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 52 1 = true := by decide +kernel
theorem kb_5012_53 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 53 1 = true := by
  decide +kernel
theorem kg_5012_53 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 53 1 = true := by decide +kernel
theorem kb_5012_54 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 54 2 = true := by
  decide +kernel
theorem kg_5012_54 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 54 2 = true := by decide +kernel
theorem kb_5012_56 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 56 2 = true := by
  decide +kernel
theorem kg_5012_56 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 56 2 = true := by decide +kernel
theorem kb_5012_58 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K5012.lits.getD i 0)) 58 1 = true := by
  decide +kernel
theorem kg_5012_58 : IPChk.allR (Pts.glueIB K5012.lits KW_5012) 58 1 = true := by decide +kernel

end B334.E1x.Pts.S707
