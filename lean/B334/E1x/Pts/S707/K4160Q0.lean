import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K4160L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 4160 of `S707`, parts 0 … 15, re-packed by predicted kernel memory (7.63 of 8.19 GB;
stage707_v5; the theorems are v3's `K4160C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_4160_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 0 2 = true := by
  decide +kernel
theorem kg_4160_0 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 0 2 = true := by decide +kernel
theorem kb_4160_2 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 2 3 = true := by
  decide +kernel
theorem kg_4160_2 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 2 3 = true := by decide +kernel
theorem kb_4160_5 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 5 2 = true := by
  decide +kernel
theorem kg_4160_5 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 5 2 = true := by decide +kernel
theorem kb_4160_7 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 7 2 = true := by
  decide +kernel
theorem kg_4160_7 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 7 2 = true := by decide +kernel
theorem kb_4160_9 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 9 1 = true := by
  decide +kernel
theorem kg_4160_9 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 9 1 = true := by decide +kernel
theorem kb_4160_10 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 10 2 = true := by
  decide +kernel
theorem kg_4160_10 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 10 2 = true := by decide +kernel
theorem kb_4160_12 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 12 1 = true := by
  decide +kernel
theorem kg_4160_12 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 12 1 = true := by decide +kernel
theorem kb_4160_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 13 1 = true := by
  decide +kernel
theorem kg_4160_13 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 13 1 = true := by decide +kernel
theorem kb_4160_14 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K4160.lits.getD i 0)) 14 2 = true := by
  decide +kernel
theorem kg_4160_14 : IPChk.allR (Pts.glueIB K4160.lits KW_4160) 14 2 = true := by decide +kernel

end B334.E1x.Pts.S707
