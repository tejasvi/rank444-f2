import B334.E1x.Pts.S707.Ctx
import B334.E1x.Pts.S707.K817L
import B334.E1x.Pts.ChkB

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! # Job 817 of `S707`, parts 0 … 27, re-packed by predicted kernel memory (5.37 of 8.19 GB;
stage707_v5; the theorems are v3's `K817C*` theorems verbatim; core Lean) -/

namespace B334.E1x.Pts.S707

theorem kb_817_0 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K817.lits.getD i 0)) 0 6 = true := by
  decide +kernel
theorem kg_817_0 : IPChk.allR (Pts.glueIB K817.lits KW_817) 0 6 = true := by decide +kernel
theorem kb_817_6 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K817.lits.getD i 0)) 6 7 = true := by
  decide +kernel
theorem kg_817_6 : IPChk.allR (Pts.glueIB K817.lits KW_817) 6 7 = true := by decide +kernel
theorem kb_817_13 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K817.lits.getD i 0)) 13 5 = true := by
  decide +kernel
theorem kg_817_13 : IPChk.allR (Pts.glueIB K817.lits KW_817) 13 5 = true := by decide +kernel
theorem kb_817_18 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K817.lits.getD i 0)) 18 1 = true := by
  decide +kernel
theorem kg_817_18 : IPChk.allR (Pts.glueIB K817.lits KW_817) 18 1 = true := by decide +kernel
theorem kb_817_19 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K817.lits.getD i 0)) 19 4 = true := by
  decide +kernel
theorem kg_817_19 : IPChk.allR (Pts.glueIB K817.lits KW_817) 19 4 = true := by decide +kernel
theorem kb_817_23 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K817.lits.getD i 0)) 23 3 = true := by
  decide +kernel
theorem kg_817_23 : IPChk.allR (Pts.glueIB K817.lits KW_817) 23 3 = true := by decide +kernel
theorem kb_817_26 : IPChk.allR (fun i => E1P.block CL Pts.H707.sl Pts.H707.UB Pts.H707.UBR (K817.lits.getD i 0)) 26 2 = true := by
  decide +kernel
theorem kg_817_26 : IPChk.allR (Pts.glueIB K817.lits KW_817) 26 2 = true := by decide +kernel

end B334.E1x.Pts.S707
